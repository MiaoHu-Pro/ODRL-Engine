import json
import rdflib
from rdflib import Graph, Namespace, BNode, URIRef, RDF, Literal
from rdflib.collection import Collection
from rdflib.namespace import NamespaceManager
import uuid
from collections import defaultdict
import json
from pathlib import Path
import validate

ODRL = Namespace("http://www.w3.org/ns/odrl/2/")
DPV = Namespace("https://w3id.org/dpv/dpv-owl#")
EX = Namespace("http://example.org/resource/")

def normalize_odrl_graph(g):
    properties_to_wrap = [ODRL.action, ODRL.assignee, ODRL.assigner, ODRL.target]

    triples_to_add = []
    triples_to_remove = []

    # Step 1: Wrap direct IRIs into blank nodes with odrl:source
    for s, p, o in g:
        if p in properties_to_wrap and isinstance(o, URIRef):
            # Create new blank node
            bn = BNode()
            triples_to_add.append((s, p, bn))
            triples_to_add.append((bn, ODRL.source, o))
            triples_to_remove.append((s, p, o))

    for triple in triples_to_remove:
        g.remove(triple)
    for triple in triples_to_add:
        g.add(triple)

    # Step 2: Replace all blank nodes with fresh IRIs
    bnode_to_iri = {}

    for s, p, o in list(g):
        new_s = bnode_to_iri.get(s, None)
        new_o = bnode_to_iri.get(o, None)

        # Subject replacement
        if isinstance(s, BNode):
            if s not in bnode_to_iri:
                bnode_to_iri[s] = EX[str(uuid.uuid4())]
            new_s = bnode_to_iri[s]

        # Object replacement
        if isinstance(o, BNode):
            if o not in bnode_to_iri:
                bnode_to_iri[o] = EX[str(uuid.uuid4())]
            new_o = bnode_to_iri[o]

        # Only modify if replacements happened
        if new_s or new_o:
            g.remove((s, p, o))
            g.add((new_s if new_s else s, p, new_o if new_o else o))

    return g

def custom_convert_odrl_policy(jsonld_str):
    g = Graph()
    g.parse(data=jsonld_str, format='json-ld')
    g = normalize_odrl_graph(g)
    # normalise_here

    #print(g.serialize(format='turtle'))

    results = []

    # Get all rules: Permissions, Prohibitions, Obligations
    rule_types = {
        str(ODRL.Permission): "Permission",
        str(ODRL.Prohibition): "Prohibition",
        str(ODRL.Obligation): "Obligation"
    }

    # Query all rules (permissions, prohibitions, obligations)
    rule_query = """
      SELECT ?rule ?ruleType WHERE {
        ?policy ?predicate ?rule .
        VALUES (?predicate ?ruleType) {
          (odrl:permission odrl:Permission)
          (odrl:prohibition odrl:Prohibition)
          (odrl:obligation odrl:Obligation)
        }
      }
    """
    ns_manager = NamespaceManager(g)
    ns_manager.bind('odrl', ODRL)
    g.namespace_manager = ns_manager

    for row in g.query(rule_query, initNs={'odrl': ODRL}):
        rule_uri = row['rule']
        rule_type = str(row['ruleType'])
        processed_rule = process_rule(g, rule_uri, rule_type)
        results.append(processed_rule)

    return results




def process_rule(g, rule_uri, rule_type):
    # Helper to run SPARQL query and get first result
    def get_single_value(query, bindings={}):
        qres = g.query(query, initBindings=bindings, initNs={'odrl': ODRL, 'dpv': DPV, 'rdf': RDF})
        for row in qres:
            return str(row[0])
        return ""

    # Get actor (assignee)
    actor_query = """
    SELECT ?actor WHERE {
      <%s> odrl:assignee ?actorNode .
      ?actorNode odrl:source ?actor .
    }
    """ % rule_uri
    actor = get_single_value(actor_query)

    # Get action
    action_query = """
    SELECT ?action WHERE {
      <%s> odrl:action ?actionNode .
      ?actionNode odrl:source | rdf:value ?action .
    }
    """ % rule_uri
    action = get_single_value(action_query)

    # Get target
    target_query = """
    SELECT ?target WHERE {
      <%s> odrl:target ?targetNode .
      ?targetNode odrl:source ?target .
    }
    """ % rule_uri
    target = get_single_value(target_query)

    # Helper to group refinements or constraints by (leftOperand, operator)
    def group_constraints_or_refinements(query):
        result = defaultdict(lambda: {"type": None, "operator": None, "value": []})
        qres = g.query(query, initNs={'odrl': ODRL, 'dpv': DPV, 'rdf': RDF})

        for row in qres:
            left = str(row.left)
            op = str(row.op)
            right = row.right.toPython() if hasattr(row.right, 'toPython') else str(getattr(row.right, 'toPython', lambda: row.right)())
            key = (left, op)
            result[key]["type"] = left
            result[key]["operator"] = op
            result[key]["value"].append(str(getattr(row.right, 'toPython', lambda: row.right)()))

        return list(result.values())

    # Get constraints (grouped)
    constraints_query = """
    SELECT ?left ?op ?right WHERE {
      <%s> odrl:constraint ?c .
      ?c odrl:leftOperand ?left ;
         odrl:operator ?op ;
         odrl:rightOperand ?right .
    }
    """ % rule_uri
    constraints = group_constraints_or_refinements(constraints_query)

    # Get actor refinements (grouped)
    actor_ref_query = """
    SELECT ?left ?op ?right WHERE {
      <%s> odrl:assignee ?actorNode .
      ?actorNode odrl:refinement ?ref .
      ?ref odrl:leftOperand ?left ;
           odrl:operator ?op ;
           odrl:rightOperand ?right .
    }
    """ % rule_uri
    actor_refinements = group_constraints_or_refinements(actor_ref_query)

    # Get action refinements (grouped)
    action_ref_query = """
    SELECT ?left ?op ?right WHERE {
      <%s> odrl:action ?actionNode .
      ?actionNode odrl:refinement ?ref .
      ?ref odrl:leftOperand ?left ;
           odrl:operator ?op ;
           odrl:rightOperand ?right .
    }
    """ % rule_uri
    action_refinements = group_constraints_or_refinements(action_ref_query)

    # Get target refinements (grouped) — new
    target_ref_query = """
    SELECT ?left ?op ?right WHERE {
      <%s> odrl:target ?targetNode .
      ?targetNode odrl:refinement ?ref .
      ?ref odrl:leftOperand ?left ;
           odrl:operator ?op ;
           odrl:rightOperand ?right .
    }
    """ % rule_uri
    target_refinements = group_constraints_or_refinements(target_ref_query)

    return {
        "rule": str(rule_type),
        "actor": actor,
        "action": action,
        "target": target,
        "purpose": "",  # Placeholder
        "query": "",    # Placeholder
        "constraints": constraints,
        "actorrefinements": actor_refinements,
        "actionrefinements": action_refinements,
        "targetrefinements": target_refinements,
        "purposerefinements": []
    }


def has_none_value_on_first_level(d):
    """ Check if dictionary d has at least one None value on the first level """
    return any((value is None) or (value == '' and key == "value") for key, value in d.items())



def filter_dicts_with_none_values(data):
    """
    Recursively filter out dictionaries from data that have at least one None value on the first level.
    Handles nested lists and dictionaries.
    """
    if isinstance(data, list):
        filtered_list = []
        for item in data:
            if isinstance(item, dict):
                if not has_none_value_on_first_level(item):
                    filtered_list.append(filter_dicts_with_none_values(item))
            elif isinstance(item, list):
                filtered_list.append(filter_dicts_with_none_values(item))
            else:
                filtered_list.append(item)
        return filtered_list
    elif isinstance(data, dict):
        filtered_dict = {}
        for key, value in data.items():
            if isinstance(value, dict):
                if not has_none_value_on_first_level(value):
                    filtered_dict[key] = filter_dicts_with_none_values(value)
            elif isinstance(value, list):
                filtered_dict[key] = filter_dicts_with_none_values(value)
            else:
                filtered_dict[key] = value
        return filtered_dict
    else:
        return data


def convert_list_to_odrl_jsonld_no_user(data_list):
    # data_list = recursive_replace (data_list,"https://w3id.org/dpv/dpv-owl#","https://w3id.org/dpv#")
    # data_list = recursive_replace (data_list,"http://www.w3.org/ns/odrl/2/","")

    odrl_permissions = []
    odrl_prohibitions = []
    odrl_obligations = []
    odrl_duties = []
    odrl_rules = []

    policy = {
        "permission": odrl_permissions,
        "prohibition": odrl_prohibitions,
        "obligation": odrl_obligations,
        "duty": odrl_duties,
        "rule": odrl_rules,
        "uid": "http://example.org/policy-" + str(uuid.uuid4()),
        "@context": [
            "http://www.w3.org/ns/odrl.jsonld",
            {
                "dcat": "http://www.w3.org/ns/dcat#",
                "dpv": "https://w3id.org/dpv/dpv-owl#",
                "ex":  "http://example.org/ns#"
            }
        ],
        "@type": "Policy",
    }

    for data in data_list:
        # Basic presence check
        if data.get("action") is None or data.get("actor") is None or data.get("target") is None:
            continue

        # Determine rule type
        if "rule" in data and data["rule"]:
            ruleType = str(data["rule"].split("/")[-1]).lower()
        else:
            ruleType = "rule"

        # Build actor/assignee
        actor_refinements = data.get("actorrefinements", []) or []
        if len(actor_refinements) > 0:
            actor = {"@type": "PartyCollection", "source": data["actor"], "refinement": []}
        else:
            actor = data["actor"]

        # Build action
        action_refinements = data.get("actionrefinements", []) or []
        if len(action_refinements) > 0:
            action = {"source": data["action"], "refinement": []}
        else:
            action = data["action"]

        # Build target
        target_refinements = data.get("targetrefinements", []) or []
        if len(target_refinements) > 0:
            target = {"@type": "AssetCollection", "source": data["target"], "refinement": []}
        else:
            target = data["target"]

        # Start rule object
        odrl_jsonld = {
            "action": action,
            "assignee": actor,
            "target": target,
            "constraint": [],
        }

        # PURPOSE AS TOP-LEVEL FIELD (not a constraint)
        purpose = data.get("purpose")
        purpose_refinements = data.get("purposerefinements", []) or []
        if purpose is not None:
            if len(purpose_refinements) > 0:
                purpose_obj = {"source": purpose, "refinement": []}
                for pr in purpose_refinements:
                    if pr.get("operator") is not None:
                        purpose_obj["refinement"].append({
                            "leftOperand": pr.get("type", "").split("#")[-1],
                            "operator": pr["operator"],
                            "rightOperand": pr.get("value"),
                        })
                odrl_jsonld["purpose"] = purpose_obj
            else:
                odrl_jsonld["purpose"] = purpose

        # Optional query constraint
        if "query" in data:
            if data["query"] != '':
                odrl_jsonld["constraint"].append({
                    "leftOperand": "ex:query",
                    "operator": "http://www.w3.org/ns/odrl/2/eq",
                    "rightOperand": data["query"],
                })

        # Generic constraints (non-purpose)
        for constraint in data.get("constraints", []) or []:
            if constraint.get("operator") is not None:
                odrl_jsonld["constraint"].append({
                    "leftOperand": constraint.get("type", "").split("#")[-1],
                    "operator": constraint["operator"],
                    "rightOperand": constraint.get("value"),
                })

        # Actor refinements
        for constraint in actor_refinements:
            if isinstance(actor, dict) and "refinement" in actor and constraint.get("operator") is not None:
                actor["refinement"].append({
                    "leftOperand": constraint.get("type", "").split("#")[-1],
                    "operator": constraint["operator"],
                    "rightOperand": constraint.get("value"),
                })

        # Action refinements
        for constraint in action_refinements:
            if isinstance(action, dict) and "refinement" in action and constraint.get("operator") is not None:
                action["refinement"].append({
                    "leftOperand": constraint.get("type", "").split("#")[-1],
                    "operator": constraint["operator"],
                    "rightOperand": constraint.get("value"),
                })

        # Target refinements
        for constraint in target_refinements:
            if isinstance(target, dict) and "refinement" in target and constraint.get("operator") is not None:
                target["refinement"].append({
                    "leftOperand": constraint.get("type", "").split("#")[-1],
                    "operator": constraint["operator"],
                    "rightOperand": constraint.get("value"),
                })

        # Append to the proper rule collection
        policy[ruleType].append(odrl_jsonld)

    # Remove empty collections
    if len(policy["permission"]) == 0:
        del policy["permission"]
    if len(policy["prohibition"]) == 0:
        del policy["prohibition"]
    if len(policy["obligation"]) == 0:
        del policy["obligation"]
    if len(policy["duty"]) == 0:
        del policy["duty"]
    if len(policy["rule"]) == 0:
        del policy["rule"]

    return policy


if __name__ == "__main__":

    """
        cactus policy format --> validation check --> custom format --> convert to odrl_jsonld
        for example in example_policies:
        
            Cactus policy format: policy_6_BIOSKIN_2025-09-22_13-17-07.json
            custom format: policy_6_BIOSKIN_2025-09-22_13-17-07_custom_format.json
            odrl_jsonld format: policy_6_BIOSKIN_2025-09-22_13-17-07_new_odrl_jsonld_format.json
        
    """

    # read a policy file
    p = Path("./example_policies/policy_6_BIOSKIN_2025-09-22_13-17-07.json")
    with p.open(encoding="utf-8") as f:
        cactus_format = json.load(f)

    # ODRL validation check
    validate.generate_ODRL_diagnostic_report(cactus_format)

    # format conversion
    custom_format = custom_convert_odrl_policy(cactus_format) #(see https://colab.research.google.com/drive/1bLIqDCpadolC1dfyC4z9p9HPtnEvrqSx#scrollTo=GqYKvyFkuqUa)

    # # save
    with open("./example_policies/policy_6_BIOSKIN_2025-09-22_13-17-07_custom_format.json", "w", encoding="utf-8") as f:
        json.dump(custom_format, f, ensure_ascii=False, indent=2)

    # odrl parse, after that, new_odrl_format can be accepted by contract-service
    filtered_data = filter_dicts_with_none_values(custom_format)
    new_odrl_format = convert_list_to_odrl_jsonld_no_user(filtered_data)


    # # save
    with open("./example_policies/policy_6_BIOSKIN_2025-09-22_13-17-07_new_odrl_jsonld_format.json", "w", encoding="utf-8") as f:
        json.dump(new_odrl_format, f, ensure_ascii=False, indent=2)


    # odrl is sent to contract servvice
    print(json.dumps(new_odrl_format, indent=2))

