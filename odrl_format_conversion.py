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
            bn = BNode()
            triples_to_add.append((s, p, bn))
            triples_to_add.append((bn, ODRL.source, o))
            triples_to_remove.append((s, p, o))

    for t in triples_to_remove:
        g.remove(t)
    for t in triples_to_add:
        g.add(t)

    # Step 2: Replace all blank nodes with fresh IRIs,
    # except if they are part of RDF lists.
    bnode_to_iri = {}

    # Detect all blank nodes used in RDF collections
    list_bnodes = set()
    for s, p, o in g.triples((None, RDF.first, None)):
        list_bnodes.add(s)
    for s, p, o in g.triples((None, RDF.rest, None)):
        list_bnodes.add(s)
        if isinstance(o, BNode):
            list_bnodes.add(o)

    for s, p, o in list(g):
        new_s = bnode_to_iri.get(s)
        new_o = bnode_to_iri.get(o)

        if isinstance(s, BNode) and s not in list_bnodes:
            if s not in bnode_to_iri:
                bnode_to_iri[s] = EX[str(uuid.uuid4())]
            new_s = bnode_to_iri[s]

        if isinstance(o, BNode) and o not in list_bnodes:
            if o not in bnode_to_iri:
                bnode_to_iri[o] = EX[str(uuid.uuid4())]
            new_o = bnode_to_iri[o]

        if new_s or new_o:
            g.remove((s, p, o))
            g.add((new_s or s, p, new_o or o))

    return g

def isJsonBlankNodesGraphFormat(json_ld_obj):
    """
    Returns True if the JSON-LD object contains explicitly defined blank nodes
    (e.g., "@id": "_:b0"), otherwise False.
    """

    # Ensure input is a dictionary
    if not isinstance(json_ld_obj, dict):
        return False

    # Extract the "@graph" key if it exists
    graph_data = json_ld_obj.get("@graph", None)

    if not graph_data or not isinstance(graph_data, list):
        return False

    # Helper function to recursively search for blank node identifiers
    def contains_blank_node(obj):
        if isinstance(obj, dict):
            # Check if the dict has an @id starting with "_:"
            if "@id" in obj and isinstance(obj["@id"], str) and obj["@id"].startswith("_:"):
                return True
            # Otherwise, recurse into values
            return any(contains_blank_node(v) for v in obj.values())
        elif isinstance(obj, list):
            return any(contains_blank_node(i) for i in obj)
        return False

    # Check all objects in @graph for blank nodes
    return any(contains_blank_node(item) for item in graph_data)

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
        result = []

        qres = g.query(query, initNs={'odrl': ODRL, 'dpv': DPV, 'rdf': RDF})

        for row in qres:
            left = str(row.left)
            op = str(row.op)
            right = row.right

            # If right is a list head (rdf:first / rdf:rest)
            if isinstance(right, BNode) and (right, RDF.first, None) in g:
                collection = Collection(g, right)
                for item in collection:
                    result.append({
                        "type": left,
                        "operator": op,
                        "value": [str(item.toPython() if hasattr(item, 'toPython') else item)]
                    })
            else:
                result.append({
                    "type": left,
                    "operator": op,
                    "value": [str(right.toPython() if hasattr(right, 'toPython') else right)]
                })

        return result

    # Get constraints (grouped)
    constraints_query = """
    SELECT ?left ?op ?right WHERE {
      <%s> odrl:constraint ?c .
      ?c odrl:leftOperand ?left ;
         odrl:operator ?op ;
         odrl:rightOperand | odrl:rightOperandReference ?right .
    }
    """ % rule_uri
    constraints = group_constraints_or_refinements(constraints_query)

    # Extract purpose constraint if it is the only constraint
    purpose = ""
    if len(constraints) == 1:
        constraint = constraints[0]
        if (
            constraint.get("type") == str(ODRL.purpose)
            and constraint.get("operator") == str(ODRL.eq)
        ):
            values = constraint.get("value") or []
            if values:
                purpose = values[0]
                constraints = []

    # Get actor refinements (grouped)
    actor_ref_query = """
    SELECT ?left ?op ?right WHERE {
      <%s> odrl:assignee ?actorNode .
      ?actorNode odrl:refinement ?ref .
      ?ref odrl:leftOperand ?left ;
           odrl:operator ?op ;
           odrl:rightOperand | odrl:rightOperandReference ?right .
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
           odrl:rightOperand | odrl:rightOperandReference ?right .
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
           odrl:rightOperand | odrl:rightOperandReference ?right .
    }
    """ % rule_uri
    target_refinements = group_constraints_or_refinements(target_ref_query)

    return {
        "rule": str(rule_type),
        "actor": actor,
        "action": action,
        "target": target,
        "purpose": purpose,
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
    # data_list = recursive_replace (data_list,"https://w3id.org/dpv/owl#","https://w3id.org/dpv#")
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
            "dpv": "https://w3id.org/dpv/owl#",
        }
        ],

        "@type": "Policy",
    }
    for data in data_list:
        if data["action"] is not None and data["actor"] is not None and data["target"] is not None:
            if "rule" in data:
                ruleType = str(data["rule"].split("/")[-1]).lower()

                if len(data["actorrefinements"])>0:
                    actor = {"@type":"PartyCollection", "source": data["actor"], "refinement": []}
                else:
                    actor = data["actor"]
                if len(data["actionrefinements"])>0:
                    action = {"source": data["action"], "refinement": []}
                else:
                    action = data["action"]


                if len(data["targetrefinements"])>0:
                    target = {"@type":"AssetCollection", "source": data["target"], "refinement": []}
                else:
                    target = data["target"]

                odrl_jsonld = {
                    "action": action,  # Extract the action type
                    "assignee": actor,
                    "target": target,
                    "constraint": [],
                }

                if len(data["purposerefinements"])>0:

                    purpose = data["purpose"]
                    purposerefinements = {"and":[]}
                    purposerefinements["and"].append({
                        "leftOperand": "purpose",
                        "operator": "http://www.w3.org/ns/odrl/2/eq",
                        "rightOperand": purpose,
                    })

                    for constraint in data["purposerefinements"]:

                        if constraint["operator"] is not None:
                            purposerefinements["and"].append(
                                {
                                    "leftOperand": constraint["type"].split("#")[
                                        -1
                                    ],  # Extract the constraint type
                                    "operator": constraint["operator"],
                                    "rightOperand": constraint["value"],
                                }
                            )

                    odrl_jsonld["constraint"].append(purposerefinements)
                else:
                    purpose = data["purpose"]
                    if purpose:
                      odrl_jsonld["constraint"].append(
                          {
                              "leftOperand": "purpose",
                              "operator": "http://www.w3.org/ns/odrl/2/eq",
                              "rightOperand": purpose,
                          }
                      )
            else:
                ruleType = "rule"
                odrl_jsonld = {
                    "action": data["action"],  # Extract the action type
                    "assignee": data["actor"],
                    "constraint": [],
                }
            if "query" in data:
                if data["query"] is not '':
                    odrl_jsonld["constraint"].append(
                        {
                            "leftOperand": "ex:query",
                            "operator": "http://www.w3.org/ns/odrl/2/eq",
                            "rightOperand": data["query"],
                        }
                    )
            for constraint in data["constraints"]:
                if constraint["operator"] is not None:
                    odrl_jsonld["constraint"].append(
                        {
                            "leftOperand": constraint["type"].split("#")[
                                -1
                            ],  # Extract the constraint type
                            "operator": constraint["operator"],
                            "rightOperand": constraint["value"],
                        }
                    )
            for constraint in data["actorrefinements"]:
                if constraint["operator"] is not None:
                    print(constraint)
                    print(odrl_jsonld)
                    print(odrl_jsonld["assignee"]["refinement"])
                    print(constraint["type"])
                    print(constraint["operator"])
                    print(constraint["value"])
                    odrl_jsonld["assignee"]["refinement"].append(
                        {
                            "leftOperand": constraint["type"].split("#")[
                                -1
                            ],  # Extract the constraint type
                            "operator": constraint["operator"],
                            "rightOperand": constraint["value"],
                        }
                    )
            for constraint in data["actionrefinements"]:
                if constraint["operator"] is not None:
                    odrl_jsonld["action"]["refinement"].append(
                        {
                            "leftOperand": constraint["type"].split("#")[
                                -1
                            ],  # Extract the constraint type
                            "operator": constraint["operator"],
                            "rightOperand": constraint["value"],
                        }
                    )
            for constraint in data["targetrefinements"]:
                if constraint["operator"] is not None:
                    odrl_jsonld["target"]["refinement"].append(
                        {
                            "leftOperand": constraint["type"].split("#")[
                                -1
                            ],  # Extract the constraint type
                            "operator": constraint["operator"],
                            "rightOperand": constraint["value"],
                        }
                    )
            policy[ruleType].append(odrl_jsonld)
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
        cactus policy format --> validation check --> negotiation_front_format --> filtered_data (clean the null value) --> convert to odrl_format
        for example in example_policies:
            
            
            Cactus policy format: policy_6_BIOSKIN_2025-09-22_13-17-07.json
            negotiation_front_format:policy_6_BIOSKIN_2025-09-22_13-17-07_negotiation_front_format.json        
            filtered_data: policy_6_BIOSKIN_2025-09-22_13-17-07_filtered_data.json
            odrl_format: policy_6_BIOSKIN_2025-09-22_13-17-07_odrl_format.json
            
            make a request body to create a negotiation, where odrl_policy is that:
             "odrl_policy": {
                "odrl":  odrl_format
                "data":  filtered_data
            }
            
            Also, this convertor can pase graph format from Abovo
            for example:
            graph_format.json -> graph_negotiation_front_format.json -> graph_filtered_data.json -> graph_odrl_format.json
            
            so the request body using to create a negotiation is as follows:
            {
                "_id": "68ecece0bb1e35369de0919a",
                "title": null,
                "type": "request",
                "consumer_id": "68c490375a5c04b2f5f9ed75",
                "provider_id": "68c48ff75a5c04b2f5f9ed74",
                "data_processing_workflow_object": {...},
                "natural_language_document": "natural_language_document_value",
                "resource_description_object": {...},
                "odrl_policy": {
                "odrl":  graph_odrl_format
                "data":  graph_filtered_data
                }

            }

        
    """

    # read a policy file
    p = Path("./example_policies/graph_format.json")
    with p.open(encoding="utf-8") as f:
        cactus_format = json.load(f)

    # ODRL validation check
    validate.generate_ODRL_diagnostic_report(cactus_format)

    # format conversion
    negotiation_front_format = custom_convert_odrl_policy(cactus_format) #(see https://colab.research.google.com/drive/1bLIqDCpadolC1dfyC4z9p9HPtnEvrqSx#scrollTo=GqYKvyFkuqUa)

    # # save
    with open("example_policies/graph_negotiation_front_format.json", "w", encoding="utf-8") as f:
        json.dump(negotiation_front_format, f, ensure_ascii=False, indent=2)

    # odrl parse, after that, new_odrl_format can be accepted by contract-service
    filtered_data = filter_dicts_with_none_values(negotiation_front_format)

    # # save
    with open("example_policies/graph_filtered_data.json", "w",
              encoding="utf-8") as f:
        json.dump(filtered_data, f, ensure_ascii=False, indent=2)


    odrl_format = convert_list_to_odrl_jsonld_no_user(filtered_data)


    # # save
    with open("example_policies/graph_odrl_format.json", "w", encoding="utf-8") as f:
        json.dump(odrl_format, f, ensure_ascii=False, indent=2)



