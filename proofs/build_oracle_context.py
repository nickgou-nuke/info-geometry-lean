import requests
import json
import sys

ARANGO_URL = "http://127.0.0.1:8529/_db/info_geometry/_api/cursor"
AUTH = ("root", "")

def query_arango(aql, bind_vars=None):
    payload = {"query": aql}
    if bind_vars:
        payload["bindVars"] = bind_vars
    try:
        resp = requests.post(ARANGO_URL, auth=AUTH, json=payload)
        resp.raise_for_status()
        return resp.json().get("result", [])
    except Exception as e:
        print(f"[-] ArangoDB query failed: {e}")
        return []

def assemble_causal_cone(target_keyword):
    """
    Queries the DAG for declarations matching the keyword,
    and extracts their types/values to build the mathematical context.
    """
    print(f"[*] Querying AST topological DAG for '{target_keyword}'...")
    
    # 1. Find the base declarations
    find_decls_aql = """
    FOR d IN lean_decls
      FILTER d.name LIKE CONCAT("%", @keyword, "%")
      LIMIT 10
      RETURN { name: d.name, type: d.type, value: d.value }
    """
    decls = query_arango(find_decls_aql, {"keyword": target_keyword})
    
    if not decls:
        return f"No direct formalizations found in the DAG for '{target_keyword}'. We are at the frontier."

    context = "=== EXTRACTED CAUSAL CONE ===\n\n"
    for d in decls:
        context += f"Declaration: {d['name']}\n"
        if d.get('type'):
            context += f"Type Signature: {d['type']}\n"
        if d.get('value'):
            context += f"Value/Proof: {d['value']}\n"
        context += "-" * 40 + "\n"
        
    return context

def generate_oracle_prompt(goal):
    """
    Assembles the strict prompt for the ChatGPT Oracle.
    It provides the filtered colimit structure and the extracted DAG context.
    """
    
    # In a full run, we would dynamically pull the colimit structures
    colimit_context = assemble_causal_cone("FilteredColimit")
    fibonacci_context = assemble_causal_cone("FibAnyon")
    
    prompt = f"""You are the Intuition Oracle for an Automath pipeline.
Your job is to propose a rigorous mathematical hypothesis and its Lean 4 implementation.
Do not hallucinate external dependencies. You must strictly align with the provided causal cone.

{colimit_context}

{fibonacci_context}

=== YOUR GOAL ===
{goal}

Provide only the valid Lean 4 code to implement this hypothesis. The pipeline will test your code natively.
"""
    return prompt

if __name__ == "__main__":
    if len(sys.argv) < 2:
        goal = "Formulate the Pentagon Identity for Fibonacci Anyons within the existing Filtered Colimit structure."
    else:
        goal = sys.argv[1]
        
    prompt = generate_oracle_prompt(goal)
    
    print("\n[+] Assembled Contextual Prompt for the Oracle:\n")
    print(prompt)
    
    # Here is where we would pipe `prompt` into browser-harness to query ChatGPT.
