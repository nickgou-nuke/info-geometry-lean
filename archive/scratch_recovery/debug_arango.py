import sys
from pathlib import Path
sys.path.append(".")
from tools.infra.arango_causal_chiral_cone_prompt import arango_target
from tools.infra.arango_dag_algorithms import run_aql

def main():
    target = arango_target(Path("."))
    res = run_aql(target, """
        FOR m IN topology_overlay_edges
          FILTER m.role == "member_of_scc"
          LIMIT 5
          RETURN m._from
    """, {})
    print(f"DEBUG: 5 endpoints = {res}")

if __name__ == "__main__":
    main()
