import sys
from pathlib import Path
sys.path.append(".")
from tools.infra.arango_causal_chiral_cone_prompt import arango_target
from tools.infra.arango_dag_algorithms import run_aql

def main():
    target = arango_target(Path("."))
    res = run_aql(target, """
        FOR m IN topology_overlay_edges
          FILTER m.role == "member_of_scc" && m.member_key == "InfoGeometry.Canonical.o55_tkk_anomaly_cancellation"
          RETURN m
    """, {})
    print(f"DEBUG: memberships for o55_tkk_anomaly_cancellation = {res}")

if __name__ == "__main__":
    main()
