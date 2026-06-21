#!/bin/bash
set -ex
PYTHONPATH=. python3 tools/infra/hydrate_arango_topology.py --input-dir artifacts/dag/index --output-dir artifacts/dag/hydrated-arango
ln -sf ../index/decls.jsonl artifacts/dag/hydrated-arango/decls.jsonl
ln -sf ../index/edges.jsonl artifacts/dag/hydrated-arango/edges.jsonl
PYTHONPATH=. python3 tools/infra/arango_layered_ingest.py --input-dir artifacts/dag/hydrated-arango --raw-nodes-collection raw_info_nodes --raw-edges-collection raw_info_edges --overlay-nodes-collection topology_overlay_nodes --overlay-edges-collection topology_overlay_edges --drop-existing
PYTHONPATH=. python3 tools/infra/arango_causal_chiral_cone_prompt.py --decl InfoGeometry.Canonical.o55_tkk_anomaly_cancellation --overlay-nodes-collection topology_overlay_nodes
