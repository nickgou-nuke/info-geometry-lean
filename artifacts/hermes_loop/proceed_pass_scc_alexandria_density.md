# Proceed pass: SCC-first DAG audit + operatorial readout reduction

Repo state
- worktree: `/home/goutev/repos/info-geometry-lean-fusion`
- branch: `fusion/upstream-intake-20260419`
- HEAD: `da4c1e0`

## 1. SCC-first Arango-DAG audit

Anchors used:
- seed: `InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed`
  - raw node: `raw_95fbdcd9d290c6ea39e79049e1395518bd63f5e7`
  - SCC: `scc_f69be33ad67b5e6e0e03b0195aa79e3d990210ae`
- target A: `InfoGeometry.Canonical.CalabiYauBridge.RNEntropySourcesMongeAmpere`
  - raw node: `raw_e1dc0633d0ecd359114d1a905bf3ace1e185f44d`
  - SCC: `scc_0cb7587516041c200b90c073817d927d594474d3`
- target B: `InfoGeometry.Canonical.MongeAmpereCramerRao.IncompressibleMongeAmpere`
  - raw node: `raw_532384db8e8af7a19f160568fdd91d85895a572f`
  - SCC: `scc_1315a6800125478d205ebac0299eb2f4164ada2b`

Connectedness results on `topology_overlay_edges` with `role == "scc_quotient"`:

- forward reachability seed -> RN target: none
- reverse reachability RN target -> seed: none
- weak connectedness seed <-> RN target: yes, depth 2
  - path: `scc_f69be... -> scc_a40b3a... -> scc_0cb758...`

- forward reachability seed -> incompressible target: none
- reverse reachability incompressible target -> seed: none
- weak connectedness seed <-> incompressible target: yes, depth 2
  - path: `scc_f69be... -> scc_a40b3a... -> scc_1315a6...`

Raw witness descent for the weak-basin intermediate:
- the intermediate SCC `scc_a40b3a...` is an endpoint-stub overlay basin
- witness edges from RN target and incompressible target into that basin descend to raw dependencies on `CompleteSpace`
- example raw witnesses:
  - `RNEntropySourcesMongeAmpere -> CompleteSpace`
  - `IncompressibleMongeAmpere -> CompleteSpace`

Interpretation:
- same weak theorem basin exists
- no directed theorem flow from `GibbsSouriauEquilibriumSeed` into RN-entropy or incompressibility owners
- this is navigation/audit evidence only, not proof
- the missing bridge remains real

## 2. Alexandria / arXiv ingestion pass

Repo-native Alexandria tooling confirmed present:
- `tools/alexandria/fetch_arxiv_corpus.py`
- `tools/alexandria/semantic_ingest.py`
- `tools/alexandria/graph_context_rank.py`
- docs: `docs/alexandria/ALEXANDRIA_SKILL.md`

Run performed:
1. fetched arXiv source markdown for the Souriau context ids
   - ids file: `artifacts/alexandria/souriau_lie_thermo_context/arxiv_ids.txt`
   - output: `artifacts/alexandria/live_souriau_fetch/`
   - fetched:
     - `2104.12621.tex.md`
     - `2109.12806.tex.md`
2. semantic digest created at:
   - `artifacts/alexandria/live_souriau_digest/`
3. graph rerank executed with the Alexandria graph runtime venv:
   - output: `/tmp/alexandria_live_souriau_rank.json`

Honesty note:
- second Alexandria Arango instance on `127.0.0.1:8530` is not running (`connection refused`)
- therefore this pass used local Alexandria digest + graph ranking, not live Alexandria-Arango ingest

## 3. Actual theorem reduction made

File changed:
- `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean`

Added theorems:
- `densityWeightLiftedReadout_zero_pair_eq_comparisonReadout_pair`
- `densityWeightLiftedReadout_zero_pair_eq_zero_of_equilibriumSeed`

Meaning:
- zero-weight density-lifted readout is exactly the comparison-state thermodynamic readout
- therefore a `GibbsSouriauEquilibriumSeed` forces the zero-weight density-lifted metric/phase packet to vanish

This is a genuine infinite-operatorial reduction on the doubled carrier.
It does not use any finite response matrix or toy determinant argument.

## 4. Verification
- `lake build InfoGeometry.Canonical.DensityWeightIntertwinerBridge` ✅
- manual harness:
  - `tests/test_density_weight_equilibrium_bridge_theorems.py` ✅
  - `tests/test_souriau_conformal_equilibrium_seed.py` ✅
  - `tests/test_souriau_thermodynamic_readout_seed_bridge.py` ✅

## 5. Remaining frontier
Still open and real:
- `GibbsSouriauEquilibriumSeed -> RNEntropySourcesMongeAmpere ...`
- `GibbsSouriauEquilibriumSeed -> IncompressibleMongeAmpere ...`
- `GibbsSouriauEquilibriumSeed -> CI.chiralScale = kahlerPotentialRN ...`

After this pass, the strongest newly-owned upstream statement is:
- `GibbsSouriauEquilibriumSeed -> zero-weight density-lifted readout packet = (0,0)`

The next honest target is to turn that zero-weight operatorial readout into a true volume/density-control witness, not to pretend the RN-entropy or Kähler/chiral bridge already exists.
