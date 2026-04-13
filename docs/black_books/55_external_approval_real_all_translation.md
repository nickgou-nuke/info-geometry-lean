# External Approval Roadmap (Repo-Native Real Translation)

## 0. Scope

This roadmap is the repo-native translation layer for the doubled real carrier:

- carrier: `H₂ := DoubledSpace E`
- axes: `J := modular_j`, `ε := spectral_epsilon`, `K := J ∘ ε = phaseAxisK`
- projected Drazin lane: `P_D, P_L, P_R, Γ_S, Γ_G, G, χ_L, χ_R, Q_D, H_D`

It freezes sign conventions, identifies gauge-equivalent sign flips, and defines the shortest closure path to Tomita–Takesaki/type III integration without importing external complex-first primitives.

---

## 1. Canonical Orientation Contract

Freeze one convention globally:

1. `S = J_TT Δ^(1/2)`
2. `σ_t(x) = Δ^(it) x Δ^(-it)`
3. `Δ = exp(-H_mod)` so `σ_t = Ad(exp(-it H_mod))`
4. repo phase axis: `K = J ∘ ε`, `K^2 = -1`
5. wedge normalization: `H_mod = 2π B_W`, `τ = 2π t`

### Gauge-equivalent flips (not theory changes)

- `K ↦ -K`: flips partner orientation, preserves linear/antilinear classes.
- `J ↦ -J`: preserves `J M J = M'` and conjugation action.
- `ε ↦ -ε`: swaps plus/minus projector labels.
- `M ↔ M'`: equivalent to modular time reversal in left/right conventions.

These are label gauges. They do not change invariants; they only change orientation conventions.

### Algebra/commutant sign diagnostic (pre-seal)

When a sign mismatch appears in left/right labels, treat it first as an orientation gauge issue:

- swap `M ↔ M'` is equivalent to modular-time reversal in conventions;
- `J ↦ -J` preserves conjugation and commutant action;
- `K ↦ -K` preserves `KLinear`/`KAntilinear` classes, only flips partner orientation;
- `ε ↦ -ε` swaps chiral labels but preserves projector algebra.

Do not classify this as a mathematical defect unless an invariant changes (index, centrality class, fixed-sector theorem, or transported closure law).

---

## 2. Current Owned Surfaces (already compiled on `main`)

### Lean owners

- `Canonical/HestenesRealStructures.lean`
  - `KLinear`, `KAntilinear`, `KreinIsometric`, `KramersSymmetry`, `MajoranaRealStructure`.
- `Canonical/TimeReversalKramers.lean`
  - real time-reversal and Kramers package on doubled real carrier.
- `Canonical/HestenesKramersBridge.lean`
  - intrinsic Kramers phase-partner lane from `K`.
- `Canonical/DrazinPenroseDilationKKT.lean`
  - explicit Drazin–Penrose–dilation Cartan/KKT generator surface.
- `Canonical/DrazinSupercharge.lean`
  - `Q_D := χ_R - χ_L = 2[P_D,G]`, odd/even parity, internal split for `Q_D^2`.
- `Canonical/KramersSuperchargeBridge.lean`
  - Kramers/Majorana compatibility on `(χ_L, χ_R, Q_D, H_D)`.
- `Canonical/UnifiedSuperchargeAlgebra.lean`
  - primitive + transported + projected + topological central-charge canopy.
- `Canonical/TomitaTakesakiRealStandardForm.lean`
  - real-standard-form orientation gauges and modular/wedge parameter normalization.
- `Canonical/ModularOrientationContract.lean`
  - sign/orientation contract over projector-flux and modular transport conventions.
- `Canonical/RealTomitaCore.lean`
  - real `δ = log Δ` interface, transport/adjoint-flow APIs, wedge normalization maps.
- `Canonical/WedgeBoostModularBridge.lean`
  - wedge/boost reparameterization bridge and modular-time ↔ wedge-rapidity roundtrip.
- `Canonical/TypeIIIContinuousCoreReal.lean`
  - real Type-III core interface (dual action, trace invariance, fixed-sector API).
- `Canonical/ModularSuperchargeClosure.lean`
  - canonical-seed modular capstone bridge for projected even/central split transport.

### Umbrella integration

- `Canonical/All.lean` imports the above lane.
- `lake build InfoGeometry.Canonical.All` passes.
- `lake build InfoGeometry.All` passes.

---

## 3. Remaining Closure Gap (precise)

### Gap A: Tomita identification capstone

`Canonical/ModularSuperchargeClosure.lean` is now assumption-free on the
even/generator identification: `H_D = modularTransportGenerator` is derived
from the canonical seed `h_mod := -(H_D ∘ K)`.

The remaining modular closure is stronger: identify this even generator with
the fully owned Tomita/wedge modular Hamiltonian lane (not only with a
constructed modular transport seed).

Current closure progress (implemented):

- `CanonicalSeedTomitaCompatibility` now identifies the canonical seed with an
  owned `RealTomitaCore.RealModularLogData` package via `hDeltaLog`.
- Compiled bridge theorems now provide:
  - `H_D = T.generator`,
  - canonical-seed flow equals `T.flow`,
  - canonical-seed adjoint flow equals `T.adjointFlow`,
  - Tomita-side fixedness of `H_D`,
  - wedge-time Tomita flow equality under a wedge-compatibility witness.

So the remaining part of Gap A is no longer seed-to-Tomita identification; it
is isolated to one canonical lower-owner theorem target:

- `canonicalSeedFlowEqUnruhTarget`, i.e.
  `FlowEqUnruh(canonicalModularSeed)`.

All wedge/Unruh bridge APIs are now reduced to this single target instead of
the older external witness packaging.

### Gap B: spectral infinite-dimensional doorway

- `Canonical/DrazinSpectralBridge.lean` is now discharged as a closure-clean bridge owner.
- Remaining work in this lane is no longer scaffold removal, but stronger downstream consumers.

### Gap C: stronger internal central term

Current internal split is available, but the strongest target remains:

- non-scalar canonical central candidate in Drazin algebra,
- explicit centrality proof against declared generator surface,
- index/supertrace shadow theorem tied to existing operatorial central charge lane.

### Gap D: `Z_op` vs `Z_scalar` closure statement

Freeze this distinction explicitly:

- `Z_op` is central only on an enlarged lane (continuous-core / relative commutant / graded extension);
- `Z_scalar` is obtained as Breuer-index or K-pairing shadow on the traced lane;
- integer-valued `Z_scalar : ℤ` requires explicit hypotheses (compact ideal + K-theory pairing, or spectral-triple ellipticity package).

No theorem should claim integer scalar central charge without naming these hypotheses.

---

## 4. Implementation Ladder (next file-by-file closures)

### Step 1: `Canonical/ModularKramersBridge.lean` (strengthen)

Add:

- theorem family linking Kramers symmetry and modular flow covariance;
- explicit orientation-gauge invariance lemmas (`K`, `J`, `ε` flips);
- fixed-sector theorems for modular flow under Kramers/Majorana compatibility.

### Step 2: `Canonical/KramersMajoranaCompatibility.lean` (capstone relation)

Add precise relation theorem between:

- abstract Kramers symmetry `Θ`,
- intrinsic phase-partner map `u ↦ K u`,
- Majorana involution `C`.

Goal: state when `Θ` reduces/factors through phase-axis lane versus when it is genuinely more general.

Status:

- completed first integrated package:
  - canonical reduction identity `Θ = R ∘ K` with `R := -(Θ ∘ K)`,
  - Majorana stability of `Θ`,
  - Majorana stability of the canonical reduction factor `R`.

### Step 3: `Canonical/DrazinModularSingularityBridge.lean` (operatorial apex translation)

Formalize singularity language strictly as:

- support/kernel projector concentration,
- defect projector obstruction,
- modular fixed/centralizer sector localization,
- transported mismatch persistence.

No free geometric metaphor without projector/modular witness.

### Step 4: `Canonical/KKTNoetherCharges.lean` (preserved operator charges)

Define and prove conserved operator charges under:

- spectral grading flow,
- geometric grading flow,
- transported commutator dynamics.

Treat scalar charges as spectral/index shadows of operator charges.

### Step 5: wedge/type III owner surfaces (completed)

Implemented:

- `Canonical/WedgeBoostModularBridge.lean`
- `Canonical/TypeIIIContinuousCoreReal.lean`
- `Canonical/ModularSuperchargeClosure.lean`

Current follow-up is strengthening from canonical-seed closure to explicit
Tomita/wedge modular-Hamiltonian identification by discharging
`canonicalSeedFlowEqUnruhTarget` from lower owners.

---

## 5. Type III Translation in Split-Clifford Real Language

Use this doctrine:

1. **Carrier doubling**: `H₂`.
2. **Standard-form doubling**: `J_TT M J_TT = M'` in real operator language.
3. **Dynamical doubling**: crossed-product/core lane for modular flow.
4. **Central first**: operator central term first; scalar/index only as shadow.

Operationally inside this repo:

- do not start from external antiunitary primitives;
- represent complex phase internally via `K`;
- represent singularity via projections/support/centralizer behavior;
- represent topological invariants through already-owned index lane.

### Modular fixed-sector caveat

The sentence "Drazin projector isolates modular fixed sector" is valid only with a witness connecting the Drazin seed to modular generator data (e.g. `A = f(log Δ)` on the declared lane; unbounded details isolated behind interfaces). Do not claim this equivalence unconditionally.

---

## 6. DAG/Python Toolchain Extensions (complexity-safe)

The DAG already supports semantic/process flow analysis. Add only scalable algorithms.

### A. Defect transport potential (linear time)

- Input: process-flow edges + defect tags.
- Algorithm: reverse BFS / reverse topological relaxation on condensation DAG.
- Complexity: `O(V + E)`.
- Output: per-node defect potential and nearest-defect witness path.

### B. Signed flow centrality (iterative sparse diffusion)

- Input: directed signed semantic flow graph.
- Algorithm: power iteration with defect/source injection on sparse adjacency.
- Complexity: `O(kE)` where `k` is small fixed iteration budget.
- Output: ranking of anomaly carriers and robust sinks.

### C. SCC Wilson-frustration proxy (linear time)

- Input: signed edges within SCCs.
- Algorithm: 2-color consistency test + frustration score per SCC.
- Complexity: `O(V + E)`.
- Output: localized non-equilibrium/obstruction loops.

### D. Multi-source shortest explanation paths (bounded)

- Input: top anomaly nodes and selected sinks.
- Algorithm: bounded BFS on condensation graph.
- Complexity: `O(E)` per batch with small frontier cap.
- Output: concise explanation chains for audit reports.

Avoid all-pairs shortest paths and dense spectral decompositions on full declaration graphs.

---

## 7. Repository-wide Tracking Policy (Lean / MD / Python / Config)

### Lean

- every new closure theorem must live on a declared owner surface;
- capstones may depend upward, owners must remain low and load-bearing;
- keep scaffold-only files outside closure-critical import surfaces.

### Markdown

- one canonical roadmap per lane (`black_books/*`),
- report status must name exact compiled owners and exact remaining gaps,
- avoid conceptual claims without file-level theorem owners.

### Python

- tooling reports summarize only; Lean owners decide truth;
- algorithms must have explicit complexity budgets;
- prefer condensation/SCC/sparse diffusion methods.

### Config

- keep one manifest schema for semantic gates,
- hard-fail adapters on subprocess errors,
- keep replay as fresh-checkout replay (not in-place rebuild).

---

## 8. Immediate action queue

1. Extend the reduction/compatibility package with uniqueness-on-fixed-sector consequences (canonicality witnessed on Majorana submodule level).
2. Grow downstream consumers of the Tomita identification bridge now that canonical-seed and wedge-normalized generator agreement is compiled.
3. Grow downstream consumers of the intrinsic non-scalar internal central lane now that strict non-scalarity witness theorems are compiled.
4. Grow downstream consumers of `DrazinSpectralBridge` and eliminate remaining scaffold-only surfaces from closure-critical paths.

---

## 9. Pre-seal acceptance checklist

Seal only when all are true:

1. Orientation-equivalence theorems for `K/J/ε` flips and `M ↔ M'` are explicitly present and referenced by modular bridge files.
2. `Z_op` (operator lane) and `Z_scalar` (index shadow) are separated in statements and documentation, with integrality hypotheses named where needed.
3. Canonical modular-seed bridge is identified with the wedge-normalized Tomita generator lane by a compiled theorem family.
4. Any claim linking Drazin fixed sectors to modular fixed sectors names the functional bridge hypothesis (`A` vs `log Δ`) and interface assumptions.
5. `DrazinSpectralBridge` is authoritative for bridge claims; keep strengthening with nontrivial consumer theorems.

This closes the theory in the repo’s real doubled language without reintroducing complex-first scaffolding.
