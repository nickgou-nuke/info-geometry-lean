# E8 triality: finite readouts and research companions

The Lean owner of this packet is
[E8TrialityThermalProtection.lean](../../../lean/InfoGeometry/E8/E8TrialityThermalProtection.lean),
in namespace `E8Triality`. Its current scope is numerical metadata, permutations
of three representation labels, arithmetic grading, and commutation of complex
scalars. The historical filename does not mean that the module constructs the
split E8 Lie group or proves thermal protection for it.

Source reviewed on 2026-11-03 at commit
`214f7bcf733eaf4720913bc2c082936f2480d3fc`. This is a source review; no new
compilation or companion-system run is recorded here. Follow the
[repository search protocol](../../../docs/REPO_DEEP_SEARCH_PROTOCOL.md) before
extending a local scope observation to other owners.

## What the Lean owner contains

| Declaration | Current content |
|---|---|
| `dim_E8`, `rank_E8`, `coxeter_number_E8`, `positive_roots_E8` | Natural-number constants 248, 8, 30, and 120. |
| `E8SplitForm`, `canonicalE8SplitForm` | A record of dimension, rank, and maximal-compact dimension. `IsCanonical` is a conjunction of numerical equalities. |
| `canonicalE8SplitForm_is_split` | A dimension/rank statement about that record. |
| `maximal_compact_dimension_eq_D8_adjoint` | Equality of the recorded dimension with the D8 adjoint-dimension formula imported from [SplitE88Group.lean](../../../lean/InfoGeometry/Algebra/SplitE88Group.lean). |
| `Spin8Representation` | Three labels: vector, positive spinor, and negative spinor. Each has assigned dimension 8. |
| `triality_sigma_order_3`, `triality_tau_order_2` | Identities for a 3-cycle and a transposition of those labels. `triality_group` is defined as permutations of `Fin 3`. |
| `e8_liouville_grading` | An integer-valued arithmetic grading of natural-number indices. |
| `count_bosonic_e8`, `count_fermionic_e8`, `witten_index_e8` | Finite counts and their difference over positive indices below 248. These indices are not a constructed E8 root system. |
| `e8_liouville_scalar_commutes_phase` | Commutation of a complex scalar grading value with a complex exponential phase, proved by `mul_comm`. |
| `triality_preserves_grading` | Grading evaluated at the assigned dimension is unchanged by cycling the three dimension-8 labels. |
| `positive_roots_E8_add_seven_eq_127` | The numerical identity `127 = 120 + 7`. |
| `witten_index_e8_constant_in_parameter` | The definition of the finite count difference, with an unused positive parameter. |

In particular, the scalar commutation statement has the shape

\[
g(n)\,\phi_t(n)=\phi_t(n)\,g(n),\qquad g(n),\phi_t(n)\in\mathbb C.
\]

Its type does not assert commutation of noncommuting E8 operators. The finite
count theorem does not contain a temperature-dependent partition function,
trace, derivative, or KMS condition. Numerical dimension coincidences do not
define an embedding or representation map.

## Tracked companion files

These files are research and computation companions. Their presence is not a
record that every backend has been executed or that each establishes the same
proposition as the Lean owner.

| File | Role |
|---|---|
| [e8_triality_thermal_protection.py](../e8_triality_thermal_protection.py) | Python computation companion. |
| [e8_triality_bridge.json](e8_triality_bridge.json) | Stored bridge data; inspect its provenance before using it as current output. |
| [E8Triality.v](E8Triality.v) | Coq source companion. |
| [e8_triality_dmodule.m2](e8_triality_dmodule.m2) | Macaulay2 source companion. |

The earlier inventory's proposed `E8Triality.thy` is not a tracked file at the
reviewed commit.

## Research directions retained from the original packet

The original packet proposed a connection between E8 representation theory,
Spin(8) triality, arithmetic parity, exceptional-algebra chains, and thermal
invariants. Treat those as research motivations. A stronger formal result
would need an explicit carrier and action, a grading on that carrier, and a
map from the arithmetic model to the intended representation. A thermal claim
would additionally need the relevant dynamics, states or trace, convergence
hypotheses, and an invariance theorem stated for those objects.

The complete earlier narrative remains available in the
[historical version of this packet](https://github.com/nickgou-nuke/info-geometry-lean/blob/214f7bcf733eaf4720913bc2c082936f2480d3fc/tools/infra/bridge_data/README_E8_TRIALITY.md).
It is research history, not a current proof-completion report.

## Targeted verification

From the repository root, after completing the repository's dependency setup:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.E8.E8TrialityThermalProtection
```

Use the [root build guide](../../../README.md) and preserve the shared cache.
A successful owner build checks its actual declarations and imported
dependencies; companion-system and stronger mathematical claims need their
own evidence.
