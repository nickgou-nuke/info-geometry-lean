# Bost–Connes arithmetic and thermofield research packet

The Lean owner is
[BostConnesThermofield.lean](../../../lean/InfoGeometry/BostConnes/BostConnesThermofield.lean),
in namespace `BostConnesThermofield`. It supplies arithmetic parity and Möbius
identities, a reciprocal-zeta L-series theorem, and commutation of scalar
grading values with complex phases. The current theorem types do not establish
temperature-independent topological anomalies or `dW/dβ = 0`.

Source reviewed on 2026-11-03 at commit
`214f7bcf733eaf4720913bc2c082936f2480d3fc`. No new build or backend execution
is reported here. See the
[repository search protocol](../../../docs/REPO_DEEP_SEARCH_PROTOCOL.md) and the
more general [Bost–Connes tools guide](../../bost_connes/README.md) for related
work.

## Current Lean content

| Declaration | Statement or definition actually present |
|---|---|
| `BostConnesGenerator` | A positive natural-number carrier, with a proof that its sector is nonzero. |
| `modular_flow`, `modular_phase` | The complex phase `exp (I * t * log n)`. |
| `modular_phase_zero` | The phase at time zero is one. |
| `liouville_commutes_modular_flow` | A complex cast of the arithmetic parity commutes with the complex phase, by scalar multiplication commutativity. |
| `witten_index` | A real `tsum` of Möbius-weighted powers over positive naturals. |
| `witten_index_eq_reciprocal_zeta` | For real `beta > 1`, the **complex** Möbius L-series satisfies `L ↗μ (beta : ℂ) = (riemannZeta (beta : ℂ))⁻¹`. |
| `thermal_anomaly_protection` | Universal quantification of the same scalar commutation identity over `t` and `n`. There is no temperature parameter or derivative in its conclusion. |
| `moebius_decomposition` | The Möbius function equals the squarefree projector times Liouville parity. |
| `pauli_exclusion` | For a nonsquarefree natural number, the Möbius value is zero. |
| Sector counts and `witten_index_approx` | Finite arithmetic readouts, to be distinguished from the infinite series and any physical trace interpretation. |

The name `witten_index_eq_reciprocal_zeta` should be read with its full type:
the theorem is about the complex L-series. It does not itself identify the
separately defined real `witten_index` with that L-series. Such an identification
would need its own convergence and real/complex transport argument.

Likewise, commutation of complex numbers does not establish an operator-algebra
KMS boundary condition or a temperature-conservation law. The reciprocal-zeta
identity is an arithmetic result on `beta > 1`; it is not a claim that its value
is constant as `beta` varies.

## Tracked companion files

| File | Role |
|---|---|
| [bost_connes_thermofield.py](../bost_connes_thermofield.py) | Python arithmetic/research companion. |
| [galgebra_clifford_bost_connes.py](../galgebra_clifford_bost_connes.py) | GaAlgebra/Clifford computation companion. |
| [bost_connes_bridge.json](bost_connes_bridge.json) | Stored bridge data. |
| [BostConnesThermofield.v](BostConnesThermofield.v) | Coq source companion. |
| [BostConnesThermofield.thy](BostConnesThermofield.thy) | Isabelle/HOL source companion. |
| [bost_connes_dmodule.m2](bost_connes_dmodule.m2) | Macaulay2 source companion. |

These paths establish source availability, not equal coverage or a fresh pass
in every backend. Numerical output needs a reproducible command, parameters,
truncation bound, and date before it is used as evidence. The former placeholder
values such as `0.XXX` were not measurements.

## Historical research interpretation

The original packet connected arithmetic Liouville parity, squarefree sectors,
thermofield language, modular dynamics, and a graded trace. Those are useful
motivations for further work. A thermodynamic claim needs an explicit algebra,
dynamics, state or trace, domain and convergence hypotheses, and the relevant
invariance theorem. Preserve the distinction between that research objective
and the scalar/arithmetic statements above.

The full original narrative remains in the
[historical packet](https://github.com/nickgou-nuke/info-geometry-lean/blob/214f7bcf733eaf4720913bc2c082936f2480d3fc/tools/infra/bridge_data/README_BOST_CONNES.md).
Its all-temperature conservation and cross-system completion statements are
historical assertions, not current theorem coverage.

## Targeted verification

From the repository root, with dependencies prepared:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.BostConnes.BostConnesThermofield
```

Follow the [root build guide](../../../README.md). Report the commit and actual
command result for any new verification; a successful build checks the stated
arithmetic theorems and does not supply the missing thermodynamic interpretation.
