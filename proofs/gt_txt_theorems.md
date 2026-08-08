# Extracted Theorems & Conjecture Targets from `g&t.txt`

## Explicit Lean-style declarations

- `theorem exponential_reconstruction_surjective` (line 64)
  - In compact connected context, the discrete Weyl+Cartan data via `exp` is surjective onto the Lie group.

- `theorem metriplectic_flow_to_einstein_equations` (line 220 / duplicated at 469)
  - At `β = 1`, metriplectic steady-state flow plus KMS pole assumptions imply `RicciTensor M = 0`.

- `theorem crystallization_unifies_continuum` (line 327)
  - With O(5,5)-cone preservation and Klein-bottle twist, Riemann zeros lie on the Brillouin boundary.

- `theorem einstein_hilbert_from_phonon_residue` (line 559)
  - Residue at `s=1` of `Tr |D|^{-s}` identifies Einstein–Hilbert action.

- `theorem z2_topological_stability` (line 712)
  - Z2-equivalence class from glide/reciprocal symmetry implies stable Klein-bottle topology.

- `theorem o55_crystallization_stable` (line 1031 / duplicated 1116)
  - O(5,5) Cartan sectors with vanishing twisted index imply reality/localization of spectrum.

- `theorem boost_rotation_commute` (line 1290)
  - Cartesian boost/rotation generators commute when arranged from Cartan + involution.

- `theorem zeros_on_chiral_light_cone` (line 1303)
  - `O ρ = 0 ↔ ρ.re = 1/2` (chiral-light-cone identity).

## Axiom-style declarations in snippets

- `axiom fisherMetric` (line 210, 459)
- `axiom RicciTensor` (line 213, 462)
- `axiom effectiveActionDensity` (line 552)

## Proposed conjecture targets (narrative, not code-named)

- `Cayley_converts_noncompact` (around lines 180–190): Surrogates for non-compact groups via Cayley transform are needed to recover compact-boundary surjectivity.
- `EinsteinField_eq_hydrodynamic_limit` (line 178 / 427): Einstein equations arise as hydrodynamic limit of metriplectic flow at critical `β = 1`.
- `RH_from_crystallization` (various lines): Riemann zeros are interpreted as Bragg peaks confined to `Re(s)=1/2` (Brillouin boundary).
- `Nielsen_Ninomiya_violation_on_klein_bottle` (line 1375): Same-sign exceptional-point monopoles can occur on non-orientable Klein-bottle boundary.
- `Monodromy_T24` (line 1382): Hadjiivanov–Todorov style punctured-Klein-bottle monodromy relation controls braid braiding in vacuum topology.

## Note
This file reflects *only what is present in `g&t.txt`*, not semantic truth status.
