# Nuclear sector-to-observable contract

User request (2026-10-26): sector projectors → allowed transitions → exact
Feshbach reduction → effective E2/M1 operators → identifiability from joint
energy, transition and transfer data. Base: PR #220, e21e2fec.

Source owners: `NuclearTwoModeFiveGradeLieModel` owns the occupation commutator
grading on M₄(ℝ); `NuclearOperatorSchurComplement.effectiveOperator` owns the
Schur expression; `NuclearConfigurationMixing` owns real two-configuration
spectral reconstruction and coherent transition amplitudes.
`NuclearConfigurationGradedReadout` proves that the finite block is PHP and
exhibits full-Hamiltonian leakage. A compressed eigenvector alone is not a full
eigenvector. Mathlib linear maps, matrices, adjoints and diagonal projectors are
the carriers for the additions.

Implementation contracts:

1. Diagonal sector projectors are complementary/idempotent; a homogeneous
   operator has a zero sector block unless target charge = source charge + grade.
   Instantiate with occupation weights (-1,0,0,1), independently of physical Jπ.
2. On P-space ⊕ Q-space, an explicit two-sided inverse of D−E gives an exact
   eigen-equation equivalence and reconstructed Q component −(D−E)⁻¹Cx.
   Prove preservation of nonzero eigenvectors. Do not invert the zero extension
   Q(H−E)Q on the entire ambient space.
3. For possibly different initial/final finite spaces, Ωf† O Ωi reproduces the
   full complex amplitude, and Ω†Ω reproduces its norm metric. Instantiate Ω
   with Feshbach reconstruction; E2/M1 selection covariance requires a supplied
   physical tensor operator and charge-intertwining dressing.
4. In the existing real, calibrated two-configuration model, transfer fixes
   c²/s²; nonzero real interference calibration fixes cs; spectral energies then
   fix the Hamiltonian entries. Unknown operators and vanishing interference
   do not satisfy this identifiability theorem. Joint inference is conditional,
   not a fit to experimental data.

Scope barriers: CAR grade ≠ electromagnetic rank; occupation parity ≠ spatial
parity. E2/M1 rank/triangle rules require physical angular momentum tensor data.
No completeness of quantum labels, full phonon resolvent, Riemannian curvature,
gravitational mechanism, nuclear chirality measurement or numerical fit follows.
No dependency revisions or existing owner semantics are to be changed.

The implemented statements below have passed the targeted Lean build. Their
physical uses remain conditional on the hypotheses described here.

## Implemented interfaces

| Module | Main result | Required input |
| --- | --- | --- |
| `NuclearSectorSelection` | `five_grade_sector_selection` | Actual occupation commutator eigen-equation |
| `NuclearFeshbachReduction` | `eigen_equation_iff`, `reconstructed_nonzero_eigenvector_iff` | Two-sided inverse of D−E on the complementary space |
| `NuclearEffectiveMultipole` | `effective_amplitude`, `effective_normalized_strength` | Supplied complex transition operator and separate dressings |
| `NuclearEffectiveMultipole` | `feshbach_normMetric_posDef`, `effective_parity_intertwining` | Feshbach dressing; physical parity intertwiners for the latter |
| `NuclearJointSpectroscopyInference` | `joint_data_identifies_hamiltonian` | Fixed real orthonormal model, ordered energies, separated transfer calibration, nonzero real interference calibration |

`inclusive_transfer_response` derives the response TᵀT from a sum of channel
strengths. `orthogonal_transfer_images` supplies the precise condition making
it diagonal. Orthogonality of the chosen final basis alone is insufficient.

The finite Schur theorem explicitly excludes the complementary pole. At that
pole, `complementary_pole_eigenvector` exhibits a nonzero Q-only eigenvector.
The effective operator retains both norm metrics, including their nontrivial
Feshbach correction. The synthetic calibrated example has mixing weights 9/25
and 16/25 and an interference-channel strength 49/25; these are not sulfur-37
measurements. Equal transfer calibrations and a quadrature complex calibration
have explicit information-loss witnesses.

## Physical application boundary

For E2/M1, supply reduced matrix elements, physical spatial parity operators,
and angular tensor hypotheses. `parityEvenMultipoleAllowed` expresses necessary
spin/parity conditions only; it does not prove existence of a transition or
construct Wigner–Eckart coefficients. The E2-compatible 7/2→3/2 branch is
M1-forbidden by its rank triangle condition.

Exact Feshbach elimination is generally energy dependent and nonorthonormal.
The joint identification theorem applies after a **common calibrated real
orthonormal two-configuration realization** has been provided. No theorem here
asserts that an arbitrary full nuclear Hamiltonian admits that realization.
Accordingly the identified object is the finite calibrated Hamiltonian.
Constructing the full phonon resolvent, an angular tensor realization,
experimental response/uncertainty propagation and fitting actual data remain
separate tasks.

## Targeted verification command

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Physics.NuclearSectorSelection \
  InfoGeometry.Physics.NuclearEffectiveMultipole \
  InfoGeometry.Physics.NuclearJointSpectroscopyInference
```

The effective-multipole target imports and checks Feshbach reduction.

## Verification result (2026-10-26)

- `[kernel_verified]`: all four new modules passed the locked targeted build
  (8941 jobs, including cached dependencies) with Lean 4.34.1 and unchanged
  mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- 37 theorems and 10 definitions were inspected with `#print axioms`: only
  `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` or custom axioms.
- An independent read-only semantic audit accepted the documented scope. Its
  corrections concerning parity-even ranks, transfer-image orthogonality,
  reduced matrix elements and the calibrated finite realization are incorporated.
- The repository-root build stops before elaboration because the existing
  `external_refs/atlas-lean` package is absent. Verification instead used an
  isolated Lake project importing the actual repository sources and the same
  pinned mathlib. No repository dependency manifest or toolchain was changed.
- Existing dependency warnings remain. The new sector module also reports
  three nonblocking deprecation warnings for `if_pos`/`if_neg` on this pin.
  No full-repository CI success or experimental fit is claimed.
- Staged proof-proxy, placeholder and whitespace scans pass. The semantic
  vacuity gate passes with zero errors and three `trivial_surface` heuristic
  warnings (`normMetric_readout`, `effective_eq_existing`,
  `sectorProjector_transpose`). Independent review confirmed that these are
  legitimate small identities/API compatibility facts, with no circularity or
  unsupported physical conclusion. Final independent acceptance passed after
  inspecting the successful build and all 47 axiom reports.
