# Configuration mixing on the existing five-grade operator carrier

## Ground-truth contract

This extends the finite real mixing and decay inference in PR #220 using
existing repository owners at base `2d3a6ed286fde7098d152b83c9c75580b98865d0`.
The current source, rather than an older PR's description, fixes the carrier.

Owners:

* `NuclearFiveGradeCommonCarrierRepresentation`: `Carrier = ℕ → Fin 4 → NativeZorn`,
  `Operator = Module.End ℝ Carrier`, the represented grading matrix `G`, exact
  CAR/CCR, and `RepresentedHasGrade k T`, meaning `G*T-T*G=(k:ℝ)•T`.
* `NuclearTwoModeFiveGradeLieModel.gradingOperator_eq_diagonal`:
  the fermionic grading matrix is `diag(-1,0,0,1)`.
* `NuclearFiveGradeSolovievCommonCompression`: linear maps `e=modelEmbed`,
  `r=modelReadout`, `r(e v)=v`, idempotent `P=e*r`, and the explicit theorem
  `P (fullHamiltonian Eqp omega V (P (e ![C,D]))) =
  e (qpnmMatrix Eqp omega V *ᵥ ![C,D])`.
* `NuclearConfigurationMixing`: real matrix spectral construction, coherent
  amplitudes, strength sum rule, conditional intruder inference, nonidentifiability.
* `NuclearDecayInference`: conditional inference from E2-corrected rates.

Source searches covered embedding/readout/grading, matrix and operator lift,
five-grade transport, recent nuclear PRs, direct consumers, and a bounded
`context_preflight.py` packet. The algebra-equivalence transport owner is not
applicable to this proper corner inclusion. Graph/index artifacts remain absent.

## Exact lift and dependency order

1. The split embedding `r*e=1` defines `iota(O)=e*O*r` using native matrix
   linear maps and the existing common carrier.
2. `iota` is injective, linear and multiplicative. It induces a native Lie
   homomorphism. It sends `1` to `P`, not to the full carrier's identity.
3. Matrix readout `T ↦ r*T*e` is a left inverse of `iota`; consequently the
   original finite transition readouts and inference theorems apply exactly.
4. `G*e=0` and `r*G=0` imply all lifted operators have grade zero, and the
   readout of every nonzero-grade homogeneous operator vanishes.
5. Extend an invertible finite basis change by the identity off the corner:
   `U(O)=1-P+iota(O)`. It is multiplicative and preserves the full identity.
   The normalized mixing rotation therefore gives inverse full operators.
   Their conjugation preserves every existing adjoint grade.
6. The existing QPNM compression becomes the full operator identity
   `P*H*P=iota(H_QPNM)`.
7. Compute an explicit full-Hamiltonian leakage outside the selected corner;
   finite eigenvectors cannot be promoted automatically to full eigenvectors.

## Interpretation limits

The selected two states have the same fermion occupation grade, and differ in
phonon occupation zero/one. Their identification with normal/intruder nuclear
configurations is additional physical modelling, not a theorem of the lift.
The fermionic five-grade index is not angular momentum or spatial parity.

`P` selects only two scalar-Zorn coordinates. It is not the entire grade-zero
subspace, and has not been shown orthogonal: this algebraic countable-product
carrier has no supplied Hilbert inner product or completion. Readout amplitudes
are finite-coordinate matrix elements. No full-space Born rule is asserted.

The lift preserves multiplication; compression of arbitrary full operators
need not preserve it. A completed basis rotation is an algebraic invertible
operator, not a proved unitary operator on an unspecified Hilbert space.
A finite scalar operator lifts to a scalar multiple of `P`, not of the full
identity. It is central within the lifted matrix algebra, but need not commute
with arbitrary full-carrier operators. Earlier scalar-defect invisibility
therefore does not automatically extend to every five-grade observable.
All experimental and rate-law assumptions in PR #220 remain explicit.

## Validation

`[kernel_verified]` for the 29 new theorem statements; physical interpretation
is `[accepted_limited_scope]` under the boundaries above.

* Lean 4.34.1; exact pinned mathlib
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
* An isolated Lake project imports the actual repository source with that
  pinned mathlib. Sequential, shared-lock command:
  `flock /tmp/info-geometry-build.lock lake build InfoGeometry.Physics.NuclearConfigurationGradedReadout`.
  It completed successfully (8949 jobs), including both new modules.
* `lake env lean` on an import plus `#print axioms` for all 33 new declarations
  (29 theorems, four definitions including the native Lie homomorphism) passed.
  Every footprint contains only `propext`, `Classical.choice`, `Quot.sound`.
* `python3 tools/quality/proof_proxy_staged_gate.py`, placeholder scan, and
  `git diff --cached --check` pass.
* `python3 tools/quality/semantic_vacuity_gate.py` on the two new modules
  exits successfully with seven `trivial_surface` warnings. These concern
  definitional application/readout helpers and simplifications using proved
  linear-map/grading laws; they do not replace a theorem by its hypothesis.
  The separate semantic/acceptance reviews inspect these short proofs.
* No warnings originate in the new modules. Existing imported-owner lint and
  deprecated-import warnings remain.
* The prescribed repository-root locked build was attempted during the base
  mixing work and stops before target compilation because
  `external_refs/atlas-lean` is absent. No dependency pins were changed.
  This targeted check does not certify the whole repository build.

Checked source SHA-256:

* `NuclearConfigurationOperatorLift.lean`:
  `5e10c46507097b495255c37e90e4efa3763935c0eafad1cdbb712aea332d0059`.
* `NuclearConfigurationGradedReadout.lean`:
  `8a410343410fdc5f1c1ec6a8308334bdc67601d681276e99f34fe465c99a6f4b`.
