# Peirce surprisal synthesis: theorem contract

Base revision: `3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`.
Intake: the user-uploaded `Pasted text.txt`, 6 November 2026.
Intake SHA-256: `3018adde0723d999c44e19dbc80217322ae449cb72178233c8cdc62bb6c11cc0`.
The original attachment is evidence to analyze, not proof authority.

## 1. Carrier, assumptions, and preserved structure

The algebraic carrier is an arbitrary associative ring, equipped with a real
algebra structure where real scaling is needed. The binary cut is an
idempotent `P`, with complementary idempotent `1 - P`. The analytic
functional calculus uses a unital complex C*-algebra and a star projection.
Trace, resolvent integration, and native differential results use the full
finite complex matrix algebra `Matrix ι ι ℂ`, for any finite index type.
The matrix norm is the native `Matrix.Norms.L2Operator` norm.

No ambient commutativity or simultaneous diagonalization of the arbitrary
matrix inputs is assumed. The two transition operators are
`U = P * A * (1 - P)` and `D = (1 - P) * C * P`. The existing owners define
`Φ = U + D`, `J = U - D`, `V = U * D + D * U`, and
`Σ = U * D - D * U`. Products retain their order before any trace readout.

The mathematical interpretation preserves distinction, directed transition,
ordered round trips, and failure of idempotency. The psychological and
physical names in the intake do not become new mathematical assumptions.
Standard ring, star, norm, spectral-calculus, integration, and differential
structures supply the hypotheses; no new axiom is declared.

## 2. Existing canonical owners

Paths below are relative to `lean/InfoGeometry/`.

| Requested structure | Existing owner and exact declaration surface |
| --- | --- |
| Binary cut and fourfold anatomy | `Core/PeirceDecomposition.lean`: `complementIdempotent_sq`, `idempotent_mul_complement`, `complement_mul_idempotent`, the four `component` maps, `peirce_decomposition`, and the full ordered sector multiplication table. |
| Directed corners and the quartet | `OperatorAlgebra/PeirceSpine/Basic.lean`: `conePlus`, `coneMinus`, `genPhi`, `genJ`, `genV`, `genSig`; `Tetraktys.lean`: `archetype_A3_nilpotent_cones_and_tetraktys_table`. |
| Inner-derivation spectra | `Tetraktys.lean`: `archetype_A5_klein_hadamard_spectra_and_partition` and the later A10/A11 spectra; these retain operator-valued `V` and `V²`. |
| Exact aporia | `Core/IdempotencyDefect.lean`: `defect x = x*x-x`; `Core/PeirceDefect.lean`: `defect_add_coupled`, `defect_add_idempotent_eq_square_iff`, `tangent_iff_diagonal_corners_zero`. |
| Recursive tower | `Core/DefectIteration.lean`: `commute_iterate_add_idempotent`, `iterate_add_of_mul_eq_zero`, `map_iterate`, `adjoin_iterate_antitone`. |
| Native finite prerequisite poset | `Core/PeirceSourceOrder.lean`: `Stage`, `prerequisites`, its `PartialOrder` instance, `support_octet_independent`, `trace_frame_independent`, `synthesis_covers`, `stage_synthesis_peirce_source_master`. |
| Scalar log-determinant differentiation | `Analysis/ComplexMatrixLogDetCalculus.lean`: `hasFDerivAt_negLogDet`, `logDetDifferential_apply`. |
| Positive trace/CFC-log identification | `Canonical/FiniteBogoliubovFrameDeformationEntropy.lean`: `trace_log_eq_log_norm_det_of_isStrictlyPositive`. |

The new synthesis imports `Core.DefectIteration` and
`Core.PeirceSourceOrder`, making both existing order constructions available
in its checked source closure. The finite prerequisite poset is defined by
inclusion of explicit prerequisite sets; it is not a claimed extraction of
every declaration dependency or a proof of physical causation. Its strict
order is acyclic. Some branches are incomparable, so it is not replaced by
an arbitrary total ranking. The stage called `trace` concerns diagonal
corner projections; the stage called `iteration` concerns double
commutators. Actual polynomial defect recursion is provided separately.

The recursive defect tower is `defect^[n] x`. Its generated subalgebras form
an antitone chain in Mathlib's native `Subalgebra` partial order. Successive
steps need not be distinct. In particular, iteration does not establish
strictly growing complexity, new grades, or convergence to an attractor.
The order organizes prerequisites; each identity is proved from the ring
and idempotent hypotheses and earlier theorems, not from a bare order relation.

## 3. Six substantive additions

1. **`OperatorAlgebra/PeirceSpine/TwoSheetFunctionalCalculus.lean`.**
   Defines `twoSheet P p q = p • P + q • (1-P)` and proves its multiplication,
   commutator, and ordered sandwich laws. `cfc_twoSheet` proves the actual
   Mathlib CFC formula for any scalar function restricted to the finite
   spectrum. `twoSheet_isStrictlyPositive` supplies positivity for positive
   weights. `neg_log_twoSheet` and `neg_log_twoSheet_chiral` identify the
   actual negative CFC logarithm. `volume_log_commutes` proves the volume
   logarithm commutes with its generating deformation.
2. **`OperatorAlgebra/PeirceSpine/TwoSheetModular.lean`.**
   Proves `[K, Φ] = -Δ • J`, where `K = -CFC.log ρ` and
   `Δ = log p - log q`. Positive weights give the exact stopped-action
   criterion `p = q ∨ Φ = 0`. Native `Function.iterate` yields
   `ad_K^[2*n] Φ = Δ^(2*n) • Φ` and
   `ad_K^[2*n+1] Φ = -Δ^(2*n+1) • J` for every natural `n`.
3. **`Analysis/BKMResolventIntegral.lean`.**
   Defines the completed logarithmic divided difference
   `c(p,q) = if p=q then 1/p else (log p-log q)/(p-q)`.
   Proves symmetry, positivity for `p,q>0`, improper integrability, and
   `integral_Ioi_logResolventKernel`:
   `∫ s>0, 1/((p+s)*(q+s)) = c(p,q)`, including the diagonal case.
4. **`OperatorAlgebra/PeirceSpine/TwoSheetBKM.lean`.**
   Uses the genuine matrix inverse `R_s = (ρ+sI)⁻¹`. Proves the ordered
   identity `R_s * Φ * R_s = (1/((p+s)*(q+s))) • Φ`, then its Bochner
   integral. The trace integral allows an arbitrary left matrix input.
   Its quadratic specialization is `c(p,q) * ReTr V`, nonnegative for
   Hermitian `Φ` and strictly positive when `Φ ≠ 0`.
5. **`Analysis/PeirceVolumeCalculus.lean`.**
   Proves the native real Fréchet derivative of
   `L(Φ) = log ‖det (I+βΦ²)‖` wherever the weight is invertible.
   It first retains `β(ΦH+HΦ)`, then uses proved commutation and trace
   cyclicity to obtain `DL(Φ)[H] = 2β ReTr((I+βΦ²)⁻¹ Φ H)`.
   For Hermitian `Φ,H` and `β≥0`, this differentiates the actual
   `ReTr(CFC.log (I+βΦ²))`. `neg_log_volumeWeight_inv` proves the actual
   operator identity `-CFC.log ((I+βΦ²)⁻¹) = CFC.log (I+βΦ²)`.
6. **`OperatorAlgebra/PeirceSpine/TwoSheetSurprisalSynthesis.lean`.**
   Defines the actual real resolvent pairing with a star on its first input:
   `gρ(X,Y) = ∫ s>0, ReTr(star X * R_s * Y * R_s)`.
   `genJ_gram_eq_idempotencyDefect` proves
   `star J * J = defect(P+Φ)` for self-adjoint `Φ` and a star projection `P`.
   The master `modular_bkm_energy_eq_defect_trace` proves
   `gρ([K,Φ],[K,Φ]) = Δ² c(p,q) ReTr(defect(P+Φ))`.
   The equivalent `modular_bkm_energy_eq_log_jump_sq_mul` identifies this
   with `Δ² gρ(Φ,Φ)`. `isotropic_bkm_positive_modular_zero` records positive
   odd energy and zero modular action at equal positive weights.

## 4. Deductive dependencies

The algebraic branch is the existing Peirce cut, ordered corners, quartet,
and exact defect. The analytic branch adds the proved finite-spectrum CFC
formula and the scalar resolvent integral. They meet through the ordered
matrix resolvent theorem. The energy-defect synthesis then uses all of:

- the actual sheet-log commutator theorem;
- the actual convergent trace-resolvent integral;
- the current Gram identity, derived from `star J = -J`, `J² = -V`, and
  `defect(P+Φ) = V`.

The volume-log calculus is a separate branch through native matrix
log-determinant differentiation and positive trace/CFC-log identification.
It is not used as a premise for a nonzero sheet modular commutator. The
source-closure manifest records the exact import order and SHA-256 of every
selected repository source; compilation rejects import cycles.

## 5. Corrected claims and explicit boundaries

- `CFC.log (I+βΦ²)` commutes with `Φ`. Thus it cannot itself provide the
  manuscript's asserted nonzero commutator on `Φ`. The sheet logarithm is a
  different operator.
- `-[Φ,[Φ,J]] = -2[Σ,Φ] = -4VJ` compares values on the indicated elements.
  It is not an equality of the corresponding superoperators on every input.
- The full derivative of the square is `ΦH+HΦ`. The displayed resolvent
  expression is a scalar trace differential. On the Hermitian branch its
  Hilbert--Schmidt gradient is `2β(I+βΦ²)⁻¹Φ`; on the full real vector space
  of complex matrices the gradient is the adjoint of that matrix. No
  unrestricted operator-log derivative formula is asserted.
- The BKM result is a convergent resolvent pairing and its odd-sector
  evaluation. Identifying it with `fderiv CFC.log` or an Umegaki
  relative-entropy Hessian remains outside these proofs.
- The forward logarithmic mean and its inverse are distinct. Existing
  forward Kubo--Mori pairings are not silently substituted for `c(p,q)`.
- `c(p,p)=1/p`, not the total quotient `0/0`. Equal weights stop modular
  action but do not erase positive BKM geometry.
- `ad_K² Φ = Δ² Φ` alone is not a unitary oscillator theorem. The unitary
  generator includes a factor `i`, which changes the sign of its square.
- Positivity and trace-one normalization are separate. The BKM algebraic
  identities only need an idempotent; a positive density interpretation
  needs a star projection and normalization. `I/2` has ordinary trace one
  only in dimension two. The volume inverse is not normalized by definition.
- Mathlib's `CFC.log` is total, and `Real.log` follows its native real
  convention away from the positive cone. General total-CFC commutation and
  two-point identities are not claims that every argument is a positive
  state. Positive weights and positive volume weights supply that intended
  interpretation where needed.
- The exact Kantor sandwich already occurs as the final conjunct of
  `archetype_CL8_higher_grade_uncertainty_anomaly_in_symmetry_closure` in
  `OperatorAlgebra/PeirceSpine/ChiralLorentzTwistorCartanUncertaintyPoset.lean`.
  Its five operators are separately defined ordered maps; the sandwich is
  not inferred merely from Peirce corner names. This existing owner is
  source-reviewed, not newly compiled in the selected closure here.
- That owner's CL9 theorem reuses the normalized-Hilbert-state
  `cramerRao_metriplectic_full_bound`. The existing QGT/Fubini--Study/Berry
  inequality is not identified by this work with the new BKM pairing.
- Associative operator identities do not prove a nonassociative Zorn
  extension, a nonzero ordinary self-cross-product, a continuum mass gap,
  emergence of physical time, or a psychological model.

## 6. Validation scope and reproduction

The pinned environment is Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No dependency pin, root build
configuration, verification tool, or existing theorem owner is modified.

The maintained exact-closure route is:

```bash
python3 tools/quality/check_operator_geometry.py --repo . \
  --mathlib /path/to/the/pinned/mathlib \
  --work-dir /path/to/a/fresh/verification/directory \
  --target InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetSurprisalSynthesis \
  --target InfoGeometry.Analysis.PeirceVolumeCalculus
```

The checker uses the shared repository build lock, verifies the compiler and
dependency pins, compiles unchanged source snapshots, and compares live
source hashes at completion. It checks the selected source closure, not the
entire repository. Declaration auditing uses the repository's
`tools/quality/reviewed_audit_source.py` and native `Lean.collectAxioms` for
all declarations of the selected new owners and the reused core order
owners, including private declarations. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed; unsafe and partial declarations are rejected.

Independent A-A source review and separate QA-A reruns are recorded with
source hashes in the delivered verification evidence. Automated OpenGauss,
semantic/vacuity, and staged proof checks are separate from kernel checks.
Static Gate 4 output alone is not a kernel certificate.

The standard locked root Lake build was attempted and stopped before
checking these targets because the path dependency
`external_refs/homotopy-hypothesis-lean4` is missing. `external_refs/atlas-lean`
is another required path without a tracked checkout in this clone. These
paths have no repository-pinned submodule entries to restore here. The
unrelated dependency configuration is preserved. This work therefore makes
no successful root-package build, pre-push, publication, or whole-repository
verification claim.
