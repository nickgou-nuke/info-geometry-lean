import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.BregmanDeformation

open Matrix
open Complex
open Real

noncomputable section

/-!
# Bregman Analytic Bound

The thermodynamic cost term

`exp (ε • K) - I - ε • K`

is the matrix-exponential remainder used in the Bregman/IPM reading of the
finite-dimensional modular-Hamiltonian flow.  Here `K` is an operator in the
noncommutative matrix algebra `Mₙ(ℂ)`; when packaged as
`MatrixModularHamiltonian`, it carries the self-adjoint law `K* = K`.

The closed-form `phaseAxis` rotation corridor later in the file is separate:
that lane uses the skew complex-structure generator with square `-I`, not the
self-adjoint modular Hamiltonian.  This file does not prove the analytic matrix
remainder estimate. Instead, it names that estimate as an explicit hypothesis
and proves the kernel-checkable consequences used by the Cantor-boundary lane.

#### BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully
checked by the kernel.]

* `exponentialRemainder_zero`
* `exponentialRemainder_zero_norm`
* `modularStep_isSelfAdjoint`
* `modularExponential_isSelfAdjoint`
* `exponentialRemainder_isSelfAdjoint`
* `MatrixModularHamiltonian.exponentialRemainder_eq`
* `cos_remainder_abs_le_sq`
* `sin_remainder_abs_le_sq`
* `scalar_rotation_remainder_abs_sum_le_sq`
* `closedFormPhaseAxisRemainder_entry_bound`
* `closedFormPhaseAxisRemainder_entryMax_bound`
* `dikinOmega_zero`
* `dikinOmegaStar_zero`
* `dikinOmega_nonneg_of_nonneg`
* `dikinOmegaStar_nonneg_of_lt_one`
* `matrix_bregman_nonneg_of_dikin_envelope`
* `matrix_dikin_sandwich_of_selfConcordant_envelope`
* `matrix_bregman_zero_of_dikin_envelope_radius_zero`
* `phase_axis_norm_bound_of_closed_exp`
* `phase_axis_deformation_bounded_of_quadratic_bound`
* `dikin_bound_of_phase_axis_norm`
* `matrix_bregman_size_le_dikin_radius_sq_of_quadratic_bound`
* `bregman_bound_clears_at_flat_boundary`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* `phase_axis_deformation_bounded_of_quadratic_bound`
* `dikin_bound_of_phase_axis_norm`
* `phase_axis_norm_bound_of_closed_exp`

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields,
witnesses, certificates, or renamed placeholders.]

* Prove the matrix-exponential quadratic remainder estimate from Taylor
  expansion and a concrete operator norm:
  `HasQuadraticBregmanBound K`.
* Identify the closed-form `modularDelta ε` entrywise estimate with the
  `NormedSpace.exp (ε • phaseAxis)` estimate once the matrix-exponential
  closed form is proved.
* Prove the closed-form exponential identity
  `exp (ε • K) = cos ε • 1 + sin ε • K` from `K ^ 2 = -1`.
* Prove `‖K‖ = 1` for the concrete phase-axis matrix from its chosen C*-norm,
  not merely from the algebraic relation `K ^ 2 = -1`.
* Build the full `ℓ²(BinaryCantorBoundary) ⊗ DoubledSpace ℝ` completion and
  derive uniform continuity of the diagonal Cuntz shift from boundedness of
  the base shift and the fiber phase axis.
-/

open scoped BigOperators Matrix Norms.Operator

set_option autoImplicit false

namespace BregmanAnalyticBound

abbrev MatrixEnd (n : ℕ) :=
  Matrix (Fin n) (Fin n) ℂ

/-! ## Matrix Dikin envelope for self-concordant Bregman divergences -/

/--
The lower Nesterov--Nemirovski Dikin envelope
`ω(t) = t - log (1 + t)`.
-/
noncomputable def dikinOmega (t : ℝ) : ℝ :=
  t - Real.log (1 + t)

/--
The upper Nesterov--Nemirovski Dikin envelope
`ω*(t) = -t - log (1 - t)`, used for local radii `t < 1`.
-/
noncomputable def dikinOmegaStar (t : ℝ) : ℝ :=
  -t - Real.log (1 - t)

@[simp]
theorem dikinOmega_zero :
    dikinOmega 0 = 0 := by
  simp [dikinOmega]

@[simp]
theorem dikinOmegaStar_zero :
    dikinOmegaStar 0 = 0 := by
  simp [dikinOmegaStar]

/-- `ω(t)` is nonnegative on nonnegative local radii. -/
theorem dikinOmega_nonneg_of_nonneg {t : ℝ}
    (ht : 0 ≤ t) :
    0 ≤ dikinOmega t := by
  have hpos : 0 < 1 + t := by linarith
  have hlog : Real.log (1 + t) ≤ (1 + t) - 1 :=
    Real.log_le_sub_one_of_pos hpos
  unfold dikinOmega
  linarith

/-- `ω*(t)` is nonnegative on its natural domain `t < 1`. -/
theorem dikinOmegaStar_nonneg_of_lt_one {t : ℝ}
    (ht : t < 1) :
    0 ≤ dikinOmegaStar t := by
  have hpos : 0 < 1 - t := by linarith
  have hlog : Real.log (1 - t) ≤ (1 - t) - 1 :=
    Real.log_le_sub_one_of_pos hpos
  unfold dikinOmegaStar
  linarith

/--
Self-concordant Dikin sandwich for a matrix Bregman divergence `D` measured in
a local Hessian radius `localRadius`.

This is the repo's conservative bridge for self-concordant barriers: the
analytic self-concordance proof supplies these three fields, and downstream
matrix/IPM files consume only the resulting bounds.
-/
structure HasMatrixSelfConcordantDikinEnvelope {n : ℕ}
    (D : MatrixEnd n → MatrixEnd n → ℝ)
    (localRadius : MatrixEnd n → MatrixEnd n → ℝ) : Prop where
  radius_nonneg : ∀ x y, 0 ≤ localRadius x y
  lower : ∀ x y, dikinOmega (localRadius x y) ≤ D x y
  upper : ∀ x y, localRadius x y < 1 →
    D x y ≤ dikinOmegaStar (localRadius x y)

/--
A self-concordant Dikin envelope implies nonnegativity of the underlying
matrix Bregman divergence.
-/
theorem matrix_bregman_nonneg_of_dikin_envelope {n : ℕ}
    {D : MatrixEnd n → MatrixEnd n → ℝ}
    {localRadius : MatrixEnd n → MatrixEnd n → ℝ}
    (hsc : HasMatrixSelfConcordantDikinEnvelope D localRadius)
    (x y : MatrixEnd n) :
    0 ≤ D x y := by
  exact (dikinOmega_nonneg_of_nonneg (hsc.radius_nonneg x y)).trans
    (hsc.lower x y)

/--
The canonical self-concordant local sandwich:
`ω(r) ≤ D(x,y) ≤ ω*(r)` for Dikin radius `r < 1`.
-/
theorem matrix_dikin_sandwich_of_selfConcordant_envelope {n : ℕ}
    {D : MatrixEnd n → MatrixEnd n → ℝ}
    {localRadius : MatrixEnd n → MatrixEnd n → ℝ}
    (hsc : HasMatrixSelfConcordantDikinEnvelope D localRadius)
    (x y : MatrixEnd n)
    (hsmall : localRadius x y < 1) :
    dikinOmega (localRadius x y) ≤ D x y ∧
      D x y ≤ dikinOmegaStar (localRadius x y) :=
  ⟨hsc.lower x y, hsc.upper x y hsmall⟩

/--
If the Dikin radius vanishes on the diagonal, the Dikin sandwich forces the
matrix Bregman divergence to vanish there.
-/
theorem matrix_bregman_zero_of_dikin_envelope_radius_zero {n : ℕ}
    {D : MatrixEnd n → MatrixEnd n → ℝ}
    {localRadius : MatrixEnd n → MatrixEnd n → ℝ}
    (hsc : HasMatrixSelfConcordantDikinEnvelope D localRadius)
    (x : MatrixEnd n)
    (hradius : localRadius x x = 0) :
    D x x = 0 := by
  have hsmall : localRadius x x < 1 := by
    simp [hradius]
  have hupper := hsc.upper x x hsmall
  have hle : D x x ≤ 0 := by
    simp [hradius] at hupper
    exact hupper
  have hge : 0 ≤ D x x :=
    matrix_bregman_nonneg_of_dikin_envelope hsc x x
  exact le_antisymm hle hge

/-! ## Operator-valued modular Hamiltonian remainder -/

/--
Finite-dimensional modular Hamiltonian in the noncommutative matrix algebra
`Mₙ(ℂ)`.

The field `K` is an operator.  The law `selfAdjoint` records the Tomita/KMS
Hamiltonian condition `K* = K`; no scalar proxy is used.
-/
structure MatrixModularHamiltonian (n : ℕ) where
  K : MatrixEnd n
  selfAdjoint : IsSelfAdjoint K

/--
The Bregman/IPM exponential remainder
`exp (ε • K) - I - ε • K` in the noncommutative matrix algebra `Mₙ(ℂ)`.
-/
noncomputable def exponentialRemainder {n : ℕ}
    (K : MatrixEnd n) (ε : ℝ) : MatrixEnd n :=
  (NormedSpace.exp (ε • K) : MatrixEnd n) - 1 - (ε • K : MatrixEnd n)

/-- A real modular step preserves self-adjointness of the Hamiltonian operator. -/
theorem modularStep_isSelfAdjoint {n : ℕ}
    {K : MatrixEnd n}
    (hK : IsSelfAdjoint K)
    (ε : ℝ) :
    IsSelfAdjoint (ε • K : MatrixEnd n) := by
  rw [isSelfAdjoint_iff, star_smul, hK.star_eq]
  simp

/-- The matrix exponential of a self-adjoint modular step is self-adjoint. -/
theorem modularExponential_isSelfAdjoint {n : ℕ}
    {K : MatrixEnd n}
    (hK : IsSelfAdjoint K)
    (ε : ℝ) :
    IsSelfAdjoint ((NormedSpace.exp (ε • K) : MatrixEnd n)) := by
  simpa using (modularStep_isSelfAdjoint (K := K) hK ε).exp

/--
For a self-adjoint modular Hamiltonian `K`, the operator Bregman remainder
`exp (ε • K) - I - ε • K` is again self-adjoint.
-/
theorem exponentialRemainder_isSelfAdjoint {n : ℕ}
    {K : MatrixEnd n}
    (hK : IsSelfAdjoint K)
    (ε : ℝ) :
    IsSelfAdjoint (exponentialRemainder K ε) := by
  have hExp : IsSelfAdjoint ((NormedSpace.exp (ε • K) : MatrixEnd n)) :=
    modularExponential_isSelfAdjoint (K := K) hK ε
  have hOne : IsSelfAdjoint (1 : MatrixEnd n) :=
    IsSelfAdjoint.one (MatrixEnd n)
  have hStep : IsSelfAdjoint (ε • K : MatrixEnd n) :=
    modularStep_isSelfAdjoint (K := K) hK ε
  exact (hExp.sub hOne).sub hStep

namespace MatrixModularHamiltonian

/-- Operator-valued modular Bregman remainder attached to a Hamiltonian packet. -/
noncomputable def exponentialRemainder {n : ℕ}
    (H : MatrixModularHamiltonian n) (ε : ℝ) : MatrixEnd n :=
  InfoGeometry.Analysis.BregmanAnalyticBound.exponentialRemainder H.K ε

/-- The packet readout is the same noncommutative matrix expression. -/
theorem exponentialRemainder_eq {n : ℕ}
    (H : MatrixModularHamiltonian n) (ε : ℝ) :
    H.exponentialRemainder ε =
      (NormedSpace.exp (ε • H.K) : MatrixEnd n) - 1 - (ε • H.K : MatrixEnd n) :=
  rfl

/-- The operator-valued packet remainder is self-adjoint. -/
theorem exponentialRemainder_isSelfAdjoint {n : ℕ}
    (H : MatrixModularHamiltonian n) (ε : ℝ) :
    IsSelfAdjoint (H.exponentialRemainder ε) :=
  InfoGeometry.Analysis.BregmanAnalyticBound.exponentialRemainder_isSelfAdjoint
    H.selfAdjoint ε

end MatrixModularHamiltonian

@[simp]
theorem exponentialRemainder_zero {n : ℕ} (K : MatrixEnd n) :
    exponentialRemainder K 0 = 0 := by
  simp [exponentialRemainder]

@[simp]
theorem exponentialRemainder_zero_norm {n : ℕ} (K : MatrixEnd n) :
    ‖exponentialRemainder K 0‖ = 0 := by
  rw [exponentialRemainder_zero K]
  exact norm_zero

/-! ## Scalar Taylor corridor for the closed-form rotation model -/

/--
For `|ε| ≤ 1`, the cosine component of the closed-form phase-axis rotation has
quadratic Bregman size.

This is the scalar Taylor corridor behind the diagonal entries of
`[[cos ε, -sin ε], [sin ε, cos ε]] - I - εK`.
-/
theorem cos_remainder_abs_le_sq {ε : ℝ} (hε : |ε| ≤ 1) :
    |Real.cos ε - 1| ≤ ε ^ 2 := by
  have hcb := Real.cos_bound hε
  have htri :
      |Real.cos ε - 1| ≤
        |Real.cos ε - (1 - ε ^ 2 / 2)| + |(1 - ε ^ 2 / 2) - 1| :=
    abs_sub_le (Real.cos ε) (1 - ε ^ 2 / 2) 1
  have hsimp : |(1 - ε ^ 2 / 2) - 1| = ε ^ 2 / 2 := by
    have hnon : 0 ≤ ε ^ 2 / 2 := div_nonneg (sq_nonneg ε) (by norm_num)
    have hform : (1 - ε ^ 2 / 2) - 1 = -(ε ^ 2 / 2) := by ring
    rw [hform, abs_neg, abs_of_nonneg hnon]
  have hsqabs : |ε| ^ 2 = ε ^ 2 := by rw [sq_abs]
  have hpow4 : |ε| ^ 4 ≤ ε ^ 2 := by
    rw [← hsqabs]
    exact pow_le_pow_of_le_one (abs_nonneg ε) hε (by norm_num)
  calc
    |Real.cos ε - 1|
        ≤ |Real.cos ε - (1 - ε ^ 2 / 2)| + |(1 - ε ^ 2 / 2) - 1| := htri
    _ = |Real.cos ε - (1 - ε ^ 2 / 2)| + ε ^ 2 / 2 := by rw [hsimp]
    _ ≤ |ε| ^ 4 * (5 / 96) + ε ^ 2 / 2 := by gcongr
    _ ≤ ε ^ 2 * (5 / 96) + ε ^ 2 / 2 := by gcongr
    _ ≤ ε ^ 2 := by nlinarith [sq_nonneg ε]

/--
For `|ε| ≤ 1`, the sine component of the closed-form phase-axis rotation has
quadratic Bregman size after subtracting its linear term.

This controls the off-diagonal entries of
`[[cos ε, -sin ε], [sin ε, cos ε]] - I - εK`.
-/
theorem sin_remainder_abs_le_sq {ε : ℝ} (hε : |ε| ≤ 1) :
    |Real.sin ε - ε| ≤ ε ^ 2 := by
  have hsb := Real.sin_bound hε
  have htri :
      |Real.sin ε - ε| ≤
        |Real.sin ε - (ε - ε ^ 3 / 6)| + |(ε - ε ^ 3 / 6) - ε| :=
    abs_sub_le (Real.sin ε) (ε - ε ^ 3 / 6) ε
  have hsimp : |(ε - ε ^ 3 / 6) - ε| = |ε| ^ 3 / 6 := by
    have h6 : (0 : ℝ) ≤ 6 := by norm_num
    have hnon6 : |(6 : ℝ)| = 6 := abs_of_nonneg h6
    have hform : (ε - ε ^ 3 / 6) - ε = -(ε ^ 3 / 6) := by ring
    rw [hform, abs_neg, abs_div, abs_pow, hnon6]
  have hsqabs : |ε| ^ 2 = ε ^ 2 := by rw [sq_abs]
  have hpow3 : |ε| ^ 3 ≤ ε ^ 2 := by
    rw [← hsqabs]
    exact pow_le_pow_of_le_one (abs_nonneg ε) hε (by norm_num)
  have hpow4 : |ε| ^ 4 ≤ ε ^ 2 := by
    rw [← hsqabs]
    exact pow_le_pow_of_le_one (abs_nonneg ε) hε (by norm_num)
  calc
    |Real.sin ε - ε|
        ≤ |Real.sin ε - (ε - ε ^ 3 / 6)| + |(ε - ε ^ 3 / 6) - ε| := htri
    _ = |Real.sin ε - (ε - ε ^ 3 / 6)| + |ε| ^ 3 / 6 := by rw [hsimp]
    _ ≤ |ε| ^ 4 * (5 / 96) + |ε| ^ 3 / 6 := by gcongr
    _ ≤ ε ^ 2 * (5 / 96) + ε ^ 2 / 6 := by gcongr
    _ ≤ ε ^ 2 := by nlinarith [sq_nonneg ε]

/--
For `|ε| ≤ 1`, the scalar closed-form rotation remainder has total size at
most `ε²`.

This is the Taylor/norm corridor needed for the operator estimate:
`|(cos ε - 1)| + |(sin ε - ε)| ≤ ε²`.
-/
theorem scalar_rotation_remainder_abs_sum_le_sq {ε : ℝ} (hε : |ε| ≤ 1) :
    |Real.cos ε - 1| + |Real.sin ε - ε| ≤ ε ^ 2 := by
  have hcb := Real.cos_bound hε
  have hsb := Real.sin_bound hε
  have hcos_tri :
      |Real.cos ε - 1| ≤
        |Real.cos ε - (1 - ε ^ 2 / 2)| + |(1 - ε ^ 2 / 2) - 1| :=
    abs_sub_le (Real.cos ε) (1 - ε ^ 2 / 2) 1
  have hcos_tail : |(1 - ε ^ 2 / 2) - 1| = ε ^ 2 / 2 := by
    have hnon : 0 ≤ ε ^ 2 / 2 := div_nonneg (sq_nonneg ε) (by norm_num)
    have hform : (1 - ε ^ 2 / 2) - 1 = -(ε ^ 2 / 2) := by ring
    rw [hform, abs_neg, abs_of_nonneg hnon]
  have hsin_tri :
      |Real.sin ε - ε| ≤
        |Real.sin ε - (ε - ε ^ 3 / 6)| + |(ε - ε ^ 3 / 6) - ε| :=
    abs_sub_le (Real.sin ε) (ε - ε ^ 3 / 6) ε
  have hsin_tail : |(ε - ε ^ 3 / 6) - ε| = |ε| ^ 3 / 6 := by
    have h6 : (0 : ℝ) ≤ 6 := by norm_num
    have hnon6 : |(6 : ℝ)| = 6 := abs_of_nonneg h6
    have hform : (ε - ε ^ 3 / 6) - ε = -(ε ^ 3 / 6) := by ring
    rw [hform, abs_neg, abs_div, abs_pow, hnon6]
  have hsqabs : |ε| ^ 2 = ε ^ 2 := by rw [sq_abs]
  have hpow3 : |ε| ^ 3 ≤ ε ^ 2 := by
    rw [← hsqabs]
    exact pow_le_pow_of_le_one (abs_nonneg ε) hε (by norm_num)
  have hpow4 : |ε| ^ 4 ≤ ε ^ 2 := by
    rw [← hsqabs]
    exact pow_le_pow_of_le_one (abs_nonneg ε) hε (by norm_num)
  calc
    |Real.cos ε - 1| + |Real.sin ε - ε|
        ≤ (|Real.cos ε - (1 - ε ^ 2 / 2)| + |(1 - ε ^ 2 / 2) - 1|) +
          (|Real.sin ε - (ε - ε ^ 3 / 6)| + |(ε - ε ^ 3 / 6) - ε|) := by
            exact add_le_add hcos_tri hsin_tri
    _ = |Real.cos ε - (1 - ε ^ 2 / 2)| + ε ^ 2 / 2 +
          (|Real.sin ε - (ε - ε ^ 3 / 6)| + |ε| ^ 3 / 6) := by
            rw [hcos_tail, hsin_tail]
    _ ≤ |ε| ^ 4 * (5 / 96) + ε ^ 2 / 2 +
          (|ε| ^ 4 * (5 / 96) + |ε| ^ 3 / 6) := by gcongr
    _ ≤ ε ^ 2 * (5 / 96) + ε ^ 2 / 2 +
          (ε ^ 2 * (5 / 96) + ε ^ 2 / 6) := by gcongr
    _ ≤ ε ^ 2 := by nlinarith [sq_nonneg ε]

/-! ## Closed-form finite phase-axis bound -/

/--
The closed-form 2×2 modular rotation remainder
`Δ(ε) - I - εK`, using the explicit `modularDelta` and `phaseAxis`.

This is intentionally separate from `exponentialRemainder`: the remaining
analytic task is to prove that `modularDelta ε = exp (ε • phaseAxis)`.
-/
noncomputable def closedFormPhaseAxisRemainder (ε : ℝ) : MatrixEnd 2 :=
  InfoGeometry.Canonical.BregmanDeformation.modularDelta ε
    - (1 : MatrixEnd 2)
    - (ε • InfoGeometry.Canonical.BregmanDeformation.phaseAxis : MatrixEnd 2)

/--
Entrywise max norm for 2×2 matrices.

This lightweight finite norm records exactly what the closed-form Taylor
corridor proves without claiming an operator-norm estimate.
-/
def entryMaxNorm2 (A : MatrixEnd 2) : ℝ :=
  max (max ‖A 0 0‖ ‖A 0 1‖) (max ‖A 1 0‖ ‖A 1 1‖)

/--
Every entry of the explicit phase-axis modular remainder is quadratically
bounded for `|ε| ≤ 1`.
-/
theorem closedFormPhaseAxisRemainder_entry_bound {ε : ℝ}
    (hε : |ε| ≤ 1) (i j : Fin 2) :
    ‖closedFormPhaseAxisRemainder ε i j‖ ≤ ε ^ 2 := by
  have hcos := cos_remainder_abs_le_sq (ε := ε) hε
  have hsin := sin_remainder_abs_le_sq (ε := ε) hε
  have hcosC : ‖Complex.cos (ε : ℂ) - 1‖ ≤ ε ^ 2 := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact hcos
  have hsinC : ‖Complex.sin (ε : ℂ) - (ε : ℂ)‖ ≤ ε ^ 2 := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact hsin
  have hsinC_neg : ‖(ε : ℂ) - Complex.sin (ε : ℂ)‖ ≤ ε ^ 2 := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    simpa [abs_sub_comm] using hsin
  fin_cases i <;> fin_cases j
  · simpa [closedFormPhaseAxisRemainder,
      InfoGeometry.Canonical.BregmanDeformation.modularDelta,
      InfoGeometry.Canonical.BregmanDeformation.phaseAxis] using hcosC
  · simpa [closedFormPhaseAxisRemainder,
      InfoGeometry.Canonical.BregmanDeformation.modularDelta,
      InfoGeometry.Canonical.BregmanDeformation.phaseAxis,
      abs_sub_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsinC_neg
  · simpa [closedFormPhaseAxisRemainder,
      InfoGeometry.Canonical.BregmanDeformation.modularDelta,
      InfoGeometry.Canonical.BregmanDeformation.phaseAxis] using hsinC
  · simpa [closedFormPhaseAxisRemainder,
      InfoGeometry.Canonical.BregmanDeformation.modularDelta,
      InfoGeometry.Canonical.BregmanDeformation.phaseAxis] using hcosC

/--
The explicit 2×2 phase-axis remainder has entrywise quadratic Bregman size.
-/
theorem closedFormPhaseAxisRemainder_entryMax_bound {ε : ℝ}
    (hε : |ε| ≤ 1) :
    entryMaxNorm2 (closedFormPhaseAxisRemainder ε) ≤ ε ^ 2 := by
  dsimp [entryMaxNorm2]
  exact max_le
    (max_le
      (closedFormPhaseAxisRemainder_entry_bound hε 0 0)
      (closedFormPhaseAxisRemainder_entry_bound hε 0 1))
    (max_le
      (closedFormPhaseAxisRemainder_entry_bound hε 1 0)
      (closedFormPhaseAxisRemainder_entry_bound hε 1 1))

/-! ## Conditional quadratic Bregman bound -/

/--
Closed-form phase-axis rotations have the desired local quadratic
operator-norm Bregman bound once the finite exponential identity and concrete
norm facts are supplied.

The missing analytic bridge is explicit in `hExp`: for a phase axis satisfying
`K ^ 2 = -1`, prove
`exp (ε • K) = cos ε • 1 + sin ε • K`. This theorem then converts that
identity into the honest norm estimate; it does not use a Loewner/PSD claim.
-/
theorem phase_axis_norm_bound_of_closed_exp {n : ℕ}
    (K : MatrixEnd n)
    (hI_norm : ‖(1 : MatrixEnd n)‖ ≤ 1)
    (hK_norm : ‖K‖ = 1)
    (ε : ℝ)
    (hε : |ε| ≤ 1)
    (hExp :
      (NormedSpace.exp (ε • K) : MatrixEnd n) =
        (Real.cos ε : ℂ) • (1 : MatrixEnd n) + (Real.sin ε : ℂ) • K) :
    ‖exponentialRemainder K ε‖ ≤ ε ^ 2 := by
  have hscalar := scalar_rotation_remainder_abs_sum_le_sq (ε := ε) hε
  have hcosnorm : ‖((Real.cos ε : ℂ) - 1)‖ = |Real.cos ε - 1| := by
    norm_cast
  have hsinnorm : ‖((Real.sin ε : ℂ) - (ε : ℂ))‖ = |Real.sin ε - ε| := by
    norm_cast
  have hrewrite :
      exponentialRemainder K ε =
        ((Real.cos ε - 1 : ℝ) : ℂ) • (1 : MatrixEnd n) +
          ((Real.sin ε - ε : ℝ) : ℂ) • K := by
    rw [exponentialRemainder, hExp]
    ext i j
    simp
    ring
  rw [hrewrite]
  calc
    ‖((Real.cos ε - 1 : ℝ) : ℂ) • (1 : MatrixEnd n) +
        ((Real.sin ε - ε : ℝ) : ℂ) • K‖
        ≤ ‖((Real.cos ε - 1 : ℝ) : ℂ) • (1 : MatrixEnd n)‖ +
          ‖((Real.sin ε - ε : ℝ) : ℂ) • K‖ := norm_add_le _ _
    _ = |Real.cos ε - 1| * ‖(1 : MatrixEnd n)‖ + |Real.sin ε - ε| * ‖K‖ := by
      rw [norm_smul, norm_smul]
      simpa [Complex.ofReal_sub] using
        congrArg₂ HAdd.hAdd
          (congrArg (fun x => x * ‖(1 : MatrixEnd n)‖) hcosnorm)
          (congrArg (fun x => x * ‖K‖) hsinnorm)
    _ ≤ |Real.cos ε - 1| * 1 + |Real.sin ε - ε| * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hI_norm (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (le_of_eq hK_norm) (abs_nonneg _))
    _ = |Real.cos ε - 1| + |Real.sin ε - ε| := by ring
    _ ≤ ε ^ 2 := hscalar

/--
Explicit local quadratic remainder estimate.

This is a proposition, not a global postulate. The analytic closure target is
to prove this predicate for the concrete phase-axis norm used by the
representation.
-/
def HasQuadraticBregmanBound {n : ℕ} (K : MatrixEnd n) : Prop :=
  ∀ ε : ℝ, ε * ‖K‖ ≤ 1 →
    ‖exponentialRemainder K ε‖ ≤ ε ^ 2 * ‖K‖ ^ 2

/-- Scalar size of the matrix Bregman exponential remainder. -/
noncomputable def matrixBregmanSize {n : ℕ}
    (K : MatrixEnd n) (ε : ℝ) : ℝ :=
  ‖exponentialRemainder K ε‖

/-- The local Dikin radius for a matrix phase-axis step `ε • K`. -/
noncomputable def matrixDikinRadius {n : ℕ}
    (K : MatrixEnd n) (ε : ℝ) : ℝ :=
  ε * ‖K‖

/-- The matrix Dikin radius is nonnegative for nonnegative steps. -/
theorem matrixDikinRadius_nonneg_of_step_nonneg {n : ℕ}
    (K : MatrixEnd n) {ε : ℝ}
    (hε : 0 ≤ ε) :
    0 ≤ matrixDikinRadius K ε := by
  unfold matrixDikinRadius
  exact mul_nonneg hε (norm_nonneg K)

/--
The parameterized quadratic matrix Bregman bound is exactly the Dikin
radius-squared estimate.
-/
theorem matrix_bregman_size_le_dikin_radius_sq_of_quadratic_bound {n : ℕ}
    (K : MatrixEnd n)
    (hquad : HasQuadraticBregmanBound K)
    (ε : ℝ)
    (hε : ε * ‖K‖ ≤ 1) :
    matrixBregmanSize K ε ≤ matrixDikinRadius K ε ^ 2 := by
  have h := hquad ε hε
  unfold matrixBregmanSize matrixDikinRadius
  calc
    ‖exponentialRemainder K ε‖ ≤ ε ^ 2 * ‖K‖ ^ 2 := h
    _ = (ε * ‖K‖) ^ 2 := by ring

/--
Read back the quadratic Bregman estimate from an explicit theorem hypothesis.
-/
theorem phase_axis_deformation_bounded_of_quadratic_bound {n : ℕ}
    (K : MatrixEnd n)
    (hquad : HasQuadraticBregmanBound K)
    (ε : ℝ)
    (hε : ε * ‖K‖ ≤ 1) :
    ‖exponentialRemainder K ε‖ ≤ ε ^ 2 * ‖K‖ ^ 2 :=
  hquad ε hε

/--
If the phase axis has norm one, the quadratic Bregman bound becomes the Dikin
radius estimate `‖exp (εK) - I - εK‖ ≤ ε²`.
-/
theorem dikin_bound_of_phase_axis_norm {n : ℕ}
    (K : MatrixEnd n)
    (hquad : HasQuadraticBregmanBound K)
    (hK_norm : ‖K‖ = 1)
    (ε : ℝ)
    (hε : ε ≤ 1) :
    ‖exponentialRemainder K ε‖ ≤ ε ^ 2 := by
  have hεK : ε * ‖K‖ ≤ 1 := by
    simpa [hK_norm] using hε
  have h := hquad ε hεK
  simpa [hK_norm] using h

/--
The flat KMS boundary has zero modular step, so the Bregman deformation clears
without any analytic estimate.
-/
theorem bregman_bound_clears_at_flat_boundary {n : ℕ}
    (K : MatrixEnd n) :
    ‖exponentialRemainder K 0‖ ≤ 0 := by
  simp

end BregmanAnalyticBound
