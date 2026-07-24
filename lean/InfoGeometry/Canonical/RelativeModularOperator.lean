import InfoGeometry.Canonical.RelativeModularCore
import InfoGeometry.MaxEnt.JaynesInfoStatMech
import InfoGeometry.Meta.Architecture
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators

/-!
# Relative Modular Operator

Canonical finite diagonal owner for the relative modular operator over projective
positive-state pairs.

This file sits strictly between:
- `RelativeModularCore`, which owns the projective relative-state pair and its
  cocycle laws,
- `RelativeSurprisalOperatorLift`, which packages downstream first-quantized
  readouts.

The owner here is the diagonal operator with projective relative density on the
diagonal. Its logarithmic readouts recover the relative log-density and the
relative modular potential.
-/

namespace InfoGeometry.Canonical.RelativeModularOperator

open InfoGeometry.Canonical.PositiveRayCore
open RelativePotentialCore
open RelativeModularCore
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

section Finite

variable {n : ℕ} [Nonempty (Fin n)]

/-- Finite diagonal relative modular operator attached to a projective state pair. -/
@[rep_depth operator]
noncomputable def RelativeStatePair.modularOperator
    (R : RelativeStatePair (Fin n)) : FinMat n :=
  diagMatrix R.density

@[simp] theorem RelativeStatePair.modularOperator_eq_diagMatrix_density
    (R : RelativeStatePair (Fin n)) :
    RelativeStatePair.modularOperator R = diagMatrix R.density := rfl

@[simp] theorem RelativeStatePair.modularOperator_diag
    (R : RelativeStatePair (Fin n)) (i : Fin n) :
    RelativeStatePair.modularOperator R i i = R.density i := by
  rw [RelativeStatePair.modularOperator_eq_diagMatrix_density]
  rw [diagMatrix, Matrix.diagonal_apply_eq]

@[simp] theorem RelativeStatePair.modularOperator_offdiag
    (R : RelativeStatePair (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    RelativeStatePair.modularOperator R i j = 0 := by
  rw [RelativeStatePair.modularOperator_eq_diagMatrix_density]
  rw [diagMatrix, Matrix.diagonal_apply_ne _ hij]

@[simp] theorem RelativeStatePair.modularOperator_diag_eq_exp_logDensity
    (R : RelativeStatePair (Fin n)) (i : Fin n) :
    RelativeStatePair.modularOperator R i i = Real.exp (R.logDensity i) := by
  rw [RelativeStatePair.modularOperator_diag]
  exact relativeDensity_eq_exp_relativeLogDensity R.source R.target i

@[simp] theorem RelativeStatePair.log_modularOperator_diag_eq_logDensity
    (R : RelativeStatePair (Fin n)) (i : Fin n) :
    Real.log (RelativeStatePair.modularOperator R i i) = R.logDensity i := by
  rw [RelativeStatePair.modularOperator_diag_eq_exp_logDensity]
  simp

@[simp] theorem RelativeStatePair.modularPotential_eq_neg_log_modularOperator_diag
    (R : RelativeStatePair (Fin n)) (i : Fin n) :
    R.modularPotential i = -Real.log (RelativeStatePair.modularOperator R i i) := by
  rw [RelativeStatePair.modularPotential_eq_neg_logDensity]
  rw [← RelativeStatePair.log_modularOperator_diag_eq_logDensity]

/-- Composition of relative state pairs becomes multiplication of diagonal modular operators. -/
@[rep_depth operator]
theorem RelativeStatePair.compose_modularOperator
    (R₁₂ R₂₃ : RelativeStatePair (Fin n)) (h : R₁₂.target = R₂₃.source) :
    RelativeStatePair.modularOperator (R₁₂.compose R₂₃)
      = RelativeStatePair.modularOperator R₁₂ * RelativeStatePair.modularOperator R₂₃ := by
  rw [RelativeModularOperator.RelativeStatePair.modularOperator_eq_diagMatrix_density]
  rw [RelativeModularOperator.RelativeStatePair.modularOperator_eq_diagMatrix_density]
  rw [RelativeModularOperator.RelativeStatePair.modularOperator_eq_diagMatrix_density]
  unfold diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    change relativeDensity (α := Fin n) R₁₂.source R₂₃.target i =
      relativeDensity (α := Fin n) R₁₂.source R₁₂.target i
        * relativeDensity (α := Fin n) R₂₃.source R₂₃.target i
    rw [← h]
    exact relativeDensity_cocycle R₁₂.source R₁₂.target R₂₃.target i
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]

/-- Canonical finite relative modular operator for a pair of projective states. -/
@[rep_depth operator]
noncomputable def relativeModularOperator
    (q q0 : PositiveRay (Fin n)) : FinMat n :=
  RelativeStatePair.modularOperator ({ source := q, target := q0 } : RelativeStatePair (Fin n))

@[simp] theorem relativeModularOperator_diag
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeModularOperator (n := n) q q0 i i =
      relativeDensity (α := Fin n) q q0 i := by
  change RelativeStatePair.modularOperator
      ({ source := q, target := q0 } : RelativeStatePair (Fin n)) i i
      = relativeDensity (α := Fin n) q q0 i
  exact RelativeStatePair.modularOperator_diag
    (R := ({ source := q, target := q0 } : RelativeStatePair (Fin n))) i

@[simp] theorem relativeModularOperator_offdiag
    (q q0 : PositiveRay (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    relativeModularOperator (n := n) q q0 i j = 0 := by
  change RelativeStatePair.modularOperator
      ({ source := q, target := q0 } : RelativeStatePair (Fin n)) i j = 0
  exact RelativeStatePair.modularOperator_offdiag
    (R := ({ source := q, target := q0 } : RelativeStatePair (Fin n))) (hij := hij)

@[simp] theorem relativeModularOperator_diag_eq_exp_relativeLogDensity
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeModularOperator (n := n) q q0 i i =
      Real.exp (relativeLogDensity (α := Fin n) q q0 i) := by
  change RelativeStatePair.modularOperator
      ({ source := q, target := q0 } : RelativeStatePair (Fin n)) i i
      = Real.exp (relativeLogDensity (α := Fin n) q q0 i)
  exact RelativeStatePair.modularOperator_diag_eq_exp_logDensity
    (R := ({ source := q, target := q0 } : RelativeStatePair (Fin n))) i

@[simp] theorem relativeLogDensity_eq_log_relativeModularOperator_diag
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeLogDensity (α := Fin n) q q0 i =
      Real.log (relativeModularOperator (n := n) q q0 i i) := by
  symm
  change Real.log (RelativeStatePair.modularOperator
      ({ source := q, target := q0 } : RelativeStatePair (Fin n)) i i)
      = relativeLogDensity (α := Fin n) q q0 i
  exact RelativeStatePair.log_modularOperator_diag_eq_logDensity
    (R := ({ source := q, target := q0 } : RelativeStatePair (Fin n))) i

@[simp] theorem relativeModularPotential_eq_neg_log_relativeModularOperator_diag
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeModularPotential (α := Fin n) q q0 i =
      -Real.log (relativeModularOperator (n := n) q q0 i i) := by
  change relativeModularPotential (α := Fin n) q q0 i =
      -Real.log (RelativeStatePair.modularOperator
        ({ source := q, target := q0 } : RelativeStatePair (Fin n)) i i)
  exact RelativeStatePair.modularPotential_eq_neg_log_modularOperator_diag
    (R := ({ source := q, target := q0 } : RelativeStatePair (Fin n))) i

@[simp] theorem relativeModularOperator_self
    (q : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q = (1 : FinMat n) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [relativeModularOperator_diag, Matrix.one_apply]
    rw [if_pos rfl]
    exact relativeDensity_self (q := q) (a := i)
  · rw [relativeModularOperator_offdiag (hij := hij)]
    rw [Matrix.one_apply]
    rw [if_neg hij]

/-- The finite relative modular operator satisfies the multiplicative cocycle law. -/
@[rep_depth operator]
theorem relativeModularOperator_cocycle
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q1
      = relativeModularOperator (n := n) q q0
          * relativeModularOperator (n := n) q0 q1 := by
  change RelativeStatePair.modularOperator
      ({ source := q, target := q1 } : RelativeStatePair (Fin n))
      = RelativeStatePair.modularOperator
          ({ source := q, target := q0 } : RelativeStatePair (Fin n))
          * RelativeStatePair.modularOperator
              ({ source := q0, target := q1 } : RelativeStatePair (Fin n))
  exact RelativeStatePair.compose_modularOperator
    (R₁₂ := ({ source := q, target := q0 } : RelativeStatePair (Fin n)))
    (R₂₃ := ({ source := q0, target := q1 } : RelativeStatePair (Fin n)))
    rfl

/--
Multiplicative volume shadow of the finite relative modular operator owner.
-/
@[rep_depth operator]
noncomputable def relativeModularVolumeShadow
    (q q0 : PositiveRay (Fin n)) : ℝ :=
  Matrix.det (relativeModularOperator (n := n) q q0)

@[simp] theorem relativeModularVolumeShadow_eq_prod_relativeDensity
    (q q0 : PositiveRay (Fin n)) :
    relativeModularVolumeShadow (n := n) q q0
      = ∏ i, relativeDensity (α := Fin n) q q0 i := by
  unfold relativeModularVolumeShadow relativeModularOperator
  change Matrix.det (Matrix.diagonal (fun i => relativeDensity (α := Fin n) q q0 i))
      = ∏ i, relativeDensity (α := Fin n) q q0 i
  rw [Matrix.det_diagonal]

@[simp] theorem relativeModularVolumeShadow_pos
    (q q0 : PositiveRay (Fin n)) :
    0 < relativeModularVolumeShadow (n := n) q q0 := by
  rw [relativeModularVolumeShadow_eq_prod_relativeDensity]
  refine Finset.prod_pos ?_
  intro i hi
  rw [relativeDensity_eq_exp_relativeLogDensity]
  positivity

@[simp] theorem relativeModularVolumeShadow_self
    (q : PositiveRay (Fin n)) :
    relativeModularVolumeShadow (n := n) q q = 1 := by
  unfold relativeModularVolumeShadow
  rw [relativeModularOperator_self]
  simp

/--
The volume shadow inherits the multiplicative cocycle law of the modular
operator owner.
-/
@[rep_depth operator]
theorem relativeModularVolumeShadow_cocycle
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeModularVolumeShadow (n := n) q q1
      = relativeModularVolumeShadow (n := n) q q0
          * relativeModularVolumeShadow (n := n) q0 q1 := by
  unfold relativeModularVolumeShadow
  rw [relativeModularOperator_cocycle]
  exact Matrix.det_mul _ _

/--
Additive log-volume readout of the finite relative modular operator.
-/
@[rep_depth operator]
noncomputable def relativeModularVolumePotential
    (q q0 : PositiveRay (Fin n)) : ℝ :=
  -Real.log (relativeModularVolumeShadow (n := n) q q0)

@[rep_depth thermo, capstone]
theorem log_relativeModularVolumeShadow_eq_sum_relativeLogDensity
    (q q0 : PositiveRay (Fin n)) :
    Real.log (relativeModularVolumeShadow (n := n) q q0)
      = ∑ i, relativeLogDensity (α := Fin n) q q0 i := by
  rw [relativeModularVolumeShadow_eq_prod_relativeDensity]
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    rw [relativeDensity_eq_exp_relativeLogDensity]
    rw [Real.log_exp]
  · intro i hi
    rw [relativeDensity_eq_exp_relativeLogDensity]
    positivity

@[rep_depth thermo, capstone]
theorem relativeModularVolumePotential_eq_sum_relativeModularPotential
    (q q0 : PositiveRay (Fin n)) :
    relativeModularVolumePotential (n := n) q q0
      = ∑ i, relativeModularPotential (α := Fin n) q q0 i := by
  unfold relativeModularVolumePotential
  rw [log_relativeModularVolumeShadow_eq_sum_relativeLogDensity]
  calc
    -(∑ i, relativeLogDensity (α := Fin n) q q0 i)
      = ∑ i, -relativeLogDensity (α := Fin n) q q0 i := by
          rw [← Finset.sum_neg_distrib]
    _ = ∑ i, relativeModularPotential (α := Fin n) q q0 i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [relativeModularPotential_eq_neg_relativeLogDensity]

@[rep_depth thermo, capstone]
theorem log_relativeModularVolumeShadow_cocycle
    (q q0 q1 : PositiveRay (Fin n)) :
    Real.log (relativeModularVolumeShadow (n := n) q q1)
      = Real.log (relativeModularVolumeShadow (n := n) q q0)
          + Real.log (relativeModularVolumeShadow (n := n) q0 q1) := by
  rw [relativeModularVolumeShadow_cocycle]
  exact Real.log_mul
    (ne_of_gt (relativeModularVolumeShadow_pos (n := n) q q0))
    (ne_of_gt (relativeModularVolumeShadow_pos (n := n) q0 q1))

@[rep_depth thermo, capstone]
theorem relativeModularVolumePotential_cocycle
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeModularVolumePotential (n := n) q q1
      = relativeModularVolumePotential (n := n) q q0
          + relativeModularVolumePotential (n := n) q0 q1 := by
  unfold relativeModularVolumePotential
  rw [log_relativeModularVolumeShadow_cocycle (n := n) q q0 q1]
  ring

@[simp, rep_depth thermo, capstone]
theorem relativeModularVolumePotential_self
    (q : PositiveRay (Fin n)) :
    relativeModularVolumePotential (n := n) q q = 0 := by
  unfold relativeModularVolumePotential
  rw [relativeModularVolumeShadow_self]
  simp

/--
Berezinian-style supervolume shadow obtained as the ratio of plus/minus volume
shadows.
-/
@[rep_depth operator]
noncomputable def relativeModularBerezinianShadow
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) : ℝ :=
  relativeModularVolumeShadow (n := n) qPlus q0Plus
    / relativeModularVolumeShadow (n := n) qMinus q0Minus

/-- Compatibility alias for the Berezinian-style scalar shadow. -/
@[rep_depth operator]
noncomputable abbrev relativeModularSupervolumeShadow
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) : ℝ :=
  relativeModularBerezinianShadow (n := n) qPlus q0Plus qMinus q0Minus

@[simp] theorem relativeModularBerezinianShadow_pos
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    0 < relativeModularBerezinianShadow (n := n) qPlus q0Plus qMinus q0Minus := by
  unfold relativeModularBerezinianShadow
  exact div_pos
    (relativeModularVolumeShadow_pos (n := n) qPlus q0Plus)
    (relativeModularVolumeShadow_pos (n := n) qMinus q0Minus)

@[rep_depth operator]
noncomputable def relativeModularBerezinianPotential
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) : ℝ :=
  -Real.log (relativeModularBerezinianShadow (n := n) qPlus q0Plus qMinus q0Minus)

/-- Compatibility alias for the Berezinian negative-log readout. -/
@[rep_depth operator]
noncomputable abbrev relativeModularSupervolumePotential
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) : ℝ :=
  relativeModularBerezinianPotential (n := n) qPlus q0Plus qMinus q0Minus

@[rep_depth thermo, capstone]
theorem log_relativeModularBerezinianShadow_eq_volumeLog_sub_volumeLog
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    Real.log (relativeModularBerezinianShadow (n := n) qPlus q0Plus qMinus q0Minus)
      = Real.log (relativeModularVolumeShadow (n := n) qPlus q0Plus)
          - Real.log (relativeModularVolumeShadow (n := n) qMinus q0Minus) := by
  unfold relativeModularBerezinianShadow
  rw [Real.log_div
    (ne_of_gt (relativeModularVolumeShadow_pos (n := n) qPlus q0Plus))
    (ne_of_gt (relativeModularVolumeShadow_pos (n := n) qMinus q0Minus))]

@[rep_depth thermo, capstone]
theorem relativeModularBerezinianPotential_eq_volumePotential_sub_volumePotential
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    relativeModularBerezinianPotential (n := n) qPlus q0Plus qMinus q0Minus
      = relativeModularVolumePotential (n := n) qPlus q0Plus
          - relativeModularVolumePotential (n := n) qMinus q0Minus := by
  unfold relativeModularBerezinianPotential relativeModularVolumePotential
  rw [log_relativeModularBerezinianShadow_eq_volumeLog_sub_volumeLog]
  ring

@[rep_depth thermo, capstone]
theorem relativeModularBerezinianPotential_eq_sum_relativeModularPotential_sub_sum_relativeModularPotential
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    relativeModularBerezinianPotential (n := n) qPlus q0Plus qMinus q0Minus
      = (∑ i, relativeModularPotential (α := Fin n) qPlus q0Plus i)
          - ∑ i, relativeModularPotential (α := Fin n) qMinus q0Minus i := by
  rw [relativeModularBerezinianPotential_eq_volumePotential_sub_volumePotential]
  rw [relativeModularVolumePotential_eq_sum_relativeModularPotential]
  rw [relativeModularVolumePotential_eq_sum_relativeModularPotential]

/--
Primary scalar readout of the finite relative modular operator owner:
the averaged negative logarithmic diagonal readout of `Δ`.
-/
@[rep_depth operator]
noncomputable def relativeModularHamiltonianReadout
    (q q0 : PositiveRay (Fin n)) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, -Real.log (relativeModularOperator (n := n) q q0 i i)

/--
Owner-level scalar readout equals the averaged relative modular potential.
-/
@[rep_depth thermo, capstone]
theorem relativeModularHamiltonianReadout_eq_average_relativeModularPotential
    (q q0 : PositiveRay (Fin n)) :
    relativeModularHamiltonianReadout (n := n) q q0
      = (n : ℝ)⁻¹ * ∑ i,
          relativeModularPotential (α := Fin n) q q0 i := by
  unfold relativeModularHamiltonianReadout
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  exact (relativeModularPotential_eq_neg_log_relativeModularOperator_diag (n := n) q q0 i).symm

/--
The averaged modular Hamiltonian readout is the normalized negative logarithmic
volume shadow of the finite modular operator owner.
-/
@[rep_depth thermo, capstone]
theorem relativeModularHamiltonianReadout_eq_inv_card_mul_relativeModularVolumePotential
    (q q0 : PositiveRay (Fin n)) :
    relativeModularHamiltonianReadout (n := n) q q0
      = (n : ℝ)⁻¹ * relativeModularVolumePotential (n := n) q q0 := by
  rw [relativeModularHamiltonianReadout_eq_average_relativeModularPotential]
  rw [relativeModularVolumePotential_eq_sum_relativeModularPotential]

/--
Finite commutative shadow of the RedLine information energy.

This theorem is only the diagonal finite-dimensional readout shadow:
the genuine noncommutative operator-ratio theorem must pass through the
Drazin/Penrose regular-lane functional calculus, not through this diagonal
model.
-/
@[rep_depth thermo, capstone]
theorem relativeInformationEnergy_finiteShadow_eq_sum_gauge_sq_neg_log_relativeModularOperator_diag
    (q q0 : PositiveRay (Fin n)) :
    relativeInformationEnergy (α := Fin n) q q0 =
      ∑ i, gaugeSection (α := Fin n) q0 i
        * (-Real.log (relativeModularOperator (n := n) q q0 i i)) ^ (2 : ℕ) := by
  unfold relativeInformationEnergy
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [relativeModularPotential_eq_neg_log_relativeModularOperator_diag]

/--
Finite commutative shadow of the RedLine information norm.

This is the RMS size of the negative logarithmic diagonal readout in the finite
diagonal model only. It is a shadow of the intended noncommutative theorem, not
the noncommutative theorem itself.
-/
@[rep_depth thermo, capstone]
theorem relativeInformationNorm_finiteShadow_eq_sqrt_sum_gauge_sq_neg_log_relativeModularOperator_diag
    (q q0 : PositiveRay (Fin n)) :
    relativeInformationNorm (α := Fin n) q q0 =
      Real.sqrt
        (∑ i, gaugeSection (α := Fin n) q0 i
          * (-Real.log (relativeModularOperator (n := n) q q0 i i)) ^ (2 : ℕ)) := by
  unfold relativeInformationNorm
  rw [relativeInformationEnergy_finiteShadow_eq_sum_gauge_sq_neg_log_relativeModularOperator_diag]

@[rep_depth thermo, capstone]
theorem relativeModularHamiltonianReadout_cocycle
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeModularHamiltonianReadout (n := n) q q1
      = relativeModularHamiltonianReadout (n := n) q q0
          + relativeModularHamiltonianReadout (n := n) q0 q1 := by
  rw [relativeModularHamiltonianReadout_eq_inv_card_mul_relativeModularVolumePotential]
  rw [relativeModularHamiltonianReadout_eq_inv_card_mul_relativeModularVolumePotential]
  rw [relativeModularHamiltonianReadout_eq_inv_card_mul_relativeModularVolumePotential]
  rw [relativeModularVolumePotential_cocycle (n := n) q q0 q1]
  ring

/--
Self-relative modular Hamiltonian readout vanishes.
-/
@[simp, rep_depth thermo, capstone]
theorem relativeModularHamiltonianReadout_self
    (q : PositiveRay (Fin n)) :
    relativeModularHamiltonianReadout (n := n) q q = 0 := by
  unfold relativeModularHamiltonianReadout
  have hsum : ∑ i : Fin n, -Real.log (relativeModularOperator (n := n) q q i i) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [relativeModularOperator_diag]
    rw [relativeDensity_self (q := q) (a := i)]
    simp
  rw [hsum]
  ring

end Finite

end InfoGeometry.Canonical.RelativeModularOperator
