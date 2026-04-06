import InfoGeometry.Canonical.RelativeModularCore
import InfoGeometry.MaxEnt.JaynesInfoStatMech
import InfoGeometry.Meta.Architecture

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
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeModularCore
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
  rw [RelativeStatePair.modularOperator_eq_diagMatrix_density]
  rw [RelativeStatePair.modularOperator_eq_diagMatrix_density]
  rw [RelativeStatePair.modularOperator_eq_diagMatrix_density]
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

end Finite

end InfoGeometry.Canonical.RelativeModularOperator
