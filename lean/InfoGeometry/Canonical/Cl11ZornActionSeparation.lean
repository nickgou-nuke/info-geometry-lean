import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Canonical.OperatorZornPolarizationSymmetry

/-!
# Anticommuting implementers, commuting conjugations, and Zorn obstructions

The real Pauli implementers are reused from `Cl11Matrix`. Their product
squares to minus identity. The induced conjugations commute and their
composite squares to identity: the central sign disappears in conjugation.
This is not a free affine glide or a global covering theorem.
-/

namespace InfoGeometry.Canonical.Cl11ZornActionSeparation

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Canonical.OperatorZornPolarizationSymmetry
open InfoGeometry.Physics.NCG

/-- These are the source's anticommuting two-state implementers. -/
theorem implementers_anticommute : Eplus * J1 = -(J1 * Eplus) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Eplus, J1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The implementing product has square minus identity, not plus identity. -/
theorem implementer_product_square : (J1 * Eplus) * (J1 * Eplus) = -(1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Eplus, J1, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugations commute although the implementers anticommute. -/
theorem induced_conjugations_commute (X : Mat2) :
    Eplus * (J1 * X * J1) * Eplus = J1 * (Eplus * X * Eplus) * J1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, J1, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Eplus * J1` is the inverse of `J1 * Eplus`. The conjugation has order two. -/
theorem composite_conjugation_square (X : Mat2) :
    (J1 * Eplus) * ((J1 * Eplus) * X * (Eplus * J1)) * (Eplus * J1) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, J1, Matrix.mul_apply, Fin.sum_univ_two]

/-- A three-vector of actual noncommuting matrix coefficients. -/
def noncommutingVector : OperatorVector Mat2 := ![0, Eplus, J1]

/-- Zero ordered quadratic readout does not imply a square-zero operator-Zorn ray. -/
theorem operator_null_not_square_zero :
    operatorZornCasimir (sigmaPlus noncommutingVector) = 0 ∧
      operatorZornMul (sigmaPlus noncommutingVector) (sigmaPlus noncommutingVector) ≠ 0 := by
  refine ⟨orderedReadout_sigmaPlus _, ?_⟩
  intro h
  have hc := (sigmaPlus_square_zero_iff_commuting noncommutingVector).mp h
  have h01 := congrArg (fun M : Mat2 => M 0 1) hc.1
  norm_num [noncommutingVector, Eplus, J1, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- The coordinate sign is not an automorphism of the scalar Zorn product. -/
theorem offDiagonalSign_not_multiplicative :
    ¬ ∀ X Y : OperatorZornMatrix ℝ,
      offDiagonalSign (operatorZornMul X Y) =
        operatorZornMul (offDiagonalSign X) (offDiagonalSign Y) := by
  intro h
  have h2 := congrArg (fun X : OperatorZornMatrix ℝ => X.sigma_minus 2)
    (h (sigmaPlus ![1, 0, 0]) (sigmaPlus ![0, 1, 0]))
  norm_num [offDiagonalSign, operatorZornMul, sigmaPlus, NCZornElement.mul,
    NCZornElement.zornCross, NCZornElement.zornDot] at h2

/-- Plain exchange also fails multiplicativity; their signed composite does not. -/
theorem exchange_not_multiplicative :
    ¬ ∀ X Y : OperatorZornMatrix ℝ,
      exchange (operatorZornMul X Y) =
        operatorZornMul (exchange X) (exchange Y) := by
  intro h
  have h2 := congrArg (fun X : OperatorZornMatrix ℝ => X.sigma_plus 2)
    (h (sigmaPlus ![1, 0, 0]) (sigmaPlus ![0, 1, 0]))
  norm_num [exchange, operatorZornMul, sigmaPlus, NCZornElement.mul,
    NCZornElement.zornCross, NCZornElement.zornDot] at h2

/-- Even the multiplicative signed exchange does not preserve every
operator-valued ordered norm. This defect disappears only after an appropriate trace. -/
theorem signedExchange_orderedReadout_not_invariant :
    operatorZornCasimir (signedExchange (operatorZornCoordinates Eplus J1 0 0)) ≠
      operatorZornCasimir (operatorZornCoordinates Eplus J1 0 0) := by
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  norm_num [operatorZornCasimir, signedExchange, operatorZornCoordinates,
    operatorDot, NCZornElement.zornDot, Eplus, J1, Matrix.mul_apply,
    Fin.sum_univ_two] at h01

/-- A fixed algebra unit is not a nontrivial translation of a base space. -/
theorem signedExchange_fixes_unit {A : Type*} [Ring A] :
    signedExchange (operatorZornCoordinates (1 : A) 1 0 0) =
      operatorZornCoordinates 1 1 0 0 := by
  simp [signedExchange, operatorZornCoordinates]

end InfoGeometry.Canonical.Cl11ZornActionSeparation
