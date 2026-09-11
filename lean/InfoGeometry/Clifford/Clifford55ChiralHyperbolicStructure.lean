import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Hyperbolic chirality projectors for the native `Cl(5,5)` spinor carrier

The native spinor owner already constructs the ordered volume matrix and its
two complementary idempotents.  This file proves the operator-theoretic
consequence needed for the chiral-sheet interpretation: an operator that
anticommutes with the volume exchanges the two chiral projectors.

No matrix classification or Pin representation theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SpinorChirality

open InfoGeometry.Clifford.SpinorRep

noncomputable def chiralDilation (r : ℝ) : SpinorMatrix 5 :=
  r • chiralPlusProjector + r⁻¹ • chiralMinusProjector

theorem chiralDilation_mul_plus (r : ℝ) :
    chiralDilation r * chiralPlusProjector =
      r • chiralPlusProjector := by
  rw [chiralDilation, add_mul, smul_mul_assoc, smul_mul_assoc,
    chiralProjectors_orthogonal_rev, chiralPlusProjector_idempotent,
    smul_zero, add_zero]

theorem chiralDilation_mul_minus (r : ℝ) :
    chiralDilation r * chiralMinusProjector =
      r⁻¹ • chiralMinusProjector := by
  rw [chiralDilation, add_mul, smul_mul_assoc, smul_mul_assoc,
    chiralProjectors_orthogonal, chiralMinusProjector_idempotent,
    smul_zero, zero_add]

theorem chiralDilation_mul_inverse {r : ℝ} (hr : r ≠ 0) :
    chiralDilation r * chiralDilation r⁻¹ =
      (1 : SpinorMatrix 5) := by
  have hinv : (r⁻¹)⁻¹ = r := inv_inv r
  rw [show chiralDilation r⁻¹ =
      r⁻¹ • chiralPlusProjector + r • chiralMinusProjector by
        simp [chiralDilation, hinv]]
  rw [mul_add, Algebra.mul_smul_comm, Algebra.mul_smul_comm,
    chiralDilation_mul_plus, chiralDilation_mul_minus]
  rw [smul_smul, smul_smul, inv_mul_cancel₀ hr, mul_inv_cancel₀ hr,
    one_smul]
  simpa using chiralProjectors_complementary

theorem chiralProjector_plus_swap_of_anticommutes
    (A : SpinorMatrix 5)
    (hA : A * chirality55 = -(chirality55 * A)) :
    A * chiralPlusProjector = chiralMinusProjector * A := by
  rw [chiralPlusProjector, chiralMinusProjector,
    Algebra.mul_smul_comm, smul_mul_assoc]
  have hcore : A * (1 + chirality55) = (1 - chirality55) * A := by
    rw [mul_add, sub_mul, one_mul, mul_one, hA]
    rfl
  rw [hcore]

theorem chiralProjector_minus_swap_of_anticommutes
    (A : SpinorMatrix 5)
    (hA : A * chirality55 = -(chirality55 * A)) :
    A * chiralMinusProjector = chiralPlusProjector * A := by
  rw [chiralPlusProjector, chiralMinusProjector,
    Algebra.mul_smul_comm, smul_mul_assoc]
  have hcore : A * (1 - chirality55) = (1 + chirality55) * A := by
    rw [mul_sub, add_mul, one_mul, mul_one, hA]
    simp only [sub_eq_add_neg, neg_neg]
  rw [hcore]

theorem chiralMinus_of_anticommutes
    (A : SpinorMatrix 5)
    (hA : A * chirality55 = -(chirality55 * A))
    (ψ : SpinorSpace 5)
    (hψ : chiralPlus ψ) :
    chiralMinus (matrixApply A ψ) := by
  have hA' : chirality55 * A = -(A * chirality55) := by
    have h := congrArg Neg.neg hA
    simpa using h.symm
  rw [chiralPlus] at hψ
  rw [← chirality55_eq_canonical] at hψ
  rw [chiralMinus]
  calc
    matrixApply chirality55 (matrixApply A ψ) =
        matrixApply (chirality55 * A) ψ :=
      (matrixApply_mul chirality55 A ψ).symm
    _ = matrixApply (-(A * chirality55)) ψ := by rw [hA']
    _ = -matrixApply (A * chirality55) ψ := matrixApply_neg (A * chirality55) ψ
    _ = -matrixApply A (matrixApply chirality55 ψ) := by
      rw [matrixApply_mul]
    _ = -matrixApply A ψ := by rw [hψ]

theorem chiralPlus_of_anticommutes
    (A : SpinorMatrix 5)
    (hA : A * chirality55 = -(chirality55 * A))
    (ψ : SpinorSpace 5)
    (hψ : chiralMinus ψ) :
    chiralPlus (matrixApply A ψ) := by
  rw [chiralMinus] at hψ
  rw [← chirality55_eq_canonical] at hψ
  rw [chiralPlus]
  calc
    matrixApply chirality55 (matrixApply A ψ) =
        matrixApply (chirality55 * A) ψ :=
      (matrixApply_mul chirality55 A ψ).symm
    _ = matrixApply (-(A * chirality55)) ψ := by
      have hA' : chirality55 * A = -(A * chirality55) := by
        have h := congrArg Neg.neg hA
        simpa using h.symm
      rw [hA']
    _ = -matrixApply (A * chirality55) ψ := matrixApply_neg (A * chirality55) ψ
    _ = -matrixApply A (matrixApply chirality55 ψ) := by
      rw [matrixApply_mul]
    _ = matrixApply A ψ := by
      rw [hψ]
      have hneg : matrixApply A (-ψ) = -matrixApply A ψ := by
        rw [matrixApply_eq_mulVec]
        exact Matrix.mulVec_neg ψ A
      rw [hneg]
      simp

end InfoGeometry.Clifford.Cl55SpinorChirality
