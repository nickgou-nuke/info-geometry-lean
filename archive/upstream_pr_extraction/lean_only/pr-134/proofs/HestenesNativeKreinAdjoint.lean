import proofs.HestenesHermitianAdjoint

/-!
# Native Hestenes Hermitian/Krein adjoint

This is the Clifford operation compatible with matrix `J A† J`.  It is
separate from the previously certified beta-twisted reversion.
-/

noncomputable section
namespace HestenesNativeKreinAdjoint

open HestenesCl14
open HestenesCliffordKrein
open HestenesHermitianAdjoint

abbrev EvenAlgebra := ClPlus14

def hestenesKreinAdjoint (x : EvenAlgebra) : EvenAlgebra :=
  sigmaEven 0 * hestenesAdjoint x * sigmaEven 0

@[simp] theorem hestenesKreinAdjoint_add (x y : EvenAlgebra) :
    hestenesKreinAdjoint (x + y) =
      hestenesKreinAdjoint x + hestenesKreinAdjoint y := by
  simp [hestenesKreinAdjoint, hestenesAdjoint_add, mul_add, add_mul]

@[simp] theorem hestenesKreinAdjoint_smul (r : ℝ) (x : EvenAlgebra) :
    hestenesKreinAdjoint (r • x) = r • hestenesKreinAdjoint x := by
  simp [hestenesKreinAdjoint, hestenesAdjoint_smul]

@[simp] theorem hestenesKreinAdjoint_mul (x y : EvenAlgebra) :
    hestenesKreinAdjoint (x * y) =
      hestenesKreinAdjoint y * hestenesKreinAdjoint x := by
  apply Subtype.ext
  simp only [hestenesKreinAdjoint, hestenesAdjoint_mul, mul_assoc]
  rw [← mul_assoc (sigmaEven 0) (sigmaEven 0), sigmaEven_zero_sq]
  simp

@[simp] theorem hestenesAdjoint_beta :
    hestenesAdjoint (sigmaEven 0) = sigmaEven 0 := by
  apply Subtype.ext
  change gamma 0 * CliffordAlgebra.reverse beta * gamma 0 = beta
  rw [reverse_beta]
  change gamma 0 * (-(gamma 1 * gamma 0)) * gamma 0 =
    gamma 1 * gamma 0
  have h : gamma 0 * gamma 1 = -(gamma 1 * gamma 0) := by
    exact eq_neg_of_add_eq_zero_left (gamma_anticomm (by decide))
  rw [mul_neg]
  rw [← mul_assoc]
  rw [h]
  simp [mul_assoc, gamma_one_sq, gamma_zero_sq]

@[simp] theorem hestenesKreinAdjoint_involutive (x : EvenAlgebra) :
    hestenesKreinAdjoint (hestenesKreinAdjoint x) = x := by
  calc
    hestenesKreinAdjoint (hestenesKreinAdjoint x) =
        sigmaEven 0 * hestenesAdjoint
          (sigmaEven 0 * hestenesAdjoint x * sigmaEven 0) * sigmaEven 0 := by
            rfl
    _ = sigmaEven 0 *
          (hestenesAdjoint (sigmaEven 0) *
            hestenesAdjoint (hestenesAdjoint x) *
            hestenesAdjoint (sigmaEven 0)) * sigmaEven 0 := by
            rw [hestenesAdjoint_mul, hestenesAdjoint_mul]
            simp only [mul_assoc]
    _ = x := by
          rw [hestenesAdjoint_beta, hestenesAdjoint_involutive]
          calc
            sigmaEven 0 * (sigmaEven 0 * x * sigmaEven 0) * sigmaEven 0 =
                (sigmaEven 0 * sigmaEven 0) * x *
                  (sigmaEven 0 * sigmaEven 0) := by simp only [mul_assoc]
            _ = x := by rw [sigmaEven_zero_sq]; simp

end HestenesNativeKreinAdjoint
end noncomputable section
