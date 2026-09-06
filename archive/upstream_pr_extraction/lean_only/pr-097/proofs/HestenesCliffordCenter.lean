import proofs.HestenesClPlus14

/-!
# Spacetime pseudoscalar owner for real Cl⁺(1,3)

This owner keeps the pseudoscalar distinct from the beta-twisted reverse
operation.  The matrix bridge must later use the Hestenes Hermitian adjoint,
not pure reversion, on this central complex structure.
-/

noncomputable section
namespace HestenesCliffordCenter

open HestenesCl14

abbrev Algebra := Cl14
abbrev EvenAlgebra := ClPlus14

def omegaPair (i j : Fin 4) : EvenAlgebra :=
  (CliffordAlgebra.even.ι Q14).bilin (basisVec i) (basisVec j)

def spacetimePseudoscalar : EvenAlgebra :=
  omegaPair 0 1 * omegaPair 2 3

@[simp] theorem spacetimePseudoscalar_val :
    (spacetimePseudoscalar : Algebra) =
      gamma 0 * gamma 1 * gamma 2 * gamma 3 := by
  change (gamma 0 * gamma 1) * (gamma 2 * gamma 3) = _
  simp only [mul_assoc]

@[simp] theorem spacetimePseudoscalar_mem_even :
    (spacetimePseudoscalar : Algebra) ∈ CliffordAlgebra.even Q14 := by
  exact spacetimePseudoscalar.property

end HestenesCliffordCenter
end noncomputable section
