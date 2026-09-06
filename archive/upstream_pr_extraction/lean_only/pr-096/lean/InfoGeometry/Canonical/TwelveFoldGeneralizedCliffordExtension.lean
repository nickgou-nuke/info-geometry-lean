import Mathlib.Tactic
import InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra
import InfoGeometry.Canonical.TwelveFoldExplicitOperators

/-!
# Twelvefold unit inside the six-state generalized Clifford envelope

The existing order-twelve master matrix is not asserted to be a defining
order-twelve Weyl generator.  This file proves the exact, weaker statement:
it is a linear combination of the two generalized-Clifford monomials
`I ⊗ X²` and `Γ ⊗ X²`.  Its exact multiplicative order remains owned by
`TwelveFoldExplicitOperators.masterTwelve_order_exact`.
-/

open scoped Matrix

namespace InfoGeometry.Canonical.TwelveFoldGeneralizedCliffordExtension

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra
open InfoGeometry.Canonical.TwelveFoldExplicitOperators

noncomputable section

private abbrev aMinus : ℂ := (1 - Complex.I) / 2
private abbrev aPlus : ℂ := (1 + Complex.I) / 2

/-- The cube of the quartic sheet phase is the exact linear combination
`((1-i)/2)I + ((1+i)/2)Γ`. -/
theorem omegaChi_cube_decomposition :
    omegaChi ^ 3 =
      aMinus • (1 : SheetMatrix) + aPlus • sheetParity := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [omegaChi, aMinus, aPlus, uPlus, uMinus, sheetParity,
      pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_mul_I] <;> ring

/-- Exact tensor-factor decomposition of the twelvefold master. -/
theorem masterTwelve_tensor_decomposition :
    masterTwelve =
      aMinus • Matrix.kronecker (1 : SheetMatrix) (colorShift ^ 2) +
      aPlus • Matrix.kronecker sheetParity (colorShift ^ 2) := by
  rw [masterTwelve_eq_kronecker, omegaChi_cube_decomposition]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.add_apply]
  ring

/-- The second tensor generator is the GCA monomial `Z₆³X₆²`. -/
theorem sixWeylZ_cube_mul_sixWeylX_sq (ω : ℂ) (hω : ω ^ 3 = 1) :
    sixWeylZ ω ^ 3 * sixWeylX ^ 2 =
      Matrix.kronecker sheetParity (colorShift ^ 2) := by
  rw [sixWeylZ_cube ω hω,
    InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra.sixWeylX_sq]
  rw [sixParity, kronecker_mul]
  simp

/-- The master is an explicit linear combination of two order-six GCA
monomials. -/
theorem masterTwelve_gca_decomposition (ω : ℂ) (hω : ω ^ 3 = 1) :
    masterTwelve =
      aMinus • sixWeylX ^ 2 +
      aPlus • (sixWeylZ ω ^ 3 * sixWeylX ^ 2) := by
  rw [masterTwelve_tensor_decomposition, ← sixWeylX_sq]
  rw [sixWeylZ_cube_mul_sixWeylX_sq ω hω]

/-- Consequently the twelvefold master belongs to the linear span of the two
specified generalized-Clifford monomials. -/
theorem masterTwelve_mem_gca_monomial_span (ω : ℂ) (hω : ω ^ 3 = 1) :
    masterTwelve ∈ Submodule.span ℂ
      ({sixWeylX ^ 2, sixWeylZ ω ^ 3 * sixWeylX ^ 2} : Set SixMatrix) := by
  rw [masterTwelve_gca_decomposition ω hω]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end
end InfoGeometry.Canonical.TwelveFoldGeneralizedCliffordExtension
