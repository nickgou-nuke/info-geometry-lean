import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

namespace InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv

open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

abbrev FusionTree := Fin 2 → ℂ

noncomputable def fLinearMap (τ s : ℂ) :
    FusionTree →ₗ[ℂ] FusionTree :=
  Matrix.toLin' (fibonacciFusionMatrix τ s)

noncomputable def fLinearEquiv (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FusionTree ≃ₗ[ℂ] FusionTree := by
  apply LinearEquiv.ofLinear (fLinearMap τ s) (fLinearMap τ s)
  · rw [show (fLinearMap τ s).comp (fLinearMap τ s) =
        Matrix.toLin' (fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s) by
        simp [fLinearMap, Matrix.toLin'_mul]]
    rw [fibonacciFusionMatrix_sq hs hτ]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · rw [show (fLinearMap τ s).comp (fLinearMap τ s) =
        Matrix.toLin' (fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s) by
        simp [fLinearMap, Matrix.toLin'_mul]]
    rw [fibonacciFusionMatrix_sq hs hτ]
    ext x i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

theorem fLinearEquiv_apply (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) (x : FusionTree) :
    fLinearEquiv τ s hs hτ x =
      Matrix.mulVec (fibonacciFusionMatrix τ s) x := by
  rfl

theorem fLinearEquiv_self_inverse (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (fLinearEquiv τ s hs hτ).symm = fLinearEquiv τ s hs hτ := by
  ext x
  simp [fLinearEquiv]

theorem fLinearEquiv_trans_self (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (fLinearEquiv τ s hs hτ).trans (fLinearEquiv τ s hs hτ) =
      LinearEquiv.refl ℂ FusionTree := by
  rw [← fLinearEquiv_self_inverse τ s hs hτ]
  exact (fLinearEquiv τ s hs hτ).self_trans_symm

end InfoGeometry.Categorical.FibonacciFusionTreeLinearEquiv
