import Mathlib
import InfoGeometry.Canonical.SplitSpinFactorTKKParameterInjectivity

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66

/-- Raw TKK parameter carrier before restricting the middle operator to the
metric-skew zero-grade subspace. -/
abbrev TKKRawParam := V10 × ((ℝ × Module.End ℝ V10) × V10)

/-- Linear parameterization of the four graded generator components.
The codomain is the pointwise function module; injectivity is independent of
whether the resulting functions are subsequently bundled as linear
endomorphisms. -/
def tkkParamMap : TKKRawParam →ₗ[ℝ] (V12 → V12) where
  toFun := tkkParamFunction
  map_add' p q := by
    rcases p with ⟨u, ⟨⟨lambda, A⟩, v⟩⟩
    rcases q with ⟨u', ⟨⟨lambda', A'⟩, v'⟩⟩
    funext x
    rcases x with ⟨s, z, t⟩
    simp [tkkParamFunction, tkkParamAction, pGen, dGen, rotGen, kGen,
      B10, zornPolar, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.add, ZornVectorMatrix.smul,
      ZornVec3.dot, Fin.sum_univ_three]
    module
  map_smul' a p := by
    rcases p with ⟨u, ⟨⟨lambda, A⟩, v⟩⟩
    funext x
    rcases x with ⟨s, z, t⟩
    simp [tkkParamFunction, tkkParamAction, pGen, dGen, rotGen, kGen,
      B10, zornPolar, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.smul, ZornVec3.dot,
      Fin.sum_univ_three]
    module

@[simp] theorem tkkParamMap_apply
    (u : V10) (lambda : ℝ) (A : Module.End ℝ V10) (v : V10) :
    tkkParamMap (u, ((lambda, A), v)) = tkkParamAction u lambda A v := rfl

/-- Full linear injectivity of the 3-graded TKK parameterization. -/
theorem tkkParamMap_injective : Function.Injective tkkParamMap := by
  rw [LinearMap.injective_iff_map_eq_zero]
  rintro ⟨u, ⟨⟨lambda, A⟩, v⟩⟩ h_zero
  have hfun : ∀ x : V12, tkkParamAction u lambda A v x = 0 := by
    intro x
    have hx := congrFun h_zero x
    simpa [tkkParamMap, tkkParamFunction] using hx
  have ⟨hu, hlambda, hA, hv⟩ :=
    tkk_param_injective u lambda A v hfun
  apply Prod.ext
  · exact hu
  · apply Prod.ext
    · apply Prod.ext
      · exact hlambda
      · exact hA
    · exact hv

/-- Equivalent pointwise injectivity statement for the underlying function
parameterization. -/
theorem tkkParamMap_eq_iff
    (p q : TKKRawParam) : tkkParamMap p = tkkParamMap q ↔ p = q := by
  constructor
  · exact tkkParamMap_injective
  · intro h
    exact congrArg tkkParamMap h

end InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66

