import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitSpinFactorTKKParameterInjectivity

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66

lemma B10_neg_left (u v : V10) : B10 (-u) v = -B10 u v := by
  have := B10_smul_left (-1) u v
  simpa using this

lemma B10_add_left (u v w : V10) : B10 (u + v) w = B10 u w + B10 v w := by
  rw [show u + v = u - (-v) by abel, B10_sub_left, B10_neg_left, sub_neg_eq_add]

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
    unfold tkkParamFunction tkkParamAction pGen dGen rotGen kGen
    ext1
    · dsimp
      simp only [B10_add_left, add_mul]
      ring
    · ext1
      · dsimp
        simp only [smul_add]
        abel
      · dsimp
        simp only [B10_add_left]
        ring
  map_smul' a p := by
    rcases p with ⟨u, ⟨⟨lambda, A⟩, v⟩⟩
    funext x
    unfold tkkParamFunction tkkParamAction pGen dGen rotGen kGen
    ext1
    · dsimp
      simp only [B10_smul_left]
      ring
    · ext1
      · dsimp
        rw [smul_comm x.2.2 a u, smul_comm x.1 a v]
        simp only [smul_add, smul_zero]
      · dsimp
        simp only [B10_smul_left]
        ring

@[simp] theorem tkkParamMap_apply
    (u : V10) (lambda : ℝ) (A : Module.End ℝ V10) (v : V10) :
    tkkParamMap (u, ((lambda, A), v)) = tkkParamAction u lambda A v := rfl

/-- Full linear injectivity of the 3-graded TKK parameterization. -/
theorem tkkParamMap_injective : Function.Injective tkkParamMap :=
  tkkParamFunction_injective

/-- Equivalent pointwise injectivity statement for the underlying function
parameterization. -/
theorem tkkParamMap_eq_iff
    (p q : TKKRawParam) : tkkParamMap p = tkkParamMap q ↔ p = q :=
  tkkParamMap_injective.eq_iff

end InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66

