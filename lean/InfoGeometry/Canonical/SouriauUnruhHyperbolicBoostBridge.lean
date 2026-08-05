import Mathlib

noncomputable section

namespace InfoGeometry.Canonical

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **1. Дефиниция на Хиперболичен / Лоренцов Генератор K**:
    Удовлетворява K² = I (аналог на хиперболичната единица ε² = +1). -/
def HyperbolicBoostGenerator (K : Module.End ℝ V) : Prop :=
  K.comp K = LinearMap.id

/-- **2. 1-Параметричен Лоренцов Буст Оператор U(η) = cosh(η) I + sinh(η) K**:
    Генерира хиперболични ротации с бързина (rapidity) η. -/
def boostOp (K : Module.End ℝ V) (eta : ℝ) : Module.End ℝ V :=
  (Real.cosh eta) • LinearMap.id + (Real.sinh eta) • K

/-- **3. Сурио-Унру Gibbs Плътностен Оператор ρ_Unruh(η) = U(-η)**:
    Термодинамичният Gibbs фактор e^{-η K} за ускорен наблюдател. -/
def souriauUnruhGibbsOp (K : Module.End ℝ V) (eta : ℝ) : Module.End ℝ V :=
  boostOp K (-eta)

/-- **Теорема 1**: Групов Хомоморфизъм на Лоренцовите Бустове U(η₁) ∘ U(η₂) = U(η₁ + η₂).
    Доказано алгебрично чрез K² = I и хиперболичните тригонометрични тъждества за сума. -/
theorem boostOp_add
    (K : Module.End ℝ V) (hK : HyperbolicBoostGenerator K) (eta1 eta2 : ℝ) :
    (boostOp K eta1).comp (boostOp K eta2) = boostOp K (eta1 + eta2) := by
  dsimp [boostOp]
  ext x
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply]
  have hK_apply : K (K x) = x := by
    have h_comp := LinearMap.congr_fun hK x
    exact h_comp
  rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul, hK_apply]
  rw [Real.cosh_add, Real.sinh_add]
  module

/-- **Теорема 2**: Инверсивност на Буста U(η) ∘ U(-η) = I.
    Връщането назад по време в Rindler клина възстановява идентитета. -/
theorem boostOp_inverse
    (K : Module.End ℝ V) (hK : HyperbolicBoostGenerator K) (eta : ℝ) :
    (boostOp K eta).comp (souriauUnruhGibbsOp K eta) = LinearMap.id := by
  dsimp [souriauUnruhGibbsOp]
  rw [boostOp_add K hK, add_neg_cancel, boostOp]
  simp only [Real.cosh_zero, Real.sinh_zero, one_smul, zero_smul, add_zero]

end InfoGeometry.Canonical
