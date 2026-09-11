import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/--
Транспортният мост (Cone Bridge).
Това е формализираният архитектурен факт, че трите конуса:
1. Бъдещият светлинен конус (Future Lorentz Cone) - C^+
2. Конусът на позитивно дефинитните Ермитови паравектори (Jordan Positive Cone) - H_2(C)_+
3. Естественият конус на стандартната форма (Natural Cone) - \mathcal{P}

са изоморфни проявления на една и съща геометрична структура, обединени чрез Hestenes паравекторния формализъм.
-/
theorem future_lorentz_cone_eq_natural_cone (X : HestenesSelfAdjoint Q v0) :
    X ∈ FutureLorentzCone Q v0 ↔ X.val ∈ NaturalCone Q v0 := by
  dsimp [FutureLorentzCone, NaturalCone, L_action, J_mod]
  apply Iff.intro
  · rintro ⟨Y, hY⟩
    use Y
    apply Subtype.ext
    exact hY
  · rintro ⟨Y, hY⟩
    use Y
    exact congrArg Subtype.val hY

end InfoGeometry.Clifford.Hestenes
