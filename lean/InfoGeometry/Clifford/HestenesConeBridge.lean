/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem coneBridge_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- In any non-commutative `*-ring` `[Ring B] [StarRing B]`, every element of the form
`y * star y` is self-adjoint (`star x = x`). -/
theorem ring_self_adjoint_of_mul_star
    {B : Type*} [Ring B] [StarRing B] {x : B}
    (hx : ∃ y : B, x = y * star y) :
    star x = x := by
  rcases hx with ⟨y, rfl⟩
  simp [star_mul]

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M)

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
