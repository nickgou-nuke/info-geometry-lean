import InfoGeometry.Algebra.SplitCayleyF2
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.SplitCayleyF2

theorem delta2_mul_alpha_structural (r : Vec3) (x y : Cayley) :
    (delta2 r (x * y)).α = (delta2 r x * delta2 r y).α := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      have hneg : ∀ a : Scalar, -a = a := by
        intro a
        fin_cases a <;> rfl
      have htwo : (2 : Scalar) = 0 := CharP.cast_eq_zero Scalar 2
      change (delta2 r (mul {α := xa, u := xu, v := xv, β := xb}
        {α := ya, u := yu, v := yv, β := yb})).α =
        (mul (delta2 r {α := xa, u := xu, v := xv, β := xb})
          (delta2 r {α := ya, u := yu, v := yv, β := yb})).α
      simp [delta2, mul, dot, cross]
      ring_nf
      simp [htwo]

theorem delta2_mul_beta_structural (r : Vec3) (x y : Cayley) :
    (delta2 r (x * y)).β = (delta2 r x * delta2 r y).β := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      have hneg : ∀ a : Scalar, -a = a := by
        intro a
        fin_cases a <;> rfl
      change (delta2 r (mul {α := xa, u := xu, v := xv, β := xb}
        {α := ya, u := yu, v := yv, β := yb})).β =
        (mul (delta2 r {α := xa, u := xu, v := xv, β := xb})
          (delta2 r {α := ya, u := yu, v := yv, β := yb})).β
      simp [delta2, mul, dot, cross]
      ring_nf
      simp [sub_eq_add_neg]
      ring

theorem delta2_mul_u_structural (r : Vec3) (x y : Cayley) :
    (delta2 r (x * y)).u = (delta2 r x * delta2 r y).u := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      have htwo : (2 : Scalar) = 0 := CharP.cast_eq_zero Scalar 2
      have hneg : ∀ a : Scalar, -a = a := by
        intro a
        fin_cases a <;> rfl
      change (delta2 r (mul {α := xa, u := xu, v := xv, β := xb}
        {α := ya, u := yu, v := yv, β := yb})).u =
        (mul (delta2 r {α := xa, u := xu, v := xv, β := xb})
          (delta2 r {α := ya, u := yu, v := yv, β := yb})).u
      funext i
      fin_cases i <;> simp [delta2, mul, dot, cross]
      all_goals ring_nf
      all_goals simp only [sub_eq_add_neg]
      all_goals simp only [hneg, htwo]
      all_goals ring

theorem delta2_mul_v_structural (r : Vec3) (x y : Cayley) :
    (delta2 r (x * y)).v = (delta2 r x * delta2 r y).v := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      have htwo : (2 : Scalar) = 0 := CharP.cast_eq_zero Scalar 2
      have hneg : ∀ a : Scalar, -a = a := by
        intro a
        fin_cases a <;> rfl
      change (delta2 r (mul {α := xa, u := xu, v := xv, β := xb}
        {α := ya, u := yu, v := yv, β := yb})).v =
        (mul (delta2 r {α := xa, u := xu, v := xv, β := xb})
          (delta2 r {α := ya, u := yu, v := yv, β := yb})).v
      funext i
      fin_cases i <;> simp [delta2, mul, dot, cross]
      all_goals ring_nf
      all_goals simp only [sub_eq_add_neg]
      all_goals simp only [hneg, htwo]
      all_goals ring

theorem delta2_mul_structural (r : Vec3) (x y : Cayley) :
    delta2 r (x * y) = delta2 r x * delta2 r y := by
  apply Cayley.ext
  · exact delta2_mul_alpha_structural r x y
  · exact delta2_mul_u_structural r x y
  · exact delta2_mul_v_structural r x y
  · exact delta2_mul_beta_structural r x y

end InfoGeometry.Algebra.SplitCayleyF2
