import InfoGeometry.Algebra.SplitCayleyF2
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.SplitCayleyF2

theorem delta1_mul_alpha_structural (r : Vec3) (x y : Cayley) :
    (delta1 r (x * y)).α = (delta1 r x * delta1 r y).α := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      change (delta1 r (mul {α := xa, u := xu, v := xv, β := xb}
        {α := ya, u := yu, v := yv, β := yb})).α =
        (mul (delta1 r {α := xa, u := xu, v := xv, β := xb})
          (delta1 r {α := ya, u := yu, v := yv, β := yb})).α
      simp [delta1, mul, dot, cross]
      ring

theorem delta1_mul_beta_structural (r : Vec3) (x y : Cayley) :
    (delta1 r (x * y)).β = (delta1 r x * delta1 r y).β := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      change (delta1 r (mul {α := xa, u := xu, v := xv, β := xb}
        {α := ya, u := yu, v := yv, β := yb})).β =
        (mul (delta1 r {α := xa, u := xu, v := xv, β := xb})
          (delta1 r {α := ya, u := yu, v := yv, β := yb})).β
      simp [delta1, mul, dot, cross]
      ring

theorem delta1_mul_u_structural (r : Vec3) (x y : Cayley) :
    (delta1 r (x * y)).u = (delta1 r x * delta1 r y).u := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      change (delta1 r (mul {α := xa, u := xu, v := xv, β := xb}
        {α := ya, u := yu, v := yv, β := yb})).u =
        (mul (delta1 r {α := xa, u := xu, v := xv, β := xb})
          (delta1 r {α := ya, u := yu, v := yv, β := yb})).u
      funext i
      fin_cases i <;> simp [delta1, mul, dot, cross]
      all_goals ring

theorem delta1_mul_v_structural (r : Vec3) (x y : Cayley) :
    (delta1 r (x * y)).v = (delta1 r x * delta1 r y).v := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      change (delta1 r (mul {α := xa, u := xu, v := xv, β := xb}
        {α := ya, u := yu, v := yv, β := yb})).v =
        (mul (delta1 r {α := xa, u := xu, v := xv, β := xb})
          (delta1 r {α := ya, u := yu, v := yv, β := yb})).v
      funext i
      fin_cases i <;> simp [delta1, mul, dot, cross]
      all_goals ring

theorem delta1_mul_structural (r : Vec3) (x y : Cayley) :
    delta1 r (x * y) = delta1 r x * delta1 r y := by
  apply Cayley.ext
  · exact delta1_mul_alpha_structural r x y
  · exact delta1_mul_u_structural r x y
  · exact delta1_mul_v_structural r x y
  · exact delta1_mul_beta_structural r x y

end InfoGeometry.Algebra.SplitCayleyF2
