import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.Grp.Basic

namespace InfoGeometry.Algebra.TKK

/-- A Jordan Triple System signature -/
class JordanTripleSystem (J : Type*) [AddCommGroup J] where
  tripleProduct : J → J → J → J
  -- The main identity: {x, y, {u, v, w}} - {u, v, {x, y, w}} = {{x, y, u}, v, w} - {u, {y, x, v}, w}
  jordan_identity : ∀ x y u v w : J,
    tripleProduct x y (tripleProduct u v w) - tripleProduct u v (tripleProduct x y w) =
    tripleProduct (tripleProduct x y u) v w - tripleProduct u (tripleProduct y x v) w

/-- The 3-graded TKK decomposition spaces -/
structure TKKGrading (J : Type*) [AddCommGroup J] [JordanTripleSystem J] where
  g_neg1 : J
  g_0    : J → J → J 
  g_pos1 : J

end InfoGeometry.Algebra.TKK
