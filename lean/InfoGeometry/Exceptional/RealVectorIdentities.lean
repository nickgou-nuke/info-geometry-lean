import InfoGeometry.Exceptional.SplitOctonionZornReal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

namespace InfoGeometry.Exceptional.RealZorn

@[ext]
lemma Vec3Real.ext_local (u v : Vec3Real) (h1 : u.1 = v.1) (h2 : u.2.1 = v.2.1) (h3 : u.2.2 = v.2.2) : u = v := by
  rcases u with ⟨u1, u21, u22⟩
  rcases v with ⟨v1, v21, v22⟩
  dsimp at h1 h2 h3
  rw [h1, h2, h3]

theorem dot_cross_self (u x : Vec3Real) : dot u (cross u x) = 0 := by
  obtain ⟨u1, u21, u22⟩ := u
  obtain ⟨x1, x21, x22⟩ := x
  dsimp [dot, cross, smul, sub, add]
  ring

theorem cross_anti_comm (u v : Vec3Real) : cross u v = smul (-1) (cross v u) := by
  obtain ⟨u1, u21, u22⟩ := u
  obtain ⟨v1, v21, v22⟩ := v
  apply Vec3Real.ext_local <;> (dsimp [dot, cross, smul, sub, add]; ring)

theorem cross_cross_bac_cab (u v w : Vec3Real) : cross u (cross v w) = sub (smul (dot u w) v) (smul (dot u v) w) := by
  obtain ⟨u1, u21, u22⟩ := u
  obtain ⟨v1, v21, v22⟩ := v
  obtain ⟨w1, w21, w22⟩ := w
  apply Vec3Real.ext_local <;> (dsimp [dot, cross, smul, sub, add]; ring)

end InfoGeometry.Exceptional.RealZorn
