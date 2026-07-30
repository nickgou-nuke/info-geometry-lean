import Mathlib.Algebra.BigOperators.Intervals
import InfoGeometry.Algebra.CuntzN

open BigOperators

namespace CuntzAlgebra

variable {n : ℕ} {A : Type*} [Ring A] [StarRing A]

/-- Compatibility name for the generic Cuntz `Oₙ` owner. -/
abbrev CuntzIsometries (n : ℕ) (A : Type*) [Ring A] [StarRing A] :=
  InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := n) A

def rangeProj (c : CuntzIsometries n A) (i : Fin n) : A :=
  c.S i * star (c.S i)

theorem rangeProj_idem (c : CuntzIsometries n A) (i : Fin n) :
    rangeProj c i * rangeProj c i = rangeProj c i := by
  exact InfoGeometry.Algebra.Cuntz.range_projection_idempotent c i

theorem rangeProj_ortho (c : CuntzIsometries n A) {i j : Fin n} (h : i ≠ j) :
    rangeProj c i * rangeProj c j = 0 := by
  exact InfoGeometry.Algebra.Cuntz.range_projection_orthogonal c i j h

theorem isometry_delta (c : CuntzIsometries n A) (i j : Fin n) :
    star (c.S i) * c.S j = if i = j then 1 else 0 :=
  c.isometry i j

theorem rangeProj_sum (c : CuntzIsometries n A) :
    ∑ i : Fin n, rangeProj c i = 1 :=
  c.range_sum

end CuntzAlgebra
