import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace CuntzK0TorsionRelation

/-- If a class `u` is equal to a sum of `n+1` copies of itself, then `n • u = 0`.
This is the algebraic core of the Cuntz `K₀` torsion relation: the range
projection partition gives `[1] = (n+1)[1]`, hence `n[1]=0`. -/
theorem torsion_of_succ_nsmul_eq_self {K : Type*} [AddCommGroup K]
    (n : ℕ) (u : K) (h : (n + 1) • u = u) :
    n • u = 0 := by
  have h' : n • u + u = u := by
    change AddMonoid.nsmul (n + 1) u = u at h
    rw [AddMonoid.nsmul_succ] at h
    exact h
  have h'' : n • u + u = 0 + u := by simpa using h'
  exact add_right_cancel h''

/-- Equivalent orientation of the same relation: `[1]=(n+1)[1]` implies `n[1]=0`. -/
theorem torsion_of_self_eq_succ_nsmul {K : Type*} [AddCommGroup K]
    (n : ℕ) (u : K) (h : u = (n + 1) • u) :
    n • u = 0 := by
  exact torsion_of_succ_nsmul_eq_self n u h.symm

/-- For `𝒪₂`, the relation `[1]=2[1]` forces `[1]=0`. -/
theorem O2_unit_torsion {K : Type*} [AddCommGroup K] (u : K)
    (h : u = (2 : ℕ) • u) :
    u = 0 := by
  have h1 : (1 : ℕ) • u = 0 := torsion_of_self_eq_succ_nsmul 1 u (by simpa using h)
  simpa using h1

/-- For `𝒪ₙ` with `N+1` Cuntz isometries, the unit class is `N`-torsion. -/
theorem Cuntz_unit_torsion_from_partition {K : Type*} [AddCommGroup K]
    (N : ℕ) (unitClass : K)
    (h_partition_class : unitClass = (N + 1) • unitClass) :
    N • unitClass = 0 := by
  exact torsion_of_self_eq_succ_nsmul N unitClass h_partition_class

#check torsion_of_succ_nsmul_eq_self
#check torsion_of_self_eq_succ_nsmul
#check O2_unit_torsion
#check Cuntz_unit_torsion_from_partition

end CuntzK0TorsionRelation
