import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

/-!
# 5-Graded Iwasawa N-Sector Nilpotency

This module formally proves the structural property of the Iwasawa KAN decomposition
in the context of 5-graded Lie algebras (e.g., Tits-Kantor-Koecher closures of
Freudenthal-Kantor triple systems).

Specifically, it proves that the N-sector $\mathfrak{n} = \mathfrak{g}_1 \oplus \mathfrak{g}_2$
forms a Heisenberg-type 2-step nilpotent Lie algebra, satisfying:
1. $[\mathfrak{g}_1, \mathfrak{g}_2] = 0$
2. $[\mathfrak{g}_2, \mathfrak{g}_2] = 0$
3. $[[\mathfrak{g}_1, \mathfrak{g}_1], \mathfrak{g}_1] = 0$
4. $[[\mathfrak{n}, \mathfrak{n}], \mathfrak{n}] = 0$

This confirms the transition of the physical gauge potentials (Ramond-Ramond forms
in $\mathfrak{g}_1$ and B-field in $\mathfrak{g}_2$) into a strict 2-step nilpotent horocyclic group.
-/

namespace InfoGeometry.Algebra.FiveGradedIwasawa

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- The grade subspace projector constraint. `x` is in grade `j` if the Euler/dilaton
operator `h` scales it by `j`. -/
def InGrade (h : L) (j : ℝ) (x : L) : Prop := ⁅h, x⁆ = j • x

/-- Grade additivity under the Lie bracket. -/
theorem bracket_grade_add (h x y : L) (i j : ℝ)
    (hx : InGrade h i x) (hy : InGrade h j y) :
    InGrade h (i + j) ⁅x, y⁆ := by
  unfold InGrade at *
  rw [leibniz_lie, hx, hy]
  simp [add_smul]

/-- A Lie algebra is strictly 5-graded if all elements outside grades -2, -1, 0, 1, 2 are zero. -/
class IsFiveGraded (h : L) : Prop where
  grade_bound : ∀ (j : ℝ) (x : L), InGrade h j x → 
    (j ≠ -2 ∧ j ≠ -1 ∧ j ≠ 0 ∧ j ≠ 1 ∧ j ≠ 2) → x = 0

/-- The bracket of two elements in the unipotent shifts sector $\mathfrak{g}_1$ and $\mathfrak{g}_2$ vanishes. -/
theorem iwasawa_g1_g2_zero (h : L) [IsFiveGraded h] (x y : L)
    (hx : InGrade h 1 x) (hy : InGrade h 2 y) : ⁅x, y⁆ = 0 := by
  have h_b : InGrade h (1 + 2) ⁅x, y⁆ := bracket_grade_add h x y 1 2 hx hy
  apply IsFiveGraded.grade_bound (1 + 2) ⁅x, y⁆ h_b
  norm_num

/-- The bracket of two elements in the B-field sector $\mathfrak{g}_2$ vanishes. -/
theorem iwasawa_g2_g2_zero (h : L) [IsFiveGraded h] (x y : L)
    (hx : InGrade h 2 x) (hy : InGrade h 2 y) : ⁅x, y⁆ = 0 := by
  have h_b : InGrade h (2 + 2) ⁅x, y⁆ := bracket_grade_add h x y 2 2 hx hy
  apply IsFiveGraded.grade_bound (2 + 2) ⁅x, y⁆ h_b
  norm_num

/-- The lower central series terminates at step 2 for the pure Ramond-Ramond sector. -/
theorem iwasawa_g1_step2 (h : L) [IsFiveGraded h] (x y z : L)
    (hx : InGrade h 1 x) (hy : InGrade h 1 y) (hz : InGrade h 1 z) :
    ⁅⁅x, y⁆, z⁆ = 0 := by
  have hxy : InGrade h (1 + 1) ⁅x, y⁆ := bracket_grade_add h x y 1 1 hx hy
  have hxyz : InGrade h (1 + 1 + 1) ⁅⁅x, y⁆, z⁆ := bracket_grade_add h ⁅x, y⁆ z (1 + 1) 1 hxy hz
  apply IsFiveGraded.grade_bound (1 + 1 + 1) ⁅⁅x, y⁆, z⁆ hxyz
  norm_num

/-- The complete Iwasawa N-sector $\mathfrak{n} = \mathfrak{g}_1 \oplus \mathfrak{g}_2$ is a 2-step nilpotent Lie algebra.
Here shown by linearity over the composite grading shifts. -/
theorem iwasawa_n_sector_nilpotent (h : L) [IsFiveGraded h] 
    (x1 x2 y1 y2 z1 z2 : L)
    (hx1 : InGrade h 1 x1) (hx2 : InGrade h 2 x2)
    (hy1 : InGrade h 1 y1) (hy2 : InGrade h 2 y2)
    (hz1 : InGrade h 1 z1) (hz2 : InGrade h 2 z2) :
    ⁅⁅x1 + x2, y1 + y2⁆, z1 + z2⁆ = 0 := by
  rw [lie_add, add_lie, add_lie, lie_add, lie_add]
  have h12 : ⁅x1, y2⁆ = 0 := iwasawa_g1_g2_zero h x1 y2 hx1 hy2
  have h21 : ⁅x2, y1⁆ = 0 := by
    rw [← lie_skew, iwasawa_g1_g2_zero h y1 x2 hy1 hx2, neg_zero]
  have h22 : ⁅x2, y2⁆ = 0 := iwasawa_g2_g2_zero h x2 y2 hx2 hy2
  rw [h12, h21, h22]
  simp only [add_zero, zero_add]
  rw [lie_add]
  have h_z1 : ⁅⁅x1, y1⁆, z1⁆ = 0 := iwasawa_g1_step2 h x1 y1 z1 hx1 hy1 hz1
  have h_z2 : ⁅⁅x1, y1⁆, z2⁆ = 0 := by
    have h11 : InGrade h (1 + 1) ⁅x1, y1⁆ := bracket_grade_add h x1 y1 1 1 hx1 hy1
    change InGrade h 2 ⁅x1, y1⁆ at h11
    exact iwasawa_g2_g2_zero h ⁅x1, y1⁆ z2 h11 hz2
  rw [h_z1, h_z2, add_zero]

end InfoGeometry.Algebra.FiveGradedIwasawa
