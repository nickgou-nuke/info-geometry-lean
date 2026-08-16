import Mathlib.Tactic
import InfoGeometry.Canonical.Pin55WeylWallpaper
import InfoGeometry.Clifford.Clifford55

/-!
# Finite `(5,5)` reflection restriction

This module is only a finite reflection restriction.  The authoritative
quadratic carrier and native Pin group are `Clifford55.V55`, `Q55`, and
`Clifford55.Pin55`; no new orthogonal group, Pin group, quotient, or exact
sequence is defined here.
-/

noncomputable section

namespace InfoGeometry.Canonical.Pin55

open InfoGeometry.Canonical.Pin55WeylWallpaper
open InfoGeometry.Clifford.Clifford55

/-! The legacy names below are readouts of the native `Clifford55` carrier. -/

abbrev Split10D := V55

def splitPair55 (v w : Split10D) : ℝ :=
  dot_product v.1 w.1 - dot_product v.2 w.2

def quadratic_form_5_5 (v : Split10D) : ℝ := splitPair55 v v

/-- 
A candidate linear isometry of the split `(5,5)` quadratic space.
-/
def FormPreservingLinearMap55 : Type :=
  {f : Split10D →ₗ[ℝ] Split10D // ∀ v, quadratic_form_5_5 (f v) = quadratic_form_5_5 v}

/-!
### 2. Cl(5,5) and Pin(5,5)
-/

variable {Cl55' : Type*} [Ring Cl55'] [Algebra ℝ Cl55']
         (clifford_embed : Split10D →ₗ[ℝ] Cl55')

/-- The fundamental Clifford identity v * v = Q(v) * 1. -/
def CliffordGeneratorRelation55 : Prop :=
  ∀ v, clifford_embed v * clifford_embed v =
    algebraMap ℝ Cl55' (quadratic_form_5_5 v)

/-! The native Pin group is owned by `Clifford55`; this file adds no local
    generated predicate for it. -/

def scaleTorus (c : ℝ) (x : Torus5D) : Torus5D :=
  fun i => c * x i

def subTorus (x y : Torus5D) : Torus5D :=
  fun i => x i - y i

/-- Totalized split-pair reflection formula.  Its isometry theorem below
    requires a non-isotropic normal. -/
def orthogonalReflection55
    (n : Split10D) (hn : quadratic_form_5_5 n ≠ 0) (v : Split10D) : Split10D :=
  let c := 2 * (dot_product v.1 n.1 - dot_product v.2 n.2) /
    quadratic_form_5_5 n
  (subTorus v.1 (scaleTorus c n.1), subTorus v.2 (scaleTorus c n.2))

theorem splitPair55_self (v : Split10D) :
    splitPair55 v v = quadratic_form_5_5 v := by
  aesop (add simp [splitPair55, quadratic_form_5_5])

theorem quadratic_form_5_5_eq_Q55 (v : Split10D) :
    quadratic_form_5_5 v = Q55 v := by
  simp [quadratic_form_5_5, splitPair55, Q55_apply, dot_product,
    Fin.sum_univ_succ]
  ring

theorem q55_sub_scale
    (x y a b : Torus5D) (c : ℝ) :
    quadratic_form_5_5
        (subTorus x (scaleTorus c a), subTorus y (scaleTorus c b)) =
      quadratic_form_5_5 (x, y) - 2 * c * splitPair55 (x, y) (a, b) +
        c ^ 2 * splitPair55 (a, b) (a, b) := by
  simp [quadratic_form_5_5, subTorus, scaleTorus, splitPair55, dot_product,
    sub_eq_add_neg]
  ring

theorem orthogonalReflection55_preserves_form
    (n v : Split10D) (hn : quadratic_form_5_5 n ≠ 0) :
    quadratic_form_5_5 (orthogonalReflection55 n hn v) = quadratic_form_5_5 v := by
  have h_pair : dot_product v.1 n.1 - dot_product v.2 n.2 = splitPair55 v n := rfl
  have h_scale := q55_sub_scale v.1 v.2 n.1 n.2
    (2 * (dot_product v.1 n.1 - dot_product v.2 n.2) / quadratic_form_5_5 n)
  have h_self : splitPair55 (n.1, n.2) (n.1, n.2) = quadratic_form_5_5 n := rfl
  rw [orthogonalReflection55]
  rw [h_scale]
  rw [h_pair, h_self]
  field_simp [hn]
  ring

def alpha12Split : Split10D := (alpha_12, fun _ => 0)

theorem alpha12Split_nonisotropic : quadratic_form_5_5 alpha12Split ≠ 0 := by
  intro h
  have hq : quadratic_form_5_5 alpha12Split = 2 := by
    simp [alpha12Split, quadratic_form_5_5, splitPair55, alpha_12,
      dot_product]
    ring
  rw [hq] at h
  norm_num at h

/-! The positive `D₅` split reflection restricts to the native Weyl reflection. -/
theorem alpha12_split_reflection_eq_weyl_reflection (v : Torus5D) :
    (orthogonalReflection55 alpha12Split alpha12Split_nonisotropic
      (v, fun _ => 0)).1 = weyl_reflect v alpha_12 := by
  have h0 : dot_product (fun _ : Fin 5 => (0 : ℝ)) (fun _ : Fin 5 => (0 : ℝ)) = 0 := by
    simp [dot_product]
  have hQ : quadratic_form_5_5 (alpha_12, fun _ => 0) = dot_product alpha_12 alpha_12 := by
    simp [quadratic_form_5_5, splitPair55, h0]
  unfold orthogonalReflection55 alpha12Split weyl_reflect subTorus scaleTorus
  dsimp
  rw [h0, sub_zero, hQ]
  funext i
  ring

theorem alpha12_split_reflection_orthogonal (v : Torus5D) :
    (orthogonalReflection55 alpha12Split alpha12Split_nonisotropic
      (v, fun _ => 0)).2 = fun _ => 0 := by
  unfold orthogonalReflection55 alpha12Split subTorus scaleTorus
  ext i
  simp

end InfoGeometry.Canonical.Pin55
