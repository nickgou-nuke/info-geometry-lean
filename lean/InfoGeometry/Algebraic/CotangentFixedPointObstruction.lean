/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebraic.CotangentFormTransport

/-!
# A degenerate fixed subspace of a cotangent lift

The shear `(x,y) ↦ (x+y,y)` is an actual real linear equivalence.
Its existing cotangent lift preserves the full nondegenerate alternating form,
but the restriction to its native fixed submodule is degenerate. This prevents
promotion of arbitrary fixed-arrow closure to a symplectic fixed subgroupoid.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CotangentFixedPointObstruction

open CotangentBilinearGraph CotangentFormTransport
open InfoGeometry.Twistor.RealDualTwistor

/-- A nontrivial unipotent linear equivalence on the real plane. -/
def planeShear : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (x.1 + x.2, x.2)
  invFun x := (x.1 - x.2, x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp [add_add_add_comm]
  map_smul' r x := by ext <;> simp [smul_add]

/-- The fixed vectors are the kernel of the lift minus the identity. -/
def fixedCotangentSubmodule : Submodule ℝ (Carrier (ℝ × ℝ)) :=
  LinearMap.ker ((frameAction planeShear).toLinearMap - LinearMap.id)

theorem mem_fixedCotangentSubmodule_iff (p : Carrier (ℝ × ℝ)) :
    p ∈ fixedCotangentSubmodule ↔ frameAction planeShear p = p := by
  change frameAction planeShear p - p = 0 ↔ _
  exact sub_eq_zero

/-- Evaluating a fixed covector on a moving vector forces it to annihilate
the nonzero fixed direction `(1,0)`. -/
theorem fixed_covector_annihilates_horizontal (p : Carrier (ℝ × ℝ))
    (hp : frameAction planeShear p = p) : p.2 (1, 0) = 0 := by
  have h := congrArg (fun q : Carrier (ℝ × ℝ) => q.2 (0, 1)) hp
  change p.2 ((0 : ℝ) - 1, 1) = p.2 (0, 1) at h
  rw [zero_sub] at h
  have hdecomp : (-1, 1) = -(1, 0) + (0, 1 : ℝ × ℝ) := by
    ext <;> norm_num
  rw [hdecomp, map_add, map_neg] at h
  have hz : -p.2 (1, 0) = 0 :=
    add_right_cancel (h.trans (zero_add _).symm)
  exact neg_eq_zero.mp hz

/-- The obstruction occurs although the full form is preserved. -/
theorem planeShear_preserves_cotangentForm (p q : Carrier (ℝ × ℝ)) :
    cotangentForm (0 : LinearMap.BilinForm ℝ (ℝ × ℝ))
      (frameAction planeShear p) (frameAction planeShear q) =
        cotangentForm 0 p q := by
  apply cotangentForm_frameAction
  intro x y
  rfl

/-- The fixed subspace contains a nonzero vector in the left radical of the
restricted canonical form, so the restriction is not nondegenerate. -/
theorem fixedCotangentForm_not_nondegenerate :
    ¬((cotangentForm (0 : LinearMap.BilinForm ℝ (ℝ × ℝ))).restrict
      fixedCotangentSubmodule).Nondegenerate := by
  let u : Carrier (ℝ × ℝ) := ((1, 0), 0)
  have hu : u ∈ fixedCotangentSubmodule := by
    rw [mem_fixedCotangentSubmodule_iff]
    apply Prod.ext
    · change (1 + 0, 0 : ℝ × ℝ) = (1, 0)
      simp
    · ext x
      rfl
  let uFixed : fixedCotangentSubmodule := ⟨u, hu⟩
  have hne : uFixed ≠ 0 := by
    intro h
    have hcoord := congrArg (fun p : fixedCotangentSubmodule => p.val.1.1) h
    change (1 : ℝ) = 0 at hcoord
    exact one_ne_zero hcoord
  intro hnondeg
  apply hne
  apply hnondeg.1
  intro q
  have hq := fixed_covector_annihilates_horizontal q.val
    ((mem_fixedCotangentSubmodule_iff q.val).mp q.property)
  change q.val.2 (1, 0) - 0 + 0 = 0
  simpa only [sub_zero, add_zero] using hq

end InfoGeometry.Algebraic.CotangentFixedPointObstruction
