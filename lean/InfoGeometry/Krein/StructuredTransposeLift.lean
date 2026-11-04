/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixDisplacement
import InfoGeometry.Algebra.MonarchFactorization
import InfoGeometry.Krein.ChiralTransposeLift

/-!
# Ordered routing obstructions in the doubled transpose representation

The weighted-displacement and two-stage product formulas are connected to the
existing chiral transpose lift. Reversing a route changes the sampled weights.
The second doubled sector records exactly that change. All matrices below have
real coefficients and arbitrary finite index types.
-/

noncomputable section

namespace InfoGeometry.Krein.StructuredTransposeLift

open Matrix
open InfoGeometry.Algebra.MatrixDisplacement
open InfoGeometry.Algebra.MonarchFactorization
open InfoGeometry.Krein.ChiralTransposeLift
open InfoGeometry.Core.IdempotencyDefect

section Displacement

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The doubled representation retains the full translated-weight order obstruction. -/
theorem frame_weighted_product_defect (g h : G) (d e : G → ℝ) :
    frame (lift (weightedShift g d) * lift (weightedShift h e) -
      lift (weightedShift g d * weightedShift h e)) =
      fromBlocks 0 0 0
        (weightedShift (g + h)
          (fun j => e (g + j) * d j - d (h + j) * e j)).transpose := by
  rw [frame_product_defect, weightedShift_mul, weightedShift_mul, add_comm h g,
    ← weightedShift_sub]

/-- An entrywise criterion, not an assumed commutation of the matrix factors. -/
theorem lift_weighted_mul_eq_iff (g h : G) (d e : G → ℝ) :
    lift (weightedShift g d) * lift (weightedShift h e) =
      lift (weightedShift g d * weightedShift h e) ↔
      ∀ j, d (h + j) * e j = e (g + j) * d j := by
  rw [lift_mul_eq_iff, weightedShift_commute_iff]

/-- Every finite doubled defect stage has the explicitly computed local coefficients. -/
theorem frame_iterate_bitStep (g : G) (hg : g + g = 0) (d e : G → ℝ) (k : ℕ) :
    let p := (bitDefectPair g)^[k] (d, e)
    frame (defect^[k] (lift (bitStep g d e))) =
      fromBlocks (bitStep g p.1 p.2) 0 0 (bitStep g p.1 p.2).transpose := by
  dsimp only
  rw [frame_defect_iterate_lift, iterate_bitStep g hg]

/-- Changing the doubled frame does not create a new routing scale in the readout. -/
theorem framed_iterate_bitStep_outside (g : G) (hg : g + g = 0) (d e : G → ℝ)
    (k : ℕ) (i j : G) (h0 : i ≠ j) (h1 : i ≠ g + j) :
    frame (defect^[k] (lift (bitStep g d e))) (Sum.inl i) (Sum.inl j) = 0 := by
  rw [frame_defect_iterate_lift]
  exact iterate_bitStep_apply_of_ne g hg d e k i j h0 h1

end Displacement

section Monarch

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Reversing the two stages samples different coarse and fine blocks. -/
theorem fineMix_mul_coarseMix_apply (L : J → Matrix I I ℝ) (R : I → Matrix J J ℝ)
    (i j : I) (a b : J) :
    (fineMix R * coarseMix L) (i, a) (j, b) = R i a b * L b i j := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, coarseMix_apply, fineMix_apply]
  simp [ite_mul, mul_ite]

/-- Exact lower-sector readout of the two-stage order obstruction. -/
theorem frame_monarch_product_defect_apply
    (L : J → Matrix I I ℝ) (R : I → Matrix J J ℝ)
    (i j : I) (a b : J) :
    frame (lift (coarseMix L) * lift (fineMix R) - lift (monarch L R))
        (Sum.inr (i, a)) (Sum.inr (j, b)) =
      R j b a * L a j i - L b j i * R i b a := by
  rw [monarch, frame_product_defect]
  change (fineMix R * coarseMix L) (j, b) (i, a) -
    monarch L R (j, b) (i, a) = _
  rw [fineMix_mul_coarseMix_apply, monarch_apply]

/-- The full doubled product agrees with the lift of the two-stage operator exactly
when every forward and reverse routing coefficient agrees. -/
theorem lift_monarch_mul_eq_iff (L : J → Matrix I I ℝ) (R : I → Matrix J J ℝ) :
    lift (coarseMix L) * lift (fineMix R) = lift (monarch L R) ↔
      ∀ (i j : I) (a b : J), L a i j * R j a b = R i a b * L b i j := by
  rw [monarch, lift_mul_eq_iff]
  constructor
  · intro h i j a b
    have he := congrArg (fun M : Matrix (I × J) (I × J) ℝ => M (i, a) (j, b)) h.eq
    change monarch L R (i, a) (j, b) = (fineMix R * coarseMix L) (i, a) (j, b) at he
    simpa only [monarch_apply, fineMix_mul_coarseMix_apply] using he
  · intro h
    show coarseMix L * fineMix R = fineMix R * coarseMix L
    ext ⟨i, a⟩ ⟨j, b⟩
    change monarch L R (i, a) (j, b) = (fineMix R * coarseMix L) (i, a) (j, b)
    rw [monarch_apply, fineMix_mul_coarseMix_apply]
    exact h i j a b

end Monarch

end InfoGeometry.Krein.StructuredTransposeLift
