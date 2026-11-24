/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Nondegeneracy on an order-three fixed submodule

For a real endomorphism `A` with `A³ = 1`, preservation of a nondegenerate
bilinear form implies nondegeneracy of its restriction to `A.fixedSubmodule`.
The proof uses the fixed orbit sum `y + A y + A (A y)` and works without a
finite-dimensional hypothesis. This is a linear-algebra result, not a smooth
fixed-submanifold or symplectic-groupoid construction.
-/

noncomputable section

namespace InfoGeometry.Algebraic.OrderThreeFixedForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem eq_zero_of_three_sum (r : ℝ) (h : r + r + r = 0) : r = 0 := by
  linarith

/-- The unnormalised orbit sum lies in the native fixed submodule. -/
theorem orbitSum_mem_fixedSubmodule (A : Module.End ℝ V) (hA : A ^ 3 = 1)
    (y : V) : y + A y + A (A y) ∈ A.fixedSubmodule := by
  have hcycle : A (A (A y)) = y := by
    have h := congrArg (fun f : Module.End ℝ V => f y) hA
    simpa only [pow_succ, pow_zero, Module.End.mul_apply,
      Module.End.one_apply] using h
  change A (y + A y + A (A y)) = y + A y + A (A y)
  rw [map_add, map_add, hcycle]
  abel

/-- A left radical vector of the restricted form is already in the ambient
left radical, because pairing against an orbit sum multiplies by three. -/
theorem separatingLeft_restrict_fixedSubmodule
    (B : LinearMap.BilinForm ℝ V) (hB : B.SeparatingLeft)
    (A : Module.End ℝ V) (hA : A ^ 3 = 1)
    (hpres : ∀ x y, B (A x) (A y) = B x y) :
    (B.restrict A.fixedSubmodule).SeparatingLeft := by
  intro x hx
  apply Subtype.ext
  apply hB x.val
  intro y
  have hfixed : A x.val = x.val := x.property
  have hfirst : B x.val (A y) = B x.val y := by
    simpa only [hfixed] using hpres x.val y
  have hsecond : B x.val (A (A y)) = B x.val y := by
    have h := hpres x.val (A y)
    simpa only [hfixed, hfirst] using h
  have hsum := hx ⟨y + A y + A (A y), orbitSum_mem_fixedSubmodule A hA y⟩
  change B x.val (y + A y + A (A y)) = 0 at hsum
  rw [map_add, map_add, hfirst, hsecond] at hsum
  exact eq_zero_of_three_sum (B x.val y) hsum

/-- Order dividing three is a sufficient hypothesis for nondegeneracy of
the fixed restriction. Preservation alone is not sufficient. -/
theorem nondegenerate_restrict_fixedSubmodule
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (A : Module.End ℝ V) (hA : A ^ 3 = 1)
    (hpres : ∀ x y, B (A x) (A y) = B x y) :
    (B.restrict A.fixedSubmodule).Nondegenerate := by
  constructor
  · exact separatingLeft_restrict_fixedSubmodule B hB.1 A hA hpres
  · exact separatingLeft_restrict_fixedSubmodule B.flip hB.2 A hA
      (fun x y => hpres y x)

/-- The same fixed restriction remains alternating when the ambient form is
alternating. Together with the preceding theorem this gives the algebraic
symplectic conclusion with its actual finite-order hypothesis. -/
theorem isAlt_restrict_fixedSubmodule
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsAlt) (A : Module.End ℝ V) :
    (B.restrict A.fixedSubmodule).IsAlt := by
  intro x
  exact hB x.val

end InfoGeometry.Algebraic.OrderThreeFixedForm
