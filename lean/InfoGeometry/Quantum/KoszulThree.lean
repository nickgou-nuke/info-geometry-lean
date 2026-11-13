/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Three-generator Koszul maps with operator coefficients

The coefficients are commuting members of the generally noncommutative ring
`Module.End A M`. The degree-two coordinates use the cyclic order
`(e₂₃, e₃₁, e₁₂)`. These explicit maps implement equations (45)--(46) of
Hao Song, arXiv:2608.09913v1. No regularity or exactness is assumed here.
-/

namespace InfoGeometry.KoszulThree

universe u v

variable {A : Type u} {M : Type v}
variable [CommRing A] [AddCommGroup M] [Module A M]

/-- The degree-one differential, with coefficients acting on the left. -/
def d1 (F : Fin 3 → Module.End A M) : (Fin 3 → M) →ₗ[A] M :=
  (F 0).comp (LinearMap.proj 0) +
    (F 1).comp (LinearMap.proj 1) +
    (F 2).comp (LinearMap.proj 2)

/-- The signed degree-two differential in the cyclic basis `(e₂₃,e₃₁,e₁₂)`. -/
def d2 (F : Fin 3 → Module.End A M) : Module.End A (Fin 3 → M) :=
  LinearMap.pi ![
    (F 2).comp (LinearMap.proj 1) - (F 1).comp (LinearMap.proj 2),
    (F 0).comp (LinearMap.proj 2) - (F 2).comp (LinearMap.proj 0),
    (F 1).comp (LinearMap.proj 0) - (F 0).comp (LinearMap.proj 1)]

/-- The degree-three differential. -/
def d3 (F : Fin 3 → Module.End A M) : M →ₗ[A] (Fin 3 → M) :=
  LinearMap.pi F

@[simp] theorem d1_apply (F : Fin 3 → Module.End A M) (x : Fin 3 → M) :
    d1 F x = F 0 (x 0) + F 1 (x 1) + F 2 (x 2) := rfl

@[simp] theorem d2_apply_zero (F : Fin 3 → Module.End A M) (x : Fin 3 → M) :
    d2 F x 0 = F 2 (x 1) - F 1 (x 2) := rfl

@[simp] theorem d2_apply_one (F : Fin 3 → Module.End A M) (x : Fin 3 → M) :
    d2 F x 1 = F 0 (x 2) - F 2 (x 0) := rfl

@[simp] theorem d2_apply_two (F : Fin 3 → Module.End A M) (x : Fin 3 → M) :
    d2 F x 2 = F 1 (x 0) - F 0 (x 1) := rfl

@[simp] theorem d3_apply (F : Fin 3 → Module.End A M) (x : M) (i : Fin 3) :
    d3 F x i = F i x := rfl

/-- A pointwise consequence of commutation in the endomorphism ring. -/
theorem commute_apply (F : Fin 3 → Module.End A M)
    (hF : ∀ i j, Commute (F i) (F j)) (i j : Fin 3) (x : M) :
    F i (F j x) = F j (F i x) :=
  LinearMap.congr_fun (hF i j).eq x

/-- The first adjacent composite vanishes by pairwise operator commutation. -/
theorem d1_comp_d2 (F : Fin 3 → Module.End A M)
    (hF : ∀ i j, Commute (F i) (F j)) :
    (d1 F).comp (d2 F) = 0 := by
  apply LinearMap.ext
  intro x
  change F 0 (F 2 (x 1) - F 1 (x 2)) +
    F 1 (F 0 (x 2) - F 2 (x 0)) +
    F 2 (F 1 (x 0) - F 0 (x 1)) = 0
  simp only [map_sub]
  rw [commute_apply F hF 0 2, commute_apply F hF 0 1,
    commute_apply F hF 1 2]
  abel

/-- The second adjacent composite vanishes by pairwise operator commutation. -/
theorem d2_comp_d3 (F : Fin 3 → Module.End A M)
    (hF : ∀ i j, Commute (F i) (F j)) :
    (d2 F).comp (d3 F) = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i
  · change F 2 (F 1 x) - F 1 (F 2 x) = 0
    rw [commute_apply F hF 2 1, sub_self]
  · change F 0 (F 2 x) - F 2 (F 0 x) = 0
    rw [commute_apply F hF 0 2, sub_self]
  · change F 1 (F 0 x) - F 0 (F 1 x) = 0
    rw [commute_apply F hF 1 0, sub_self]

/-- A scalar coupling regarded as a column of endomorphisms. -/
def column (a : Fin 3 → A) : M →ₗ[A] (Fin 3 → M) :=
  LinearMap.pi fun i => a i • LinearMap.id

/-- The same scalar coupling regarded as a row of endomorphisms. -/
def row (a : Fin 3 → A) : (Fin 3 → M) →ₗ[A] M :=
  a 0 • LinearMap.proj 0 + a 1 • LinearMap.proj 1 + a 2 • LinearMap.proj 2

@[simp] theorem column_apply (a : Fin 3 → A) (x : M) (i : Fin 3) :
    column a x i = a i • x := rfl

@[simp] theorem row_apply (a : Fin 3 → A) (x : Fin 3 → M) :
    row a x = a 0 • x 0 + a 1 • x 1 + a 2 • x 2 := rfl

@[simp] theorem column_zero : column (A := A) (M := M) 0 = 0 := by
  ext x i
  simp

@[simp] theorem row_zero : row (A := A) (M := M) 0 = 0 := by
  ext x
  simp

/-- Scalar linearity supplies the off-diagonal chain identity. -/
theorem coupling_compatible (F : Fin 3 → Module.End A M) (a : Fin 3 → A) :
    (d1 F).comp (column a) = (row a).comp (d3 F) := by
  apply LinearMap.ext
  intro x
  change F 0 (a 0 • x) + F 1 (a 1 • x) + F 2 (a 2 • x) =
    a 0 • F 0 x + a 1 • F 1 x + a 2 • F 2 x
  simp only [map_smul]

end InfoGeometry.KoszulThree
