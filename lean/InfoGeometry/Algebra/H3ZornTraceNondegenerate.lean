/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornJordanIdentity
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Nondegeneracy of the full split Albert trace pairing

The proof first separates all eight Zorn coordinates using the standard
idempotent and upper/lower vector probes.  It then separates the three scalar
coordinates and all three arbitrary Zorn coordinates of the Albert carrier.
No restriction to diagonal Albert elements is made.
-/

namespace InfoGeometry.Algebra

namespace ZornVectorMatrix

variable {R : Type*} [CommRing R]

/-- The conjugated trace pairing separates every Zorn coordinate. -/
theorem eq_zero_of_trace_mul_conj_eq_zero (X : ZornVectorMatrix R)
    (h : ∀ Y : ZornVectorMatrix R, trace (mul X (conj Y)) = 0) :
    X = 0 := by
  have ha : X.a = 0 := by
    simpa [trace, mul, conj, E22] using h E22
  have hb : X.b = 0 := by
    simpa [trace, mul, conj, E11] using h E11
  have hv : ∀ i : Fin 3, X.v i = 0 := by
    intro i
    have hi : -X.v i = 0 := by
      simpa [trace, mul, conj, V, ZornVec3.dot_neg_right] using h (V i)
    exact neg_eq_zero.mp hi
  have hw : ∀ i : Fin 3, X.w i = 0 := by
    intro i
    have hi : -X.w i = 0 := by
      simpa [trace, mul, conj, U, ZornVec3.dot_neg_right] using h (U i)
    exact neg_eq_zero.mp hi
  apply ZornVectorMatrix.ext
  · exact ha
  · funext i
    exact hv i
  · funext i
    exact hw i
  · exact hb

end ZornVectorMatrix

namespace H3Zorn

variable {R : Type*} [CommRing R]

/-- The full split Albert trace pairing is nondegenerate in its first slot. -/
theorem eq_zero_of_traceBilin_left (X : H3Zorn R)
    (h : ∀ Y : H3Zorn R, traceBilin X Y = 0) : X = 0 := by
  apply ext_h3
  · change X.α₁ = 0
    simpa [traceBilin] using h ⟨1, 0, 0, 0, 0, 0⟩
  · change X.α₂ = 0
    simpa [traceBilin] using h ⟨0, 1, 0, 0, 0, 0⟩
  · change X.α₃ = 0
    simpa [traceBilin] using h ⟨0, 0, 1, 0, 0, 0⟩
  · change X.a = 0
    apply ZornVectorMatrix.eq_zero_of_trace_mul_conj_eq_zero
    intro Y
    simpa [traceBilin] using h ⟨0, 0, 0, Y, 0, 0⟩
  · change X.b = 0
    apply ZornVectorMatrix.eq_zero_of_trace_mul_conj_eq_zero
    intro Y
    simpa [traceBilin] using h ⟨0, 0, 0, 0, Y, 0⟩
  · change X.c = 0
    apply ZornVectorMatrix.eq_zero_of_trace_mul_conj_eq_zero
    intro Y
    simpa [traceBilin] using h ⟨0, 0, 0, 0, 0, Y⟩

/-- Symmetry gives nondegeneracy in the second slot as well. -/
theorem eq_zero_of_traceBilin_right (X : H3Zorn R)
    (h : ∀ Y : H3Zorn R, traceBilin Y X = 0) : X = 0 := by
  apply eq_zero_of_traceBilin_left X
  intro Y
  rw [traceBilin_symm]
  exact h Y

/-- Equality of all trace pairings determines an arbitrary Albert element. -/
theorem eq_of_traceBilin_left_eq (X Y : H3Zorn R)
    (h : ∀ Z : H3Zorn R, traceBilin X Z = traceBilin Y Z) : X = Y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_traceBilin_left (X - Y)
  intro Z
  rw [traceBilin_sub_left, h Z, sub_self]

/-- Equality of all pairings in the other slot also determines the element. -/
theorem eq_of_traceBilin_right_eq (X Y : H3Zorn R)
    (h : ∀ Z : H3Zorn R, traceBilin Z X = traceBilin Z Y) : X = Y := by
  apply eq_of_traceBilin_left_eq X Y
  intro Z
  rw [traceBilin_symm X Z, traceBilin_symm Y Z]
  exact h Z

end H3Zorn

/-- The existing native bilinear-map representation of the full Albert trace
pairing has an injective first currying map. -/
theorem h3zornTraceBilin_injective : Function.Injective h3zornTraceBilin := by
  intro X Y h
  apply H3Zorn.eq_of_traceBilin_left_eq X Y
  intro Z
  exact DFunLike.congr_fun h Z

/-- Nondegeneracy in Mathlib's native bilinear-map interface. -/
theorem h3zornTraceBilin_nondegenerate : LinearMap.Nondegenerate h3zornTraceBilin :=
  ⟨H3Zorn.eq_zero_of_traceBilin_left, H3Zorn.eq_zero_of_traceBilin_right⟩

end InfoGeometry.Algebra
