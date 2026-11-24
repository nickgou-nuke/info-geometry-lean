/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.AlternatingCornerTriple
import InfoGeometry.Algebra.NonAssocDerivation
import InfoGeometry.Core.PeirceMatrixPerfectPairing
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Associative alternating products, module actions, and null operator spaces

The ternary polynomial, Peirce corner, and Leibniz endomorphism carrier are
reused from their existing owners. Native opposite-ring linear maps express
right-module actions. Their ordered multiplication action differs from the
inner adjoint derivation and from the full alternating cubic.

The null operator statements use actual native range submodules. Their
pairing is the plain matrix trace of the ordered product, not a transpose
pairing. The real matrix counterexample fixes the Filippov boundary.
-/

namespace InfoGeometry.Algebra.AssociativeNambuOperators

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine

attribute [local instance 100] LieRing.ofAssociativeRing

section Ring

variable {A : Type*} [Ring A]

/-- The existing ternary product evaluates to the quadratic Casimir under
the three actual cyclic commutator relations. -/
theorem alternatingProduct3_eq_casimir (a b c : A)
    (hab : PeirceSpine.comm a b = c) (hbc : PeirceSpine.comm b c = a)
    (hca : PeirceSpine.comm c a = b) :
    alternatingProduct3 a b c = a * a + b * b + c * c := by
  rw [← cyclicCommutatorTriple_eq_alternatingProduct3,
    cyclicCommutatorTriple_eq_right_contraction, hbc, hca, hab]

/-- Each summand is a native endomorphism of the regular right module. -/
theorem alternatingProduct3_eq_mulLeft_sum (a b c : A) :
    alternatingProduct3 a b c =
      LinearMap.mulLeft Aᵐᵒᵖ (PeirceSpine.comm b c) a +
      LinearMap.mulLeft Aᵐᵒᵖ (PeirceSpine.comm c a) b +
      LinearMap.mulLeft Aᵐᵒᵖ (PeirceSpine.comm a b) c := by
  change alternatingProduct3 a b c =
    PeirceSpine.comm b c * a + PeirceSpine.comm c a * b + PeirceSpine.comm a b * c
  rw [← cyclicCommutatorTriple_eq_alternatingProduct3,
    cyclicCommutatorTriple_eq_right_contraction]

/-- A nonzero commutator prevents the fixed-pair ternary map from being a
unital-algebra derivation: its value on the unit is this commutator. -/
theorem alternatingProduct3_one (a b : A) :
    alternatingProduct3 a b 1 = PeirceSpine.comm a b := by
  simp [alternatingProduct3, PeirceSpine.comm]

/-- Two mutually annihilating inputs give the zero regular right-module map. -/
theorem mulLeft_comm_eq_zero_of_mul_eq_zero (a b : A)
    (hab : a * b = 0) (hba : b * a = 0) :
    LinearMap.mulLeft Aᵐᵒᵖ (PeirceSpine.comm a b) = 0 := by
  simp [PeirceSpine.comm, hab, hba]

/-- Square-zero sandwiches have zero ordered products. -/
theorem squareZero_sandwich_mul (n a b : A) (hn : n * n = 0) :
    (n * a * n) * (n * b * n) = 0 := by
  calc
    _ = n * a * (n * n) * b * n := by simp only [mul_assoc]
    _ = 0 := by rw [hn]; simp

end Ring

section Algebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The native adjoint of the commutator belongs to the existing Lie
subalgebra of ordered Leibniz endomorphisms. -/
theorem ad_comm_mem_derivations (a b : A) :
    LieAlgebra.ad R A (PeirceSpine.comm a b) ∈ NonAssocDerivation.derivations R A := by
  intro x y
  simp only [LieAlgebra.ad_apply, Ring.lie_def, PeirceSpine.comm]
  noncomm_ring

/-- Left multiplication is a derivation precisely when its coefficient
vanishes; it must not be confused with the inner adjoint action. -/
theorem mulLeft_isLeibniz_iff (c : A) :
    NonAssocDerivation.IsLeibniz R A (LinearMap.mulLeft R c) ↔ c = 0 := by
  constructor
  · intro h
    have h₁ := h 1 1
    simp only [LinearMap.mulLeft_apply, mul_one, one_mul] at h₁
    have hz : c + c = c + 0 := by simpa only [add_zero] using h₁.symm
    exact add_left_cancel hz
  · intro h x y
    simp [h]

/-- The native sandwich range is a zero-product operator subspace. -/
theorem mul_eq_zero_of_mem_sandwich_range (n : A) (hn : n * n = 0)
    {a b : A}
    (ha : a ∈ LinearMap.range (LinearMap.mulLeftRight R (n, n)))
    (hb : b ∈ LinearMap.range (LinearMap.mulLeftRight R (n, n))) : a * b = 0 := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact squareZero_sandwich_mul n x y hn

/-- The existing alternating product vanishes on the square-zero sandwich range. -/
theorem alternatingProduct3_sandwich_range (n : A) (hn : n * n = 0)
    {a b c : A}
    (ha : a ∈ LinearMap.range (LinearMap.mulLeftRight R (n, n)))
    (hb : b ∈ LinearMap.range (LinearMap.mulLeftRight R (n, n)))
    (hc : c ∈ LinearMap.range (LinearMap.mulLeftRight R (n, n))) :
    alternatingProduct3 a b c = 0 := by
  simp only [alternatingProduct3,
    mul_eq_zero_of_mem_sandwich_range n hn ha hb,
    mul_eq_zero_of_mem_sandwich_range n hn ha hc,
    mul_eq_zero_of_mem_sandwich_range n hn hb hc,
    mul_eq_zero_of_mem_sandwich_range n hn hb ha,
    mul_eq_zero_of_mem_sandwich_range n hn hc ha,
    mul_eq_zero_of_mem_sandwich_range n hn hc hb,
    zero_mul, sub_zero, add_zero]

end Algebra

section Matrix

open InfoGeometry.Core.PeirceDecomposition

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Plain trace pairing vanishes on the native square-zero sandwich space. -/
theorem trace_mul_sandwich_range (N : Matrix n n R) (hN : N * N = 0)
    {A B : Matrix n n R}
    (hA : A ∈ LinearMap.range (LinearMap.mulLeftRight R (N, N)))
    (hB : B ∈ LinearMap.range (LinearMap.mulLeftRight R (N, N))) :
    Matrix.trace (A * B) = 0 := by
  rw [mul_eq_zero_of_mem_sandwich_range N hN hA hB, Matrix.trace_zero]

/-- Reuse the existing matrix-corner submodule and its membership theorem. -/
theorem mul_eq_zero_of_mem_corner_range (P : Matrix n n R) (hP : P * P = P)
    {A B : Matrix n n R}
    (hA : A ∈ LinearMap.range (component10Linear P))
    (hB : B ∈ LinearMap.range (component10Linear P)) : A * B = 0 :=
  peirce10_mul_peirce10_eq_zero P hP
    ((mem_range_component10Linear P A).mp hA)
    ((mem_range_component10Linear P B).mp hB)

/-- The existing directed corner is totally null for the plain trace pairing. -/
theorem trace_mul_corner_range (P : Matrix n n R) (hP : P * P = P)
    {A B : Matrix n n R}
    (hA : A ∈ LinearMap.range (component10Linear P))
    (hB : B ∈ LinearMap.range (component10Linear P)) :
    Matrix.trace (A * B) = 0 := by
  rw [mul_eq_zero_of_mem_corner_range P hP hA hB, Matrix.trace_zero]

/-- The native commutator multiplication action collapses for corner inputs. -/
theorem mulLeft_comm_corner_range (P : Matrix n n R) (hP : P * P = P)
    {A B : Matrix n n R}
    (hA : A ∈ LinearMap.range (component10Linear P))
    (hB : B ∈ LinearMap.range (component10Linear P)) :
    LinearMap.mulLeft (Matrix n n R)ᵐᵒᵖ (PeirceSpine.comm A B) = 0 :=
  mulLeft_comm_eq_zero_of_mul_eq_zero A B
    (mul_eq_zero_of_mem_corner_range P hP hA hB)
    (mul_eq_zero_of_mem_corner_range P hP hB hA)

theorem alternatingProduct3_corner_range (P : Matrix n n R) (hP : P * P = P)
    {A B C : Matrix n n R}
    (hA : A ∈ LinearMap.range (component10Linear P))
    (hB : B ∈ LinearMap.range (component10Linear P))
    (hC : C ∈ LinearMap.range (component10Linear P)) :
    alternatingProduct3 A B C = 0 := by
  simp only [alternatingProduct3,
    mul_eq_zero_of_mem_corner_range P hP hA hB,
    mul_eq_zero_of_mem_corner_range P hP hA hC,
    mul_eq_zero_of_mem_corner_range P hP hB hC,
    mul_eq_zero_of_mem_corner_range P hP hB hA,
    mul_eq_zero_of_mem_corner_range P hP hC hA,
    mul_eq_zero_of_mem_corner_range P hP hC hB,
    zero_mul, sub_zero, add_zero]

end Matrix

/-- The associative alternating polynomial does not obey the Filippov
fundamental identity on real three-by-three matrices. -/
theorem alternatingProduct3_not_filippov :
    ¬ (∀ A B U V W : Matrix (Fin 3) (Fin 3) ℝ,
      alternatingProduct3 A B (alternatingProduct3 U V W) =
        alternatingProduct3 (alternatingProduct3 A B U) V W +
        alternatingProduct3 U (alternatingProduct3 A B V) W +
        alternatingProduct3 U V (alternatingProduct3 A B W)) := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2)
    (h (Matrix.single 0 0 1) (Matrix.single 0 1 1)
      (Matrix.single 0 0 1) (Matrix.single 0 2 1) (Matrix.single 1 0 1))
  norm_num [alternatingProduct3, mul_add, add_mul, mul_sub, sub_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne] at he

end InfoGeometry.Algebra.AssociativeNambuOperators
