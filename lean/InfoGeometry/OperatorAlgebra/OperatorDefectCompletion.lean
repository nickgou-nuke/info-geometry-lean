/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Operator defects, Peirce components, and strict Lie closure

All products are ordered products in an arbitrary associative algebra.
In particular, the results specialize to full matrix algebras and endomorphism
algebras without a commutativity, diagonalization, or scalar-coupling hypothesis.

This file is a proof-script draft. It has not been elaborated by Lean in the
current environment. No admission or additional axiom is used in its proofs.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.DefectCompletion

attribute [local instance] LieRing.ofAssociativeRing

section Peirce

variable {A : Type*} [Ring A]

/-- The block-diagonal component for an idempotent `p`. -/
def evenPart (p X : A) : A :=
  p * X * p + (1 - p) * X * (1 - p)

/-- The off-diagonal component for an idempotent `p`. -/
def oddPart (p X : A) : A :=
  p * X * (1 - p) + (1 - p) * X * p

/-- Exact reconstruction; even this identity does not need idempotence. -/
theorem evenPart_add_oddPart (p X : A) :
    evenPart p X + oddPart p X = X := by
  unfold evenPart oddPart
  noncomm_ring

/-- A nonzero defect has a nonzero corner, not necessarily an odd corner. -/
theorem nonzero_has_nonzero_corner (p D : A) (hD : D ≠ 0) :
    p * D * p ≠ 0 ∨
      p * D * (1 - p) ≠ 0 ∨
      (1 - p) * D * p ≠ 0 ∨
      (1 - p) * D * (1 - p) ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨hpp, hpq, hqp, hqq⟩
  apply hD
  have hrec := evenPart_add_oddPart p D
  unfold evenPart oddPart at hrec
  simpa only [hpp, hpq, hqp, hqq, zero_add] using hrec.symm

/-- Oddness follows when the two diagonal corners actually vanish. -/
theorem eq_oddPart_of_diagonal_corners_zero (p D : A)
    (hpp : p * D * p = 0)
    (hqq : (1 - p) * D * (1 - p) = 0) :
    D = oddPart p D := by
  have hrec := evenPart_add_oddPart p D
  unfold evenPart at hrec
  simpa only [hpp, hqq, zero_add] using hrec.symm

/-- The odd Peirce component is obtained by two native commutators. -/
theorem double_commutator_eq_oddPart (p X : A) (hp : p * p = p) :
    ⁅p, ⁅p, X⁆⁆ = oddPart p X := by
  calc
    ⁅p, ⁅p, X⁆⁆ =
        (p * p) * X - p * X * p - p * X * p + X * (p * p) := by
      simp only [LieRing.of_associative_ring_bracket]
      noncomm_ring
    _ = oddPart p X := by
      rw [hp]
      unfold oddPart
      noncomm_ring

/-- Compression fails to preserve brackets by an exact cross-corner term. -/
theorem compressed_commutator_defect (p X Y : A) (hp : p * p = p) :
    p * ⁅X, Y⁆ * p - ⁅p * X * p, p * Y * p⁆ =
      p * X * (1 - p) * Y * p - p * Y * (1 - p) * X * p := by
  have hmul (U V : A) :
      (p * U * p) * (p * V * p) = p * U * p * V * p := by
    calc
      (p * U * p) * (p * V * p) = p * U * (p * p) * V * p := by
        noncomm_ring
      _ = p * U * p * V * p := by rw [hp]
  simp only [LieRing.of_associative_ring_bracket]
  rw [hmul X Y, hmul Y X]
  noncomm_ring

/-- The upper corner is a nilpotent transition, with no inverse assumed. -/
theorem upper_corner_sq_zero (p X : A) (hp : p * p = p) :
    (p * X * (1 - p)) * (p * X * (1 - p)) = 0 := by
  have hqp : (1 - p) * p = 0 := by
    rw [sub_mul, one_mul, hp, sub_self]
  calc
    (p * X * (1 - p)) * (p * X * (1 - p)) =
        p * X * ((1 - p) * p) * X * (1 - p) := by noncomm_ring
    _ = 0 := by rw [hqp]; simp

/-- The lower corner is another nilpotent transition. -/
theorem lower_corner_sq_zero (p X : A) (hp : p * p = p) :
    ((1 - p) * X * p) * ((1 - p) * X * p) = 0 := by
  have hpq : p * (1 - p) = 0 := by
    rw [mul_sub, mul_one, hp, sub_self]
  calc
    ((1 - p) * X * p) * ((1 - p) * X * p) =
        (1 - p) * X * (p * (1 - p)) * X * p := by noncomm_ring
    _ = 0 := by rw [hpq]; simp

end Peirce

section LinearProjection

variable {R A : Type*} [CommRing R] [Ring A] [LieAlgebra R A]

/-- The part of a native commutator discarded by a linear readout. -/
def bracketDefect (P : A →ₗ[R] A) (X Y : A) : A :=
  ⁅X, Y⁆ - P ⁅X, Y⁆

/-- The full commutator is recovered exactly, not modulo the defect. -/
theorem bracket_reconstruction (P : A →ₗ[R] A) (X Y : A) :
    P ⁅X, Y⁆ + bracketDefect P X Y = ⁅X, Y⁆ := by
  unfold bracketDefect
  abel

/-- Closure at this pair is precisely the zero-defect condition. -/
theorem bracketDefect_eq_zero_iff (P : A →ₗ[R] A) (X Y : A) :
    bracketDefect P X Y = 0 ↔ P ⁅X, Y⁆ = ⁅X, Y⁆ := by
  unfold bracketDefect
  rw [sub_eq_zero]
  exact eq_comm

/-- Idempotence identifies the defect as an actual discarded component. -/
theorem bracketDefect_in_kernel (P : A →ₗ[R] A)
    (hP : ∀ Z, P (P Z) = P Z) (X Y : A) :
    P (bracketDefect P X Y) = 0 := by
  simp only [bracketDefect, map_sub, hP, sub_self]

/-- A nonzero discarded component cannot lie in the retained range. -/
theorem bracketDefect_not_mem_range (P : A →ₗ[R] A)
    (hP : ∀ Z, P (P Z) = P Z) (X Y : A)
    (hD : bracketDefect P X Y ≠ 0) :
    bracketDefect P X Y ∉ LinearMap.range P := by
  rintro ⟨Z, hZ⟩
  have hfixed : P (bracketDefect P X Y) = bracketDefect P X Y := by
    rw [← hZ, hP]
  apply hD
  exact hfixed.symm.trans (bracketDefect_in_kernel P hP X Y)

/-- Jacobiator of the projected commutator, with right-nested convention. -/
def projectedJacobiator (P : A →ₗ[R] A) (X Y Z : A) : A :=
  P ⁅X, P ⁅Y, Z⁆⁆ + P ⁅Y, P ⁅Z, X⁆⁆ + P ⁅Z, P ⁅X, Y⁆⁆

/-- The projected Jacobiator is exactly the feedback from discarded brackets.
No failure of Jacobi is asserted in the ambient associative algebra. -/
theorem projectedJacobiator_eq_defect (P : A →ₗ[R] A) (X Y Z : A) :
    projectedJacobiator P X Y Z =
      -P (⁅X, bracketDefect P Y Z⁆ +
        ⁅Y, bracketDefect P Z X⁆ + ⁅Z, bracketDefect P X Y⁆) := by
  unfold projectedJacobiator
  rw [← map_add, ← map_add, ← map_neg]
  apply congrArg P
  simp only [bracketDefect, LieRing.of_associative_ring_bracket]
  noncomm_ring

/-- A nonzero projected Jacobiator detects at least one nonzero omitted bracket. -/
theorem nonzero_projectedJacobiator_detects_defect
    (P : A →ₗ[R] A) (X Y Z : A)
    (hJ : projectedJacobiator P X Y Z ≠ 0) :
    bracketDefect P Y Z ≠ 0 ∨
      bracketDefect P Z X ≠ 0 ∨ bracketDefect P X Y ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨hYZ, hZX, hXY⟩
  apply hJ
  rw [projectedJacobiator_eq_defect]
  simp [hYZ, hZX, hXY]

/-- Canonical Lie closure of the retained operator range. -/
def retainedLieClosure (P : A →ₗ[R] A) : LieSubalgebra R A :=
  LieSubalgebra.lieSpan R A (Set.range P)

/-- The native closure is the least operator Lie subalgebra containing the readout. -/
theorem retainedLieClosure_le (P : A →ₗ[R] A) (K : LieSubalgebra R A)
    (hK : ∀ X : A, P X ∈ K) : retainedLieClosure P ≤ K := by
  apply LieSubalgebra.lieSpan_le.mpr
  rintro _ ⟨X, rfl⟩
  exact hK X

/-- The missing component is already generated by the retained operators
under brackets; it is not adjoined as an unrelated free generator. -/
theorem bracketDefect_mem_retainedLieClosure
    (P : A →ₗ[R] A) (X Y : A) (hX : P X = X) (hY : P Y = Y) :
    bracketDefect P X Y ∈ retainedLieClosure P := by
  have hx : X ∈ retainedLieClosure P :=
    LieSubalgebra.subset_lieSpan ⟨X, hX⟩
  have hy : Y ∈ retainedLieClosure P :=
    LieSubalgebra.subset_lieSpan ⟨Y, hY⟩
  have hret : P ⁅X, Y⁆ ∈ retainedLieClosure P :=
    LieSubalgebra.subset_lieSpan ⟨⁅X, Y⁆, rfl⟩
  exact (retainedLieClosure P).sub_mem
    ((retainedLieClosure P).lie_mem hx hy) hret

/-- A witnessed defect proves a strict enlargement of the retained linear
space inside its native Lie closure. -/
theorem range_lt_retainedLieClosure_of_defect
    (P : A →ₗ[R] A) (hP : ∀ Z, P (P Z) = P Z)
    (X Y : A) (hX : P X = X) (hY : P Y = Y)
    (hD : bracketDefect P X Y ≠ 0) :
    LinearMap.range P < (retainedLieClosure P).toSubmodule := by
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · intro Z hZ
    exact LieSubalgebra.subset_lieSpan hZ
  · intro hback
    exact bracketDefect_not_mem_range P hP X Y hD
      (hback (bracketDefect_mem_retainedLieClosure P X Y hX hY))

/-- Homogeneous eigenoperator weights add under the actual commutator. -/
theorem bracket_weight_add (H X Y : A) (a b : R)
    (hX : ⁅H, X⁆ = a • X) (hY : ⁅H, Y⁆ = b • Y) :
    ⁅H, ⁅X, Y⁆⁆ = (a + b) • ⁅X, Y⁆ := by
  rw [leibniz_lie, hX, hY, smul_lie, lie_smul, ← add_smul]

/-- A grading-compatible projection does not change the weight of the defect.
The result can be even or odd; its grade is not assigned by terminology. -/
theorem bracketDefect_weight
    (P : A →ₗ[R] A) (H X Y : A) (a b : R)
    (hPH : ∀ Z, ⁅H, P Z⁆ = P ⁅H, Z⁆)
    (hX : ⁅H, X⁆ = a • X) (hY : ⁅H, Y⁆ = b • Y) :
    ⁅H, bracketDefect P X Y⁆ = (a + b) • bracketDefect P X Y := by
  simp only [bracketDefect, lie_sub, hPH,
    bracket_weight_add H X Y a b hX hY, map_smul, smul_sub]

/-- The odd Peirce component is generated inside every Lie subalgebra
containing the idempotent and the original defect. -/
theorem oddPart_mem_of_mem (K : LieSubalgebra R A) (p D : A)
    (hp : p * p = p) (hpK : p ∈ K) (hDK : D ∈ K) :
    oddPart p D ∈ K := by
  rw [← double_commutator_eq_oddPart p D hp]
  exact K.lie_mem hpK (K.lie_mem hpK hDK)

end LinearProjection

end InfoGeometry.OperatorAlgebra.DefectCompletion
