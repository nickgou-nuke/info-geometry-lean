/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11BrauerWeylGenerators
import InfoGeometry.Geometry.AssociativeGaugeConnection
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Quaternion axes and Cayley units in two noncommutative block doublings

The two negative generators are negated to match the intake convention
`Ω = !![0, -1; 1, 0]`. The third axis is their ordered product. The first
two are odd Clifford generators and the third is even: this mixed-parity
quaternion subalgebra is not asserted to be a Clifford spin group.

Polynomial identities hold over every ring. Actual Cayley units require
invertible `2`. A faithful quaternion algebra and imaginary-quaternion Lie
embedding are separately constructed over any nontrivial real coefficient
algebra, using Mathlib's quaternion universal property.
-/

namespace InfoGeometry.Clifford.Cl22QuaternionCayley

open SplitAtomDoubling Cl11BrauerWeylGenerators

variable {B : Type*} [Ring B]

abbrev Nested (B : Type*) := Block2 (Block2 B)

def axisI : Nested B := -fourGenerators (Sum.inl 1)
def axisJ : Nested B := -fourGenerators (Sum.inr 1)
def axisK : Nested B := axisI * axisJ

@[simp] theorem axisI_square : (axisI : Nested B) * axisI = -1 := by
  simpa [axisI, fourSquares, splitSquares] using
    (fourGenerators_square (B := B) (Sum.inl 1))

@[simp] theorem axisJ_square : (axisJ : Nested B) * axisJ = -1 := by
  simpa [axisJ, fourSquares, splitSquares] using
    (fourGenerators_square (B := B) (Sum.inr 1))

theorem axes_anticommute :
    (axisI : Nested B) * axisJ + axisJ * axisI = 0 := by
  simpa [axisI, axisJ] using
    (fourGenerators_pairwise (B := B)
      (i := Sum.inl 1) (j := Sum.inr 1) (by decide))

@[simp] theorem axisI_mul_axisJ : (axisI : Nested B) * axisJ = axisK := rfl

@[simp] theorem axisJ_mul_axisI : (axisJ : Nested B) * axisI = -axisK := by
  exact eq_neg_of_add_eq_zero_right axes_anticommute

/-- The native quaternion presentation over integer scalars. -/
def integerQuaternionBasis : QuaternionAlgebra.Basis (Nested B) (-1 : ℤ) 0 (-1) where
  i := axisI
  j := axisJ
  k := axisK
  i_mul_i := by simp
  j_mul_j := by simp
  i_mul_j := axisI_mul_axisJ
  j_mul_i := by simp

@[simp] theorem axisI_mul_axisK : (axisI : Nested B) * axisK = -axisJ := by
  simpa [integerQuaternionBasis] using (integerQuaternionBasis (B := B)).i_mul_k

@[simp] theorem axisK_mul_axisI : (axisK : Nested B) * axisI = axisJ := by
  simpa [integerQuaternionBasis] using (integerQuaternionBasis (B := B)).k_mul_i

@[simp] theorem axisK_mul_axisJ : (axisK : Nested B) * axisJ = -axisI := by
  simpa [integerQuaternionBasis] using (integerQuaternionBasis (B := B)).k_mul_j

@[simp] theorem axisJ_mul_axisK : (axisJ : Nested B) * axisK = axisI := by
  simpa [integerQuaternionBasis] using (integerQuaternionBasis (B := B)).j_mul_k

@[simp] theorem axisK_square : (axisK : Nested B) * axisK = -1 := by
  simpa [integerQuaternionBasis] using (integerQuaternionBasis (B := B)).k_mul_k

theorem commutator_ij :
    (axisI : Nested B) * axisJ - axisJ * axisI = 2 • axisK := by
  simp [two_mul]

theorem commutator_jk :
    (axisJ : Nested B) * axisK - axisK * axisJ = 2 • axisI := by
  simp [two_mul]

theorem commutator_ki :
    (axisK : Nested B) * axisI - axisI * axisK = 2 • axisJ := by
  simp [two_mul]

/-- The noncommutativity defect of Cayley factors is the same ordered bracket. -/
theorem cayley_commutator_ij :
    (1 + (axisI : Nested B)) * (1 + axisJ) -
      (1 + axisJ) * (1 + axisI) = 2 • axisK := by
  calc
    _ = axisI * axisJ - axisJ * axisI := by noncomm_ring
    _ = _ := commutator_ij

theorem cayley_sandwich_ij :
    (1 + (axisI : Nested B)) * axisJ * (1 - axisI) = 2 • axisK := by
  simp only [add_mul, mul_sub, mul_one, one_mul,
    axisI_mul_axisJ, axisJ_mul_axisI, axisK_mul_axisI, two_nsmul]
  abel

theorem cayley_sandwich_jk :
    (1 + (axisJ : Nested B)) * axisK * (1 - axisJ) = 2 • axisI := by
  simp only [add_mul, mul_sub, mul_one, one_mul,
    axisJ_mul_axisK, axisK_mul_axisJ, axisI_mul_axisJ, two_nsmul]
  abel

theorem cayley_sandwich_ki :
    (1 + (axisK : Nested B)) * axisI * (1 - axisK) = 2 • axisJ := by
  simp only [add_mul, mul_sub, mul_one, one_mul,
    axisK_mul_axisI, axisI_mul_axisK, axisJ_mul_axisK, two_nsmul]
  abel

section Units

variable {A : Type*} [Ring A]

theorem cayley_factors {e : A} (he : e * e = -1) :
    (1 + e) * (1 - e) = 2 := by
  noncomm_ring [he]
  simp

theorem cayley_factors_reverse {e : A} (he : e * e = -1) :
    (1 - e) * (1 + e) = 2 := by
  noncomm_ring [he]
  simp

/-- An actual unit with the required factor of one half in its inverse. -/
def cayleyUnit [Invertible (2 : A)] (e : A) (he : e * e = -1) : Aˣ where
  val := 1 + e
  inv := (1 - e) * ⅟(2 : A)
  val_inv := by rw [← mul_assoc, cayley_factors he, mul_invOf_self]
  inv_val := by
    have hc : Commute (2 : A) (1 + e) := by
      show (2 : A) * (1 + e) = (1 + e) * 2
      noncomm_ring
    rw [mul_assoc, hc.invOf_left.eq, ← mul_assoc,
      cayley_factors_reverse he, mul_invOf_self]

end Units

theorem cayley_conjugation_ij [Invertible (2 : Nested B)] :
    (cayleyUnit (axisI : Nested B) axisI_square : Nested B) * axisJ *
      (↑((cayleyUnit (axisI : Nested B) axisI_square)⁻¹) : Nested B) = axisK := by
  change (1 + (axisI : Nested B)) * axisJ * ((1 - axisI) * ⅟(2 : Nested B)) = axisK
  rw [← mul_assoc, cayley_sandwich_ij]
  calc
    (2 • (axisK : Nested B)) * ⅟(2 : Nested B) =
        axisK * ((2 : Nested B) * ⅟(2 : Nested B)) := by
      simp only [two_nsmul]
      noncomm_ring
    _ = axisK := by rw [mul_invOf_self, mul_one]

/-- Noncommutativity is explicit and excludes characteristic two. -/
theorem cayley_factors_do_not_commute (h2 : (2 : Nested B) ≠ 0) :
    (1 + (axisI : Nested B)) * (1 + axisJ) ≠
      (1 + axisJ) * (1 + axisI) := by
  intro h
  have hz : (2 : Nested B) * axisK = 0 := by
    have hcomm := cayley_commutator_ij (B := B)
    rw [h, sub_self] at hcomm
    simpa only [two_nsmul, two_mul] using hcomm.symm
  have hh := congrArg (fun x : Nested B => x * axisK) hz
  rw [mul_assoc, axisK_square, mul_neg_one, zero_mul, neg_eq_zero] at hh
  exact h2 hh

section Curvature

open InfoGeometry.Geometry.AssociativeGaugeConnection

/-- Constant-axis curvature. The derivative hypotheses are necessary for
general derivations of the full matrix algebra. -/
theorem axis_curvature (D E : Module.End ℤ (Nested B))
    (hD : D axisJ = 0) (hE : E axisI = 0) :
    curvature D E axisI axisJ = 2 • (axisK : Nested B) := by
  simpa [curvature, hD, hE] using (commutator_ij (B := B))

/-- Gauge covariance specializes the same exact curvature under any invertible matrix. -/
theorem axis_curvature_gauge (D E : Module.End ℤ (Nested B))
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x))
    (hDJ : D axisJ = 0) (hEI : E axisI = 0) (u : (Nested B)ˣ) :
    curvature D E (gaugePotential D axisI u) (gaugePotential E axisJ u) =
      conjugate u (2 • (axisK : Nested B)) := by
  rw [curvature_gauge_covariant D E hD hE hcomm, axis_curvature D E hDJ hEI]

end Curvature

section RealEmbedding

variable [Algebra ℝ B]

/-- The same matrix axes give Mathlib's real quaternion presentation. -/
def realQuaternionBasis : QuaternionAlgebra.Basis (Nested B) (-1 : ℝ) 0 (-1) where
  i := axisI
  j := axisJ
  k := axisK
  i_mul_i := by simp
  j_mul_j := by simp
  i_mul_j := axisI_mul_axisJ
  j_mul_i := by simp

def realQuaternionHom : Quaternion ℝ →ₐ[ℝ] Nested B :=
  (realQuaternionBasis (B := B)).liftHom

theorem realQuaternionHom_injective [Nontrivial B] :
    Function.Injective (realQuaternionHom (B := B)) :=
  (realQuaternionHom (B := B)).toRingHom.injective

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- The conventional real Lie model of the imaginary quaternions. -/
def imaginaryQuaternions : LieSubalgebra ℝ (Quaternion ℝ) where
  carrier := {q | q.re = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change x.re = 0 at hx
    change y.re = 0 at hy
    change (x + y).re = 0
    simp [hx, hy]
  smul_mem' := by
    intro r x hx
    change x.re = 0 at hx
    change (r • x).re = 0
    simp [hx]
  lie_mem' := by
    intro x y _ _
    change (x * y - y * x).re = 0
    simp only [Quaternion.re_sub, Quaternion.re_mul]
    ring

/-- A native Lie homomorphism into the full noncommutative matrix algebra. -/
def imaginaryQuaternionLieHom : imaginaryQuaternions →ₗ⁅ℝ⁆ Nested B :=
  (realQuaternionHom (B := B)).toLieHom.comp imaginaryQuaternions.incl

theorem imaginaryQuaternionLieHom_injective [Nontrivial B] :
    Function.Injective (imaginaryQuaternionLieHom (B := B)) := by
  intro x y h
  apply Subtype.ext
  exact realQuaternionHom_injective h

end RealEmbedding

end InfoGeometry.Clifford.Cl22QuaternionCayley
