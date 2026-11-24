/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Canonical.ZornMultiplicationOperators
import Mathlib.Tactic.Module

/-!
# Real Zorn Clifford operators and infinitesimal triality

This module uses the canonical Zorn carrier, its native quadratic form, and
the existing universal Clifford representation.  The anticommutator is
obtained from Mathlib's polarization theorem.  The infinitesimal triality
identity is the upper-right block of an associative Clifford commutator.

The normalization is `1 / 4` for spin bivectors and `1` for the corresponding
vector action with respect to the associated bilinear form.  Clifford
generators exchange the chiral summands; bivectors preserve them.

The declarations here do not assert faithfulness, a matrix-algebra
classification, an outer `S₃` action, or a classification of the split
octonion derivation Lie algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCl44Triality

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford

/-- The native symmetric bilinear form associated with the canonical Zorn norm. -/
abbrev zornBilin : LinearMap.BilinForm ℝ (ZornMatrix ℝ) :=
  (zornNorm (R := ℝ)).associated

/-- Coordinate formula for the associated form, fixing its factor of one half. -/
theorem zornBilin_apply (a b : ZornMatrix ℝ) :
    zornBilin a b = (1 / 2 : ℝ) *
      (a.a * b.b + b.a * a.b - dot a.x b.y - dot b.x a.y) := by
  simp [zornBilin, QuadraticMap.associated_apply, zornNorm_apply,
    zornNormFun, dot]
  ring

theorem zornBilin_symm (a b : ZornMatrix ℝ) :
    zornBilin a b = zornBilin b a := by
  simp only [zornBilin_apply]
  ring

@[simp] theorem zornBilin_self (a : ZornMatrix ℝ) :
    zornBilin a a = zornNorm a := by
  simp only [zornBilin_apply, zornNorm_apply, zornNormFun]
  ring

/-- The scalar polarization convention used in the Clifford anticommutator. -/
theorem polar_eq_two_zornBilin (a b : ZornMatrix ℝ) :
    QuadraticMap.polar (zornNorm (R := ℝ)) a b = 2 * zornBilin a b := by
  have h := congrArg
    (fun B : LinearMap.BilinForm ℝ (ZornMatrix ℝ) => B a b)
    (QuadraticMap.two_nsmul_associated ℝ (zornNorm (R := ℝ)))
  have h' : zornBilin a b + zornBilin a b =
      QuadraticMap.polar (zornNorm (R := ℝ)) a b := by
    simpa only [zornBilin, two_smul, LinearMap.add_apply,
      QuadraticMap.polarBilin_apply_apply] using h
  rw [← h', two_mul]

@[simp] theorem diracGamma_apply (a : ZornMatrix ℝ)
    (s : DiracSpinor16 (R := ℝ)) :
    diracGamma a s = (a * s.2, zornConj a * s.1) := rfl

@[simp] theorem diracGammaLinear_apply (a : ZornMatrix ℝ) :
    diracGammaLinear (R := ℝ) a = diracGamma a := rfl

/-- The already constructed Clifford representation satisfies the quadratic relation. -/
theorem diracGamma_square (a : ZornMatrix ℝ) :
    diracGamma a * diracGamma a =
      zornNorm a • (1 : Module.End ℝ (DiracSpinor16 (R := ℝ))) := by
  simpa only [diracGammaLinear_apply, Algebra.algebraMap_eq_smul_one] using
    (diracGamma_sq (R := ℝ) a)

/-- The Clifford anticommutator follows from native quadratic polarization. -/
theorem diracGamma_anticommutator (a b : ZornMatrix ℝ) :
    diracGamma a * diracGamma b + diracGamma b * diracGamma a =
      (2 * zornBilin a b) • (1 : Module.End ℝ (DiracSpinor16 (R := ℝ))) := by
  have h := CliffordAlgebra.mul_add_swap_eq_polar_of_forall_mul_self_eq
    (Q := zornNorm (R := ℝ)) (diracGammaLinear (R := ℝ))
    (diracGamma_sq (R := ℝ)) a b
  rw [polar_eq_two_zornBilin, Algebra.algebraMap_eq_smul_one] at h
  simpa only [diracGammaLinear_apply] using h

/-- The vector representation of the orthogonal bivector associated with `a,b`. -/
def vectorBivector (a b : ZornMatrix ℝ) : Module.End ℝ (ZornMatrix ℝ) :=
  (zornBilin b).smulRight a - (zornBilin a).smulRight b

@[simp] theorem vectorBivector_apply (a b v : ZornMatrix ℝ) :
    vectorBivector a b v = zornBilin b v • a - zornBilin a v • b := rfl

/-- The positive-chirality block of the normalized Clifford bivector. -/
def spinBivPlus (a b : ZornMatrix ℝ) : Module.End ℝ (ZornMatrix ℝ) :=
  (1 / 4 : ℝ) •
    (leftMulLinear a * leftMulLinear (zornConj b) -
      leftMulLinear b * leftMulLinear (zornConj a))

/-- The negative-chirality block of the normalized Clifford bivector. -/
def spinBivMinus (a b : ZornMatrix ℝ) : Module.End ℝ (ZornMatrix ℝ) :=
  (1 / 4 : ℝ) •
    (leftMulLinear (zornConj a) * leftMulLinear b -
      leftMulLinear (zornConj b) * leftMulLinear a)

/-- Normalized even Clifford action on the direct sum of the two real spinor carriers. -/
def spinBivector (a b : ZornMatrix ℝ) :
    Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  (1 / 4 : ℝ) • (diracGamma a * diracGamma b - diracGamma b * diracGamma a)

@[simp] theorem spinBivector_apply (a b : ZornMatrix ℝ)
    (s : DiracSpinor16 (R := ℝ)) :
    spinBivector a b s = (spinBivPlus a b s.1, spinBivMinus a b s.2) := rfl

/-- The real chiral grading is positive on the first summand and negative on the second. -/
def chiralGrading : Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  (1 : Module.End ℝ (ZornMatrix ℝ)).prodMap (-1)

@[simp] theorem chiralGrading_apply (s : DiracSpinor16 (R := ℝ)) :
    chiralGrading s = (s.1, -s.2) := rfl

theorem chiralGrading_square : chiralGrading * chiralGrading = 1 := by
  apply LinearMap.ext
  intro s
  simp only [Module.End.mul_apply, chiralGrading_apply, neg_neg,
    Module.End.one_apply]

/-- A Clifford generator exchanges chirality. -/
theorem diracGamma_odd (a : ZornMatrix ℝ) :
    chiralGrading * diracGamma a + diracGamma a * chiralGrading = 0 := by
  apply LinearMap.ext
  intro s
  apply Prod.ext
  · change leftMulLinear a s.2 + leftMulLinear a (-s.2) = 0
    rw [map_neg, add_neg_cancel]
  · change -(zornConj a * s.1) + zornConj a * s.1 = 0
    exact neg_add_cancel _

/-- A Clifford bivector preserves each of the two chiral summands. -/
theorem spinBivector_even (a b : ZornMatrix ℝ) :
    chiralGrading * spinBivector a b = spinBivector a b * chiralGrading := by
  apply LinearMap.ext
  intro s
  simp only [Module.End.mul_apply, spinBivector_apply, chiralGrading_apply, map_neg]

/-- Associative algebra identity underlying the vector action of Clifford bivectors. -/
theorem clifford_double_commutator {A : Type*} [Ring A] [Algebra ℝ A]
    (a b c : A) (p q : ℝ)
    (hbc : b * c + c * b = (2 * p) • (1 : A))
    (hac : a * c + c * a = (2 * q) • (1 : A)) :
    (a * b - b * a) * c - c * (a * b - b * a) =
      (4 * p) • a - (4 * q) • b := by
  have hrearrange :
      (a * b - b * a) * c - c * (a * b - b * a) =
        a * (b * c + c * b) - (a * c + c * a) * b -
          b * (a * c + c * a) + (b * c + c * b) * a := by
    simp only [sub_mul, mul_sub, add_mul, mul_add, mul_assoc]
    abel
  rw [hrearrange, hbc, hac]
  simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  module

/-- The factor `1 / 4` converts the double Clifford commutator to the vector normalization. -/
theorem normalized_clifford_commutator {A : Type*} [Ring A] [Algebra ℝ A]
    (a b c : A) (p q : ℝ)
    (hbc : b * c + c * b = (2 * p) • (1 : A))
    (hac : a * c + c * a = (2 * q) • (1 : A)) :
    ((1 / 4 : ℝ) • (a * b - b * a)) * c -
        c * ((1 / 4 : ℝ) • (a * b - b * a)) = p • a - q • b := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub,
    clifford_double_commutator a b c p q hbc hac]
  module

/-- The normalized spin action induces the vector action on Clifford generators. -/
theorem spinBivector_comm_diracGamma (a b v : ZornMatrix ℝ) :
    spinBivector a b * diracGamma v - diracGamma v * spinBivector a b =
      zornBilin b v • diracGamma a - zornBilin a v • diracGamma b := by
  exact normalized_clifford_commutator (diracGamma a) (diracGamma b)
    (diracGamma v) (zornBilin b v) (zornBilin a v)
    (diracGamma_anticommutator b v) (diracGamma_anticommutator a v)

theorem diracGamma_vectorBivector (a b v : ZornMatrix ℝ) :
    diracGamma (vectorBivector a b v) =
      zornBilin b v • diracGamma a - zornBilin a v • diracGamma b := by
  change diracGammaLinear (R := ℝ)
    (zornBilin b v • a - zornBilin a v • b) = _
  simp only [map_sub, map_smul]
  simp only [diracGammaLinear_apply]

theorem spinBivector_comm_diracGamma_eq (a b v : ZornMatrix ℝ) :
    spinBivector a b * diracGamma v - diracGamma v * spinBivector a b =
      diracGamma (vectorBivector a b v) := by
  rw [spinBivector_comm_diracGamma, diracGamma_vectorBivector]

/-- Infinitesimal triality for every pair of vector generators and all Zorn arguments. -/
theorem cartan_infinitesimal_triality (a b v s : ZornMatrix ℝ) :
    spinBivPlus a b (v * s) =
      (vectorBivector a b v) * s + v * (spinBivMinus a b s) := by
  have h := congrArg
    (fun F : Module.End ℝ (DiracSpinor16 (R := ℝ)) => (F (0, s)).1)
    (spinBivector_comm_diracGamma_eq a b v)
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    spinBivector_apply, diracGamma_apply, Prod.fst_sub] at h
  exact eq_add_of_sub_eq h

/-- The complementary chiral block of the same infinitesimal identity. -/
theorem cartan_infinitesimal_triality_conjugate (a b v s : ZornMatrix ℝ) :
    spinBivMinus a b (zornConj v * s) =
      zornConj (vectorBivector a b v) * s + zornConj v * (spinBivPlus a b s) := by
  have h := congrArg
    (fun F : Module.End ℝ (DiracSpinor16 (R := ℝ)) => (F (s, 0)).2)
    (spinBivector_comm_diracGamma_eq a b v)
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    spinBivector_apply, diracGamma_apply, Prod.snd_sub] at h
  exact eq_add_of_sub_eq h

end InfoGeometry.Canonical.ZornCl44Triality
