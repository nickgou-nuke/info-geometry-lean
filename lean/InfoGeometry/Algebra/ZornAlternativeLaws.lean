/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Structural alternative laws for Zorn split octonions

This file derives the middle Moufang identity from the already-proved left and
right alternative laws of `ZornVectorMatrix`.  The proof is characteristic-free:
it linearizes the associator, proves the needed Bruck--Kleinfeld specialization
from four Teichmüller identities, and performs no coordinate enumeration.

References: R. D. Schafer, *An Introduction to Nonassociative Algebras*,
Chapter II; the Bruck--Kleinfeld associator calculus for alternative rings.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

private noncomputable abbrev bundledAssociator
    (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  _root_.associator X Y Z

private lemma bundledAssociator_add_left (X Y Z W : ZornVectorMatrix R) :
    bundledAssociator (X + Y) Z W =
      bundledAssociator X Z W + bundledAssociator Y Z W := by
  simp only [bundledAssociator, _root_.associator_apply, _root_.add_mul]
  abel

private lemma bundledAssociator_add_mid (X Y Z W : ZornVectorMatrix R) :
    bundledAssociator X (Y + Z) W =
      bundledAssociator X Y W + bundledAssociator X Z W := by
  simp only [bundledAssociator, _root_.associator_apply, _root_.add_mul, _root_.mul_add]
  abel

private lemma bundledAssociator_add_right (X Y Z W : ZornVectorMatrix R) :
    bundledAssociator X Y (Z + W) =
      bundledAssociator X Y Z + bundledAssociator X Y W := by
  simp only [bundledAssociator, _root_.associator_apply, _root_.mul_add]
  abel

private lemma bundledAssociator_left_alt (X Y : ZornVectorMatrix R) :
    bundledAssociator X X Y = 0 := by
  change associator X X Y = zero
  exact associator_left_alternative X Y

private lemma bundledAssociator_right_alt (X Y : ZornVectorMatrix R) :
    bundledAssociator X Y Y = 0 := by
  change associator X Y Y = zero
  exact associator_right_alternative X Y

private lemma bundledAssociator_flexible (X Y : ZornVectorMatrix R) :
    bundledAssociator X Y X = 0 := by
  change associator X Y X = zero
  exact associator_flexible X Y

private lemma bundledAssociator_swap12 (X Y Z : ZornVectorMatrix R) :
    bundledAssociator X Y Z = -bundledAssociator Y X Z := by
  have h := bundledAssociator_left_alt (X + Y) Z
  rw [bundledAssociator_add_left, bundledAssociator_add_mid,
    bundledAssociator_add_mid, bundledAssociator_left_alt,
    bundledAssociator_left_alt] at h
  have h' : bundledAssociator X Y Z + bundledAssociator Y X Z = 0 := by
    abel_nf at h ⊢
    exact h
  exact eq_neg_of_add_eq_zero_left h'

private lemma bundledAssociator_swap23 (X Y Z : ZornVectorMatrix R) :
    bundledAssociator X Y Z = -bundledAssociator X Z Y := by
  have h := bundledAssociator_right_alt X (Y + Z)
  rw [bundledAssociator_add_mid, bundledAssociator_add_right,
    bundledAssociator_add_right, bundledAssociator_right_alt,
    bundledAssociator_right_alt] at h
  have h' : bundledAssociator X Y Z + bundledAssociator X Z Y = 0 := by
    abel_nf at h ⊢
    exact h
  exact eq_neg_of_add_eq_zero_left h'

private lemma bundledAssociator_cycle (X Y Z : ZornVectorMatrix R) :
    bundledAssociator Y Z X = bundledAssociator X Y Z := by
  rw [bundledAssociator_swap23, bundledAssociator_swap12]
  abel

private lemma teichmuller (A B C D : ZornVectorMatrix R) :
    bundledAssociator (A * B) C D - bundledAssociator A (B * C) D +
      bundledAssociator A B (C * D) - A * bundledAssociator B C D -
      bundledAssociator A B C * D = 0 := by
  have h := associator_cocycle A B C D
  change _root_.associator (A * B) C D -
    _root_.associator A (B * C) D +
    _root_.associator A B (C * D) - A * _root_.associator B C D -
    _root_.associator A B C * D = 0
  have hn := congrArg Neg.neg h
  simp only [neg_zero] at hn
  abel_nf at hn ⊢
  exact hn

private lemma bundledAssociator_right_product (X Y Z : ZornVectorMatrix R) :
    bundledAssociator X Y (Z * X) = X * bundledAssociator X Y Z := by
  have h1 := teichmuller X X Y Z
  have h2 := teichmuller X X Z Y
  have h3 := teichmuller X Z X Y
  have e1 :
      bundledAssociator (X * X) Y Z - bundledAssociator X (X * Y) Z -
        X * bundledAssociator X Y Z = 0 := by
    rw [bundledAssociator_left_alt X (Y * Z),
      bundledAssociator_left_alt X Y] at h1
    rw [show (0 : ZornVectorMatrix R) * Z = 0 from zero_mul Z] at h1
    abel_nf at h1 ⊢
    exact h1
  rw [bundledAssociator_swap23 (X * X) Z Y,
    bundledAssociator_swap23 X (X * Z) Y, bundledAssociator_left_alt,
    bundledAssociator_swap23 X Z Y, bundledAssociator_left_alt] at h2
  have e2 :
      -bundledAssociator (X * X) Y Z + bundledAssociator X Y (X * Z) +
        X * bundledAssociator X Y Z = 0 := by
    rw [show (0 : ZornVectorMatrix R) * Y = 0 from zero_mul Y] at h2
    change -bundledAssociator (X * X) Y Z -
      -bundledAssociator X Y (X * Z) + 0 -
      X * (-(bundledAssociator X Y Z)) - 0 = 0 at h2
    simp only [_root_.mul_neg] at h2
    abel_nf at h2 ⊢
    exact h2
  have hfirst :
      bundledAssociator (X * Z) X Y = bundledAssociator X Y (X * Z) := by
    rw [bundledAssociator_swap12, bundledAssociator_swap23]
    abel
  have hcycle : bundledAssociator Z X Y = bundledAssociator X Y Z :=
    (bundledAssociator_cycle Z X Y).symm
  rw [hfirst, bundledAssociator_swap23 X (Z * X) Y,
    bundledAssociator_swap23 X Z (X * Y), hcycle,
    bundledAssociator_flexible] at h3
  have e4 :
      bundledAssociator X Y (X * Z) + bundledAssociator X Y (Z * X) -
        bundledAssociator X (X * Y) Z - X * bundledAssociator X Y Z = 0 := by
    rw [show (0 : ZornVectorMatrix R) * Y = 0 from zero_mul Y] at h3
    abel_nf at h3 ⊢
    exact h3
  have hs :
      (bundledAssociator (X * X) Y Z - bundledAssociator X (X * Y) Z -
          X * bundledAssociator X Y Z) +
        (-bundledAssociator (X * X) Y Z + bundledAssociator X Y (X * Z) +
          X * bundledAssociator X Y Z) = 0 := by
    rw [e1, e2, _root_.zero_add]
  have e3 : bundledAssociator X Y (X * Z) = bundledAssociator X (X * Y) Z := by
    have hz :
        bundledAssociator X Y (X * Z) - bundledAssociator X (X * Y) Z = 0 := by
      abel_nf at hs ⊢
      exact hs
    exact sub_eq_zero.mp hz
  rw [e3] at e4
  have hz : bundledAssociator X Y (Z * X) - X * bundledAssociator X Y Z = 0 := by
    abel_nf at e4 ⊢
    exact e4
  exact sub_eq_zero.mp hz

private lemma bundledAssociator_mul_right (X Y Z : ZornVectorMatrix R) :
    bundledAssociator (X * Y) Z X = bundledAssociator X Y Z * X := by
  have h := teichmuller X Y Z X
  rw [bundledAssociator_flexible X (Y * Z),
    bundledAssociator_right_product X Y Z, bundledAssociator_cycle X Y Z] at h
  have hz : bundledAssociator (X * Y) Z X - bundledAssociator X Y Z * X = 0 := by
    abel_nf at h ⊢
    exact h
  exact sub_eq_zero.mp hz

/-- Middle Moufang identity, derived structurally from alternativity. -/
theorem middle_moufang (X Y Z : ZornVectorMatrix R) :
    mul (mul X Y) (mul Z X) = mul X (mul (mul Y Z) X) := by
  change (X * Y) * (Z * X) = X * ((Y * Z) * X)
  have hxy := bundledAssociator_mul_right X Y Z
  have hflex := bundledAssociator_flexible X (Y * Z)
  calc
    (X * Y) * (Z * X) =
        ((X * Y) * Z) * X - bundledAssociator (X * Y) Z X := by
      simp only [bundledAssociator, _root_.associator_apply]
      abel_nf
    _ = ((X * Y) * Z) * X - bundledAssociator X Y Z * X := by rw [hxy]
    _ = (X * (Y * Z)) * X := by
      simp only [bundledAssociator, _root_.associator_apply]
      rw [_root_.sub_mul]
      abel_nf
    _ = X * ((Y * Z) * X) := by
      exact sub_eq_zero.mp hflex

/-- Left Moufang identity, derived structurally from alternativity. -/
theorem left_moufang (X Y Z : ZornVectorMatrix R) :
    mul Z (mul X (mul Z Y)) = mul (mul (mul Z X) Z) Y := by
  change Z * (X * (Z * Y)) = ((Z * X) * Z) * Y
  have h_teich := teichmuller Z X Z Y
  have h_flex := bundledAssociator_flexible Z X
  have h_swap12 := bundledAssociator_swap12 Z X Y
  have h_swap23 := bundledAssociator_swap23 Z Y (X * Z)
  have h_swap23' := bundledAssociator_swap23 Z Y X
  have h_prod := bundledAssociator_right_product Z Y X
  have h_zero : bundledAssociator Z (X * Z) Y + Z * bundledAssociator X Z Y = 0 := by
    rw [bundledAssociator_swap23 Z (X * Z) Y, h_prod, h_swap23', h_swap12]
    abel
  have h_sum : bundledAssociator (Z * X) Z Y + bundledAssociator Z X (Z * Y) = 0 := by
    rw [h_flex] at h_teich
    rw [show (0 : ZornVectorMatrix R) * Y = 0 from zero_mul Y] at h_teich
    have h_teich_rearr : (bundledAssociator (Z * X) Z Y + bundledAssociator Z X (Z * Y)) -
      (bundledAssociator Z (X * Z) Y + Z * bundledAssociator X Z Y) = 0 := by
      abel_nf at h_teich ⊢
      exact h_teich
    have h₁ := h_teich_rearr
    have h₂ := h_zero
    calc
      bundledAssociator (Z * X) Z Y + bundledAssociator Z X (Z * Y) =
          (bundledAssociator (Z * X) Z Y + bundledAssociator Z X (Z * Y) -
            (bundledAssociator Z (X * Z) Y + Z * bundledAssociator X Z Y)) +
          (bundledAssociator Z (X * Z) Y + Z * bundledAssociator X Z Y) := by abel
      _ = 0 := by rw [h₁, h₂]; abel
  have h_def : bundledAssociator (Z * X) Z Y + bundledAssociator Z X (Z * Y) =
      ((Z * X) * Z) * Y - Z * (X * (Z * Y)) := by
    simp only [bundledAssociator, _root_.associator_apply]
    abel
  rw [h_def] at h_sum
  exact (sub_eq_zero.mp h_sum).symm

/-- Right Moufang identity, derived structurally from alternativity. -/
theorem right_moufang (X Y Z : ZornVectorMatrix R) :
    mul (mul (mul Y X) Z) X = mul Y (mul X (mul Z X)) := by
  change ((Y * X) * Z) * X = Y * (X * (Z * X))
  have h_teich := teichmuller Y X Z X
  have h_flex := bundledAssociator_flexible X Z
  have h_swap12 := bundledAssociator_swap12 Y X (X * Z)
  have h_swap12' := bundledAssociator_swap12 (X * Y) X Z
  have h_swap12'' := bundledAssociator_swap12 Y X Z
  have h_swap23 := bundledAssociator_swap23 Y (X * Z) X
  have h_swap23' := bundledAssociator_swap23 (X * Y) Z X
  have h_mul_right := bundledAssociator_mul_right X Y Z
  have e3 : bundledAssociator X Y (X * Z) = bundledAssociator X (X * Y) Z := by
    have h1 := teichmuller X X Y Z
    have h2 := teichmuller X X Z Y
    rw [bundledAssociator_left_alt X (Y * Z), bundledAssociator_left_alt X Y] at h1
    rw [show (0 : ZornVectorMatrix R) * Z = 0 from zero_mul Z] at h1
    have e1 : bundledAssociator (X * X) Y Z - bundledAssociator X (X * Y) Z - X * bundledAssociator X Y Z = 0 := by
      abel_nf at h1 ⊢
      exact h1
    rw [bundledAssociator_swap23 (X * X) Z Y, bundledAssociator_swap23 X (X * Z) Y,
      bundledAssociator_left_alt, bundledAssociator_swap23 X Z Y, bundledAssociator_left_alt] at h2
    have e2 : -bundledAssociator (X * X) Y Z + bundledAssociator X Y (X * Z) + X * bundledAssociator X Y Z = 0 := by
      rw [show (0 : ZornVectorMatrix R) * Y = 0 from zero_mul Y] at h2
      change -bundledAssociator (X * X) Y Z -
        -bundledAssociator X Y (X * Z) + 0 -
        X * (-(bundledAssociator X Y Z)) - 0 = 0 at h2
      simp only [_root_.mul_neg] at h2
      abel_nf at h2 ⊢
      exact h2
    have hs : (bundledAssociator (X * X) Y Z - bundledAssociator X (X * Y) Z - X * bundledAssociator X Y Z) +
      (-bundledAssociator (X * X) Y Z + bundledAssociator X Y (X * Z) + X * bundledAssociator X Y Z) = 0 := by
      rw [e1, e2, _root_.zero_add]
    have hz : bundledAssociator X Y (X * Z) - bundledAssociator X (X * Y) Z = 0 := by
      abel_nf at hs ⊢
      exact hs
    exact sub_eq_zero.mp hz
  have h_zero : bundledAssociator Y (X * Z) X + bundledAssociator Y X Z * X = 0 := by
    have h_calc : bundledAssociator Y (X * Z) X = bundledAssociator X Y Z * X := by
      calc
        bundledAssociator Y (X * Z) X = - bundledAssociator Y X (X * Z) := h_swap23
        _ = bundledAssociator X Y (X * Z) := by rw [h_swap12, neg_neg]
        _ = bundledAssociator X (X * Y) Z := e3
        _ = - bundledAssociator (X * Y) X Z := by rw [bundledAssociator_swap12 X (X * Y) Z]
        _ = bundledAssociator (X * Y) Z X := by rw [← h_swap23']
        _ = bundledAssociator X Y Z * X := h_mul_right
    rw [h_calc, h_swap12'']
    rw [show - bundledAssociator X Y Z * X = - (bundledAssociator X Y Z * X) from neg_mul _ _]
    exact add_neg_cancel (bundledAssociator X Y Z * X)
  have h_sum : bundledAssociator (Y * X) Z X + bundledAssociator Y X (Z * X) = 0 := by
    rw [h_flex] at h_teich
    rw [show Y * (0 : ZornVectorMatrix R) = 0 from mul_zero Y] at h_teich
    have h_teich_rearr : (bundledAssociator (Y * X) Z X + bundledAssociator Y X (Z * X)) -
      (bundledAssociator Y (X * Z) X + bundledAssociator Y X Z * X) = 0 := by
      abel_nf at h_teich ⊢
      exact h_teich
    have h₁ := h_teich_rearr
    have h₂ := h_zero
    calc
      bundledAssociator (Y * X) Z X + bundledAssociator Y X (Z * X) =
          (bundledAssociator (Y * X) Z X + bundledAssociator Y X (Z * X) -
            (bundledAssociator Y (X * Z) X + bundledAssociator Y X Z * X)) +
          (bundledAssociator Y (X * Z) X + bundledAssociator Y X Z * X) := by abel
      _ = 0 := by rw [h₁, h₂]; abel
  have h_def : bundledAssociator (Y * X) Z X + bundledAssociator Y X (Z * X) =
      ((Y * X) * Z) * X - Y * (X * (Z * X)) := by
    simp only [bundledAssociator, _root_.associator_apply]
    abel_nf
  rw [h_def] at h_sum
  exact sub_eq_zero.mp h_sum

/--
Freudenthal's composition identity for an oriented triple.  It combines middle
Moufang with the trace/conjugation equation and Kirmse contraction.
-/
theorem freudenthal_composition (A B C : ZornVectorMatrix R) :
    add (mul (mul A B) (mul C A))
        (smul (norm A) (mul (conj C) (conj B))) =
      smul (trace (mul (mul A B) C)) A := by
  rw [middle_moufang]
  have h := congrArg (mul A) (conj_trace_identity (mul (mul B C) A))
  rw [mul_add, mul_scalar, conj_mul, conj_mul] at h
  have hk := kirmse_left (conj A) (mul (conj C) (conj B))
  rw [conj_conj, norm_conj] at hk
  rw [hk] at h
  rw [← trace_mul_cyclic A B C] at h
  exact h

/-- The cyclic off-diagonal component of the cubic adjoint identity. -/
theorem adjoint_component_composition
    (p q r : R) (X Y Z : ZornVectorMatrix R) :
    ((X * Y - q • conj Z) * (Z * X - p • conj Y) -
      (p * q - norm X) • (conj Z * conj Y - r • X)) =
    (p * q * r - p * norm Y - q * norm Z - r * norm X +
      trace ((X * Y) * Z)) • X := by
  have hcomp := freudenthal_composition X Y Z
  change (X * Y) * (Z * X) + norm X • (conj Z * conj Y) =
    trace ((X * Y) * Z) • X at hcomp
  have hprod : (X * Y) * (Z * X) =
      trace ((X * Y) * Z) • X - norm X • (conj Z * conj Y) :=
    eq_sub_of_add_eq hcomp
  have hY := kirmse_right Y X
  change (X * Y) * conj Y = norm Y • X at hY
  have hZ := kirmse_left Z X
  change conj Z * (Z * X) = norm Z • X at hZ
  change ZornVectorMatrix.sub
      (ZornVectorMatrix.mul
        (ZornVectorMatrix.sub (X * Y) (q • conj Z))
        (ZornVectorMatrix.sub (Z * X) (p • conj Y)))
      ((p * q - norm X) •
        ZornVectorMatrix.sub (conj Z * conj Y) (r • X)) = _
  rw [ZornVectorMatrix.sub_mul, ZornVectorMatrix.mul_sub,
    ZornVectorMatrix.mul_sub]
  have hprod' : ZornVectorMatrix.mul (ZornVectorMatrix.mul X Y)
      (ZornVectorMatrix.mul Z X) =
      ZornVectorMatrix.sub (trace ((X * Y) * Z) • X)
        (norm X • ZornVectorMatrix.mul (conj Z) (conj Y)) := by
    exact hprod
  have hY' : ZornVectorMatrix.mul (ZornVectorMatrix.mul X Y) (conj Y) =
      norm Y • X := hY
  have hZ' : ZornVectorMatrix.mul (conj Z) (ZornVectorMatrix.mul Z X) =
      norm Z • X := hZ
  have hYp : ZornVectorMatrix.mul (ZornVectorMatrix.mul X Y)
      (p • conj Y) = (p * norm Y) • X := by
    calc
      _ = p • ZornVectorMatrix.mul (ZornVectorMatrix.mul X Y) (conj Y) :=
        ZornVectorMatrix.mul_smul p (ZornVectorMatrix.mul X Y) (conj Y)
      _ = (p * norm Y) • X := by rw [hY', smul_smul]
  have hZq : ZornVectorMatrix.mul (q • conj Z)
      (ZornVectorMatrix.mul Z X) = (q * norm Z) • X := by
    calc
      _ = q • ZornVectorMatrix.mul (conj Z) (ZornVectorMatrix.mul Z X) :=
        ZornVectorMatrix.smul_mul q (conj Z) (ZornVectorMatrix.mul Z X)
      _ = (q * norm Z) • X := by rw [hZ', smul_smul]
  have hcross : ZornVectorMatrix.mul (q • conj Z) (p • conj Y) =
      (p * q) • ZornVectorMatrix.mul (conj Z) (conj Y) := by
    calc
      _ = q • ZornVectorMatrix.mul (conj Z) (p • conj Y) :=
        ZornVectorMatrix.smul_mul q (conj Z) (p • conj Y)
      _ = q • (p • ZornVectorMatrix.mul (conj Z) (conj Y)) := by
        exact congrArg (fun W : ZornVectorMatrix R => q • W)
          (ZornVectorMatrix.mul_smul p (conj Z) (conj Y))
      _ = (p * q) • ZornVectorMatrix.mul (conj Z) (conj Y) := by
        rw [smul_smul, mul_comm q p]
  simp only [InfoGeometry.Algebra.zvm_mul_def] at hprod' hY' hZ' ⊢
  rw [hprod', hYp, hZq, hcross]
  simp only [ZornVectorMatrix.sub_eq_add_neg, sub_smul]
  ext <;>
    simp [_root_.sub_eq_add_neg,
      ZornVectorMatrix.add, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul] <;>
    ring

/-- The cyclic diagonal component of the cubic adjoint identity. -/
theorem adjoint_diagonal_composition
    (p q r : R) (X Y Z : ZornVectorMatrix R) :
    (p * r - norm Z) * (p * q - norm X) -
      norm (conj X * conj Z - p • Y) =
    (p * q * r - p * norm Y - q * norm Z - r * norm X +
      trace ((X * Y) * Z)) * p := by
  have hn := norm_sub_eq_norm_add_norm_sub_trace_mul_conj
    (conj X * conj Z) (p • Y)
  change norm (sub (mul (conj X) (conj Z)) (smul p Y)) =
    norm (mul (conj X) (conj Z)) + norm (smul p Y) -
      trace (mul (mul (conj X) (conj Z)) (conj (smul p Y))) at hn
  rw [norm_mul, norm_conj, norm_conj, norm_smul, conj_smul,
    mul_smul, trace_smul, trace_conj_triple_reverse Y Z X] at hn
  rw [← trace_mul_cyclic X Y Z] at hn
  change (p * r - norm Z) * (p * q - norm X) -
      norm (sub (mul (conj X) (conj Z)) (smul p Y)) =
    (p * q * r - p * norm Y - q * norm Z - r * norm X +
      trace (mul (mul X Y) Z)) * p
  rw [hn]
  ring

/-- Polarization of the Zorn norm under addition, in trace-pairing form. -/
theorem norm_add_eq_norm_add_norm_add_trace_mul_conj
    (X Y : ZornVectorMatrix R) :
    norm (add X Y) = norm X + norm Y + trace (mul X (conj Y)) := by
  have h := norm_sub_eq_norm_add_norm_sub_trace_mul_conj X (neg Y)
  have hnn : neg (neg Y) = Y := by
    ext i <;> simp [neg]
  rw [sub, hnn, conj_neg, norm_neg, mul_neg, trace_neg] at h
  simpa using h

/-- The composition-algebra trace pairing `tr(X * conj Y)` is symmetric. -/
theorem trace_mul_conj_comm (X Y : ZornVectorMatrix R) :
    trace (mul X (conj Y)) = trace (mul Y (conj X)) := by
  calc
    trace (mul X (conj Y)) = trace (conj (mul X (conj Y))) :=
      (trace_conj _).symm
    _ = trace (mul Y (conj X)) := by rw [conj_mul, conj_conj]

/-- Two-sided sandwich operator `(K * X) * K` on `ZornVectorMatrix R`. -/
noncomputable def twoSidedSandwich (K X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  mul (mul K X) K

/-- Flexible law `(K * X) * K = K * (X * K)` on `ZornVectorMatrix R`. -/
theorem flexible_law (K X : ZornVectorMatrix R) :
    mul (mul K X) K = mul K (mul X K) := by
  change (K * X) * K = K * (X * K)
  exact sub_eq_zero.mp (bundledAssociator_flexible K X)

/-- Left and right parenthesizations of `twoSidedSandwich K X` coincide by flexibility. -/
theorem twoSidedSandwich_eq_right (K X : ZornVectorMatrix R) :
    twoSidedSandwich K X = mul K (mul X K) :=
  flexible_law K X

/--
Moufang two-sided convolution law: the product of one-sided translates `(K * X) * (Y * K)`
equals the two-sided sandwich `twoSidedSandwich K (X * Y)`.
-/
theorem twoSidedSandwich_mul_convolution (K X Y : ZornVectorMatrix R) :
    mul (mul K X) (mul Y K) = twoSidedSandwich K (mul X Y) := by
  dsimp [twoSidedSandwich]
  rw [middle_moufang K X Y, ← flexible_law K (mul X Y)]

/--
Product of two-sided sandwiches with the same kernel `K` reduces to a single two-sided
sandwich of the inner braided product `(X * K) * (K * Y)`.
-/
theorem twoSidedSandwich_mul_twoSidedSandwich (K X Y : ZornVectorMatrix R) :
    mul (twoSidedSandwich K X) (twoSidedSandwich K Y) =
      twoSidedSandwich K (mul (mul X K) (mul K Y)) := by
  calc
    mul (twoSidedSandwich K X) (twoSidedSandwich K Y) =
        mul (mul K (mul X K)) (mul (mul K Y) K) := by
      rw [twoSidedSandwich_eq_right K X]
      rfl
    _ = twoSidedSandwich K (mul (mul X K) (mul K Y)) :=
      twoSidedSandwich_mul_convolution K (mul X K) (mul K Y)

/-- Left Moufang expansion of `twoSidedSandwich K X * Y`. -/
theorem left_moufang_twoSidedSandwich (K X Y : ZornVectorMatrix R) :
    mul (twoSidedSandwich K X) Y = mul K (mul X (mul K Y)) :=
  (left_moufang X Y K).symm

/-- Right Moufang expansion of `Y * twoSidedSandwich K X`. -/
theorem right_moufang_twoSidedSandwich (K X Y : ZornVectorMatrix R) :
    mul Y (twoSidedSandwich K X) = mul (mul (mul Y K) X) K := by
  rw [twoSidedSandwich_eq_right K X, ← right_moufang K Y X]

/-- Conjugation commutes with `twoSidedSandwich`. -/
theorem conj_twoSidedSandwich (K X : ZornVectorMatrix R) :
    conj (twoSidedSandwich K X) = twoSidedSandwich (conj K) (conj X) := by
  dsimp [twoSidedSandwich]
  rw [conj_mul, conj_mul, ← flexible_law (conj K) (conj X)]

/-- Multiplicativity of the quadratic norm on `twoSidedSandwich K X`. -/
theorem norm_twoSidedSandwich (K X : ZornVectorMatrix R) :
    norm (twoSidedSandwich K X) = norm K * norm X * norm K := by
  dsimp [twoSidedSandwich]
  rw [norm_mul, norm_mul]

/-- Two-sided sandwich of `conj K` by `K` scales `K` by `norm K`. -/
theorem twoSidedSandwich_conj (K : ZornVectorMatrix R) :
    twoSidedSandwich K (conj K) = smul (norm K) K := by
  rw [twoSidedSandwich_eq_right]
  have hk := kirmse_left (conj K) K
  rw [conj_conj, norm_conj] at hk
  exact hk

/-!
## Constructive Three-Color `SplitQuaternion` Embeddings into `ZornVectorMatrix R`
-/

/-- Color-channel embedding `ι_k : Matrix (Fin 2) (Fin 2) R → ZornVectorMatrix R` along axis `k : Fin 3`. -/
def colorChannelEmbed (k : Fin 3) (M : Matrix (Fin 2) (Fin 2) R) : ZornVectorMatrix R :=
  ⟨M 0 0, fun i => M 0 1 * ZornVec3.basis k i, fun i => M 1 0 * ZornVec3.basis k i, M 1 1⟩

/-- First color-channel embedding `ι₀ : Matrix (Fin 2) (Fin 2) R → ZornVectorMatrix R`. -/
abbrev colorChannelEmbed0 (M : Matrix (Fin 2) (Fin 2) R) : ZornVectorMatrix R :=
  colorChannelEmbed 0 M

/-- Second color-channel embedding `ι₁ : Matrix (Fin 2) (Fin 2) R → ZornVectorMatrix R`. -/
abbrev colorChannelEmbed1 (M : Matrix (Fin 2) (Fin 2) R) : ZornVectorMatrix R :=
  colorChannelEmbed 1 M

/-- Third color-channel embedding `ι₂ : Matrix (Fin 2) (Fin 2) R → ZornVectorMatrix R`. -/
abbrev colorChannelEmbed2 (M : Matrix (Fin 2) (Fin 2) R) : ZornVectorMatrix R :=
  colorChannelEmbed 2 M

/-- Upper nilpotent seed `matSeedD = !![0, 1; 0, 0]`. -/
def matSeedD : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

/-- Lower nilpotent seed `matSeedB = !![0, 0; 1, 0]`. -/
def matSeedB : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]

/-- Positive Peirce pole `matPeircePlus = !![1, 0; 0, 0]`. -/
def matPeircePlus : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, 0]

/-- Negative Peirce pole `matPeirceMinus = !![0, 0; 0, 1]`. -/
def matPeirceMinus : Matrix (Fin 2) (Fin 2) R := !![0, 0; 0, 1]

/-- Noncommutative commutator of `matSeedD` and `matSeedB` is `matPeircePlus - matPeirceMinus`. -/
theorem matSeedD_comm_matSeedB :
    (matSeedD : Matrix (Fin 2) (Fin 2) R) * matSeedB - matSeedB * matSeedD =
      matPeircePlus - matPeirceMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matSeedD, matSeedB, matPeircePlus, matPeirceMinus]

/-- Explicit noncommutativity of `matPeircePlus` and `matSeedD` over any nontrivial ring. -/
theorem matPeircePlus_mul_matSeedD_ne [Nontrivial R] :
    (matPeircePlus : Matrix (Fin 2) (Fin 2) R) * matSeedD ≠ matSeedD * matPeircePlus := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [matPeircePlus, matSeedD] at h01

/-- **Single-Channel Multiplicative Homomorphism (`colorChannelEmbed_mul`)**:
    Within each individual color channel `k ∈ {0, 1, 2}`, embedding `2 × 2` matrices into
    `ZornVectorMatrix R` is an exact multiplicative homomorphism:
    `ι_k(M * N) = ι_k(M) * ι_k(N)`. -/
theorem colorChannelEmbed_mul (M N : Matrix (Fin 2) (Fin 2) R) :
    colorChannelEmbed0 (M * N) = colorChannelEmbed0 M * colorChannelEmbed0 N ∧
    colorChannelEmbed1 (M * N) = colorChannelEmbed1 M * colorChannelEmbed1 N ∧
    colorChannelEmbed2 (M * N) = colorChannelEmbed2 M * colorChannelEmbed2 N := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext
    · simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
            InfoGeometry.Algebra.zvm_mul_def, mul, Matrix.mul_apply, Fin.sum_univ_two,
            ZornVec3.dot, ZornVec3.basis]
    · rename_i i
      (fin_cases i <;>
        simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
              InfoGeometry.Algebra.zvm_mul_def, mul, Matrix.mul_apply, Fin.sum_univ_two,
              ZornVec3.cross, ZornVec3.basis]); ring
    · rename_i i
      (fin_cases i <;>
        simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
              InfoGeometry.Algebra.zvm_mul_def, mul, Matrix.mul_apply, Fin.sum_univ_two,
              ZornVec3.cross, ZornVec3.basis]); ring
    · simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
            InfoGeometry.Algebra.zvm_mul_def, mul, Matrix.mul_apply, Fin.sum_univ_two,
            ZornVec3.dot, ZornVec3.basis]

/-- **Single-Channel Norm–Determinant Identity (`norm_colorChannelEmbed_eq_det`)**:
    On each color channel `k ∈ {0, 1, 2}`, Cartan's signature-(4,4) Zorn norm restricts
    to the exact `2 × 2` matrix determinant `M 0 0 * M 1 1 - M 0 1 * M 1 0`. -/
theorem norm_colorChannelEmbed_eq_det (M : Matrix (Fin 2) (Fin 2) R) :
    norm (colorChannelEmbed0 M) = Matrix.det M ∧
    norm (colorChannelEmbed1 M) = Matrix.det M ∧
    norm (colorChannelEmbed2 M) = Matrix.det M := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [norm, colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
          ZornVec3.dot, ZornVec3.basis, Matrix.det_fin_two]

/-- **Cross-Channel Diquark Seed Fusion (`cross_channel_seed_fusion`)**:
    Whereas `matSeedD * matSeedD = 0` within any single color channel, multiplying
    `matSeedD` across two distinct color channels (`ι₀` and `ι₁`) fuses them into
    the dual lower seed `matSeedB` in the third color channel `ι₂`! -/
theorem cross_channel_seed_fusion :
    colorChannelEmbed0 (matSeedD : Matrix (Fin 2) (Fin 2) R) *
      colorChannelEmbed1 matSeedD = colorChannelEmbed2 matSeedB ∧
    colorChannelEmbed0 (matSeedB : Matrix (Fin 2) (Fin 2) R) *
      colorChannelEmbed1 matSeedB = -colorChannelEmbed2 matSeedD := by
  refine ⟨?_, ?_⟩ <;>
  · ext
    · simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
            matSeedD, matSeedB, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_neg_def, mul, neg, ZornVec3.dot, ZornVec3.basis]
    · rename_i i
      fin_cases i <;>
        simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
              matSeedD, matSeedB, InfoGeometry.Algebra.zvm_mul_def,
              InfoGeometry.Algebra.zvm_neg_def, mul, neg, ZornVec3.cross, ZornVec3.basis]
    · rename_i i
      fin_cases i <;>
        simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
              matSeedD, matSeedB, InfoGeometry.Algebra.zvm_mul_def,
              InfoGeometry.Algebra.zvm_neg_def, mul, neg, ZornVec3.cross, ZornVec3.basis]
    · simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
            matSeedD, matSeedB, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_neg_def, mul, neg, ZornVec3.dot, ZornVec3.basis]

/-- **Three-Channel Baryon Associator Split (`three_channel_baryon_associator_poles`)**:
    Multiplying the upper nilpotent seed `matSeedD` across all three color channels `(0, 1, 2)`
    yields the negative Peirce pole `ι₂(matPeirceMinus) = ⟨0, 0, 0, 1⟩` in left-associated order
    and the positive Peirce pole `ι₀(matPeircePlus) = ⟨1, 0, 0, 0⟩` in right-associated order! -/
theorem three_channel_baryon_associator_poles :
    (colorChannelEmbed0 (matSeedD : Matrix (Fin 2) (Fin 2) R) *
      colorChannelEmbed1 matSeedD) * colorChannelEmbed2 matSeedD =
      colorChannelEmbed2 matPeirceMinus ∧
    colorChannelEmbed0 (matSeedD : Matrix (Fin 2) (Fin 2) R) *
      (colorChannelEmbed1 matSeedD * colorChannelEmbed2 matSeedD) =
      colorChannelEmbed0 matPeircePlus := by
  refine ⟨?_, ?_⟩ <;>
  · ext
    · simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
            matSeedD, matPeircePlus, matPeirceMinus, InfoGeometry.Algebra.zvm_mul_def,
            mul, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    · rename_i i
      fin_cases i <;>
        simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
              matSeedD, matPeircePlus, matPeirceMinus, InfoGeometry.Algebra.zvm_mul_def,
              mul, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    · rename_i i
      fin_cases i <;>
        simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
              matSeedD, matPeircePlus, matPeirceMinus, InfoGeometry.Algebra.zvm_mul_def,
              mul, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    · simp [colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed2, colorChannelEmbed,
            matSeedD, matPeircePlus, matPeirceMinus, InfoGeometry.Algebra.zvm_mul_def,
            mul, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

/-!
## 6. Erlangen 2.0 on `ZornVectorMatrix R`: Emergent 6D Metric, Spin Curvature, & Color Torsion
-/

/-- Zorn Cartan grading involution `zornGamma = ⟨1, 0, 0, -1⟩` (`zornGamma² = one`). -/
def zornGamma : ZornVectorMatrix R :=
  ⟨1, fun _ => 0, fun _ => 0, -1⟩

/-- Even 2D singlet spin-connection projection `ω_Zorn(X) = diagonalPart X = ⟨X.a, 0, 0, X.b⟩`. -/
abbrev zornSpinConnectionPart (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  diagonalPart X

/-- Odd 6D colored frame projection `e_Zorn(X) = offDiagonalPart X = ⟨0, X.v, X.w, 0⟩`. -/
abbrev zornSpacetimeFramePart (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  offDiagonalPart X

/-- Emergent 6D split-metric bilinear `g_Zorn(X, Y) = X.v ⋅ Y.w + X.w ⋅ Y.v`. -/
def zornEmergentMetric (X Y : ZornVectorMatrix R) : R :=
  ZornVec3.dot X.v Y.w + ZornVec3.dot X.w Y.v

/-- Emergent Riemann–Cartan singlet curvature scalar `R_Zorn(X, Y) = X.v ⋅ Y.w - X.w ⋅ Y.v`. -/
def zornEmergentCurvature (X Y : ZornVectorMatrix R) : R :=
  ZornVec3.dot X.v Y.w - ZornVec3.dot X.w Y.v

/-- Octonionic color cross-product torsion `T_color(X, Y) = ⟨0, -2(X.w × Y.w), 2(X.v × Y.v), 0⟩`. -/
def zornColorCrossTorsion (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨0, fun i => (-2 : R) * ZornVec3.cross X.w Y.w i,
      fun i => (2 : R) * ZornVec3.cross X.v Y.v i, 0⟩

/-- **Cartan Decomposition of `ZornVectorMatrix R` into Singlet Spin Connection `⊕` 6D Frame**. -/
theorem zorn_cartan_connection_frame_split (X : ZornVectorMatrix R) :
    zornSpinConnectionPart X + zornSpacetimeFramePart X = X ∧
    (zornGamma * zornSpinConnectionPart X) * zornGamma = zornSpinConnectionPart X ∧
    (zornGamma * zornSpacetimeFramePart X) * zornGamma = -zornSpacetimeFramePart X := by
  refine ⟨diagonalPart_add_offDiagonalPart X, ?_, ?_⟩ <;>
  · ext
    · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
            zornGamma, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_neg_def,
            mul, neg]
    · rename_i i
      fin_cases i <;>
        simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
              zornGamma, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_neg_def,
              mul, neg, ZornVec3.cross]
    · rename_i i
      fin_cases i <;>
        simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
              zornGamma, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_neg_def,
              mul, neg, ZornVec3.cross]
    · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
            zornGamma, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_neg_def,
            mul, neg]

/-- **Emergent 6D Split-Metric Theorem (`zornSpacetimeFrame_anticommutator_eq_metric`)**:
    In the Jordan anticommutator `{e_Zorn(X), e_Zorn(Y)}` of any two 6D frame elements,
    the non-associative cross products `X.v × Y.v` and `X.w × Y.w` cancel identically,
    leaving a pure scalar multiple of the identity `one`! -/
theorem zornSpacetimeFrame_anticommutator_eq_metric (X Y : ZornVectorMatrix R) :
    zornSpacetimeFramePart X * zornSpacetimeFramePart Y +
    zornSpacetimeFramePart Y * zornSpacetimeFramePart X =
      zornEmergentMetric X Y • (one : ZornVectorMatrix R) := by
  ext
  · simp [zornSpacetimeFramePart, offDiagonalPart, zornEmergentMetric, one,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
          InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.dot_comm]
  · rename_i i
    fin_cases i <;>
      (simp [zornSpacetimeFramePart, offDiagonalPart, zornEmergentMetric, one,
             InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
             InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.cross]; ring)
  · rename_i i
    fin_cases i <;>
      (simp [zornSpacetimeFramePart, offDiagonalPart, zornEmergentMetric, one,
             InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
             InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.cross]; ring)
  · simp [zornSpacetimeFramePart, offDiagonalPart, zornEmergentMetric, one,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
          InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.dot_comm]
    ring

/-- **Frame Commutator Splits into Singlet Riemann Curvature `⊕` Octonionic Color Torsion**. -/
theorem zornSpacetimeFrame_commutator_curvature_and_color_torsion
    (X Y : ZornVectorMatrix R) :
    zornSpinConnectionPart
      (zornSpacetimeFramePart X * zornSpacetimeFramePart Y -
       zornSpacetimeFramePart Y * zornSpacetimeFramePart X) =
      zornEmergentCurvature X Y • zornGamma ∧
    zornSpacetimeFramePart
      (zornSpacetimeFramePart X * zornSpacetimeFramePart Y -
       zornSpacetimeFramePart Y * zornSpacetimeFramePart X) =
      zornColorCrossTorsion X Y ∧
    zornSpacetimeFramePart X * zornSpacetimeFramePart Y -
    zornSpacetimeFramePart Y * zornSpacetimeFramePart X =
      zornEmergentCurvature X Y • zornGamma + zornColorCrossTorsion X Y := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [_root_.sub_eq_add_neg]
    ext
    · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
            zornEmergentCurvature, zornColorCrossTorsion, zornGamma,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot_comm]
      try ring
    · rename_i i
      fin_cases i <;>
        (simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
               zornEmergentCurvature, zornColorCrossTorsion, zornGamma,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, neg, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
               zornEmergentCurvature, zornColorCrossTorsion, zornGamma,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, neg, mul, smul, ZornVec3.cross]; try ring)
    · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
            zornEmergentCurvature, zornColorCrossTorsion, zornGamma,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot_comm]
      try ring

/-- **Cartan Covariant Derivative `[ω_Zorn(X), e_Zorn(Y)]` Lands Purely in the 6D Frame**:
    For any `X, Y : ZornVectorMatrix R`, the commutator of the 2D singlet spin connection
    `zornSpinConnectionPart X` with the 6D frame `zornSpacetimeFramePart Y` has zero diagonal
    part and lands purely in the 6D colored frame! -/
theorem zornSpinConnection_spacetimeFrame_commutator_in_frame
    (X Y : ZornVectorMatrix R) :
    zornSpinConnectionPart
      (zornSpinConnectionPart X * zornSpacetimeFramePart Y -
       zornSpacetimeFramePart Y * zornSpinConnectionPart X) = zero ∧
    zornSpacetimeFramePart
      (zornSpinConnectionPart X * zornSpacetimeFramePart Y -
       zornSpacetimeFramePart Y * zornSpinConnectionPart X) =
      zornSpinConnectionPart X * zornSpacetimeFramePart Y -
      zornSpacetimeFramePart Y * zornSpinConnectionPart X := by
  refine ⟨?_, ?_⟩ <;>
  · rw [_root_.sub_eq_add_neg]
    ext
    · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
            zero, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, add, neg, mul]
    · rename_i i
      fin_cases i <;>
        (simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
               zero, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, add, neg, mul, ZornVec3.cross]; try ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
               zero, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, add, neg, mul, ZornVec3.cross]; try ring)
    · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
            zero, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, add, neg, mul]

/-- Diagonal hyperbolic gauge boost element `⟨u, 0, 0, u⁻¹⟩` in `ZornVectorMatrix R`. -/
def zornHyperbolicKernel (lam mu : R) : ZornVectorMatrix R :=
  ⟨lam, fun _ => 0, fun _ => 0, mu⟩

/-- Two-sided hyperbolic gauge boost `K(lamL, muL) * X * K(lamR, muR)` on `ZornVectorMatrix R`. -/
noncomputable def zornTwoSidedHyperbolicLaplace (lamL muL lamR muR : R) (X : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  (zornHyperbolicKernel lamL muL * X) * zornHyperbolicKernel lamR muR

/-- **Local Hyperbolic Gauge Boost Invariance of the 6D Emergent Metric, Curvature, and Norm (`u : Rˣ`)**:
    Under the antisymmetric two-sided hyperbolic gauge boost `L_{u, u⁻¹, u⁻¹, u}` (`u : Rˣ`),
    the 6D emergent split-metric `zornEmergentMetric`, the Riemann–Cartan singlet curvature
    `zornEmergentCurvature`, and the Zorn quadratic norm `norm` are all strictly invariant! -/
theorem zornEmergentMetric_and_curvature_gauge_invariant
    (u : Rˣ) (X Y : ZornVectorMatrix R) :
    zornEmergentMetric
      (zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) X)
      (zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) Y) =
      zornEmergentMetric X Y ∧
    zornEmergentCurvature
      (zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) X)
      (zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) Y) =
      zornEmergentCurvature X Y ∧
    norm (zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) X) =
      norm X := by
  have hu : (u : R) * (↑u⁻¹ : R) = 1 := Units.mul_inv u
  refine ⟨?_, ?_, ?_⟩
  · simp [zornEmergentMetric, zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
          InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, ZornVec3.cross,
          Fin.sum_univ_three]
    calc
      ((u : R) * ((u : R) * X.v 0) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * Y.w 0)) +
       (u : R) * ((u : R) * X.v 1) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * Y.w 1)) +
       (u : R) * ((u : R) * X.v 2) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * Y.w 2))) +
      ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * X.w 0) * ((u : R) * ((u : R) * Y.v 0)) +
       (↑u⁻¹ : R) * ((↑u⁻¹ : R) * X.w 1) * ((u : R) * ((u : R) * Y.v 1)) +
       (↑u⁻¹ : R) * ((↑u⁻¹ : R) * X.w 2) * ((u : R) * ((u : R) * Y.v 2))) =
      ((u : R) * (↑u⁻¹ : R)) * ((u : R) * (↑u⁻¹ : R)) *
        (X.v 0 * Y.w 0 + X.v 1 * Y.w 1 + X.v 2 * Y.w 2 +
         (X.w 0 * Y.v 0 + X.w 1 * Y.v 1 + X.w 2 * Y.v 2)) := by ring
      _ = (X.v 0 * Y.w 0 + X.v 1 * Y.w 1 + X.v 2 * Y.w 2) +
          (X.w 0 * Y.v 0 + X.w 1 * Y.v 1 + X.w 2 * Y.v 2) := by
        simp [hu]
  · simp [zornEmergentCurvature, zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
          InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, ZornVec3.cross,
          Fin.sum_univ_three]
    calc
      ((u : R) * ((u : R) * X.v 0) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * Y.w 0)) +
       (u : R) * ((u : R) * X.v 1) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * Y.w 1)) +
       (u : R) * ((u : R) * X.v 2) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * Y.w 2))) -
      ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * X.w 0) * ((u : R) * ((u : R) * Y.v 0)) +
       (↑u⁻¹ : R) * ((↑u⁻¹ : R) * X.w 1) * ((u : R) * ((u : R) * Y.v 1)) +
       (↑u⁻¹ : R) * ((↑u⁻¹ : R) * X.w 2) * ((u : R) * ((u : R) * Y.v 2))) =
      ((u : R) * (↑u⁻¹ : R)) * ((u : R) * (↑u⁻¹ : R)) *
        ((X.v 0 * Y.w 0 + X.v 1 * Y.w 1 + X.v 2 * Y.w 2) -
         (X.w 0 * Y.v 0 + X.w 1 * Y.v 1 + X.w 2 * Y.v 2)) := by ring
      _ = (X.v 0 * Y.w 0 + X.v 1 * Y.w 1 + X.v 2 * Y.w 2) -
          (X.w 0 * Y.v 0 + X.w 1 * Y.v 1 + X.w 2 * Y.v 2) := by
        simp [hu]
  · simp [norm, zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
          InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, ZornVec3.cross,
          Fin.sum_univ_three]
    calc
      (u : R) * X.a * (↑u⁻¹ : R) * ((↑u⁻¹ : R) * X.b * (u : R)) -
      ((u : R) * ((u : R) * X.v 0) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * X.w 0)) +
       (u : R) * ((u : R) * X.v 1) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * X.w 1)) +
       (u : R) * ((u : R) * X.v 2) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * X.w 2))) =
      ((u : R) * (↑u⁻¹ : R)) * ((u : R) * (↑u⁻¹ : R)) *
        (X.a * X.b - (X.v 0 * X.w 0 + X.v 1 * X.w 1 + X.v 2 * X.w 2)) := by ring
      _ = X.a * X.b - (X.v 0 * X.w 0 + X.v 1 * X.w 1 + X.v 2 * X.w 2) := by
        simp [hu]

/-- **Same-Channel Torsion Vanishing (`zornColorCrossTorsion_same_channel_zero`)**:
    Within any single color channel `ι_k` (`k ∈ {0, 1, 2}`), the octonionic color torsion
    vanishes identically, so `[e(ι_k(M)), e(ι_k(N))]` is pure Riemann spin curvature! -/
theorem zornColorCrossTorsion_same_channel_zero (M N : Matrix (Fin 2) (Fin 2) R) :
    zornColorCrossTorsion (colorChannelEmbed0 M) (colorChannelEmbed0 N) = zero ∧
    zornColorCrossTorsion (colorChannelEmbed1 M) (colorChannelEmbed1 N) = zero ∧
    zornColorCrossTorsion (colorChannelEmbed2 M) (colorChannelEmbed2 N) = zero := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext
    · rfl
    · rename_i i
      fin_cases i <;>
        simp [zornColorCrossTorsion, colorChannelEmbed0, colorChannelEmbed1,
              colorChannelEmbed2, colorChannelEmbed, zero, ZornVec3.cross,
              ZornVec3.basis]
    · rename_i i
      fin_cases i <;>
        simp [zornColorCrossTorsion, colorChannelEmbed0, colorChannelEmbed1,
              colorChannelEmbed2, colorChannelEmbed, zero, ZornVec3.cross,
              ZornVec3.basis]
    · rfl

/-- **Cross-Channel Pure Color Torsion (`zornCrossChannel_pure_color_torsion`)**:
    Across distinct color channels (`ι₀(M)` and `ι₁(N)`), both the emergent metric and
    singlet curvature vanish (`g = 0, R = 0`), and the frame commutator is purely
    octonionic color torsion in the third channel `ι₂`! -/
theorem zornCrossChannel_pure_color_torsion (M N : Matrix (Fin 2) (Fin 2) R) :
    zornEmergentMetric (colorChannelEmbed0 M) (colorChannelEmbed1 N) = 0 ∧
    zornEmergentCurvature (colorChannelEmbed0 M) (colorChannelEmbed1 N) = 0 ∧
    zornSpacetimeFramePart (colorChannelEmbed0 M) *
      zornSpacetimeFramePart (colorChannelEmbed1 N) -
    zornSpacetimeFramePart (colorChannelEmbed1 N) *
      zornSpacetimeFramePart (colorChannelEmbed0 M) =
      colorChannelEmbed2 !![0, (-2 : R) * (M 1 0 * N 1 0); (2 : R) * (M 0 1 * N 0 1), 0] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [zornEmergentMetric, colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed,
          ZornVec3.dot, ZornVec3.basis]
  · simp [zornEmergentCurvature, colorChannelEmbed0, colorChannelEmbed1, colorChannelEmbed,
          ZornVec3.dot, ZornVec3.basis]
  · rw [_root_.sub_eq_add_neg]
    ext
    · simp [zornSpacetimeFramePart, offDiagonalPart, colorChannelEmbed0, colorChannelEmbed1,
            colorChannelEmbed2, colorChannelEmbed, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            add, neg, mul, ZornVec3.dot, ZornVec3.basis]
    · rename_i i
      fin_cases i <;>
        (simp [zornSpacetimeFramePart, offDiagonalPart, colorChannelEmbed0, colorChannelEmbed1,
               colorChannelEmbed2, colorChannelEmbed, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               add, neg, mul, ZornVec3.cross, ZornVec3.basis]; try ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornSpacetimeFramePart, offDiagonalPart, colorChannelEmbed0, colorChannelEmbed1,
               colorChannelEmbed2, colorChannelEmbed, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               add, neg, mul, ZornVec3.cross, ZornVec3.basis]; try ring)
    · simp [zornSpacetimeFramePart, offDiagonalPart, colorChannelEmbed0, colorChannelEmbed1,
            colorChannelEmbed2, colorChannelEmbed, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            add, neg, mul, ZornVec3.dot, ZornVec3.basis]

/-- Classical 3D Nambu volume determinant `zornNambuDet u v w = u ⋅ (v × w)`. -/
def zornNambuDet (u v w : ZornVec3 R) : R :=
  ZornVec3.dot u (ZornVec3.cross v w)

/-- Non-associative Zorn associator `[X, Y, Z] = (X * Y) * Z - X * (Y * Z)`. -/
noncomputable def zornAssociator (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  (X * Y) * Z - X * (Y * Z)

/-- Antisymmetric commutator `[X, Y] = X * Y - Y * X` on `ZornVectorMatrix R`. -/
noncomputable def zornComm (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  X * Y - Y * X

/-- Cyclic Lie Jacobiator `J(X, Y, Z) = [X, [Y, Z]] + [Y, [Z, X]] + [Z, [X, Y]]`. -/
noncomputable def zornJacobiator (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  zornComm X (zornComm Y Z) + zornComm Y (zornComm Z X) + zornComm Z (zornComm X Y)

/-- **Universal Malcev–Zorn `S₃` Identity (`zornJacobiator_eq_neg_six_smul_zornAssociator`)**:
    Explains why the combinatorial factor `6 = |S₃|` appears in the Nambu–Bianchi law: for ANY
    three elements `X, Y, Z : ZornVectorMatrix R` (with zero hypotheses!), the cyclic Lie
    Jacobiator is identically `-6` times the non-associative associator! -/
theorem zornJacobiator_eq_neg_six_smul_zornAssociator
    (X Y Z : ZornVectorMatrix R) :
    zornJacobiator X Y Z = (-6 : R) • zornAssociator X Y Z := by
  have h_expand :
      zornJacobiator X Y Z =
        -bundledAssociator X Y Z - bundledAssociator Y Z X - bundledAssociator Z X Y +
        bundledAssociator X Z Y + bundledAssociator Y X Z + bundledAssociator Z Y X := by
    simp only [zornJacobiator, zornComm, bundledAssociator, _root_.associator_apply,
      _root_.mul_sub, _root_.sub_mul]
    abel
  have h_yzx : bundledAssociator Y Z X = bundledAssociator X Y Z :=
    bundledAssociator_cycle X Y Z
  have h_zxy : bundledAssociator Z X Y = bundledAssociator X Y Z :=
    (bundledAssociator_cycle Y Z X).trans h_yzx
  have h_xzy : bundledAssociator X Z Y = -bundledAssociator X Y Z := by
    rw [bundledAssociator_swap23 X Y Z, neg_neg]
  have h_yxz : bundledAssociator Y X Z = -bundledAssociator X Y Z := by
    rw [bundledAssociator_swap12 X Y Z, neg_neg]
  have h_zyx : bundledAssociator Z Y X = -bundledAssociator X Y Z :=
    (bundledAssociator_cycle Z Y X).symm.trans h_yxz
  have h_sum :
      zornJacobiator X Y Z =
        -(bundledAssociator X Y Z + bundledAssociator X Y Z + bundledAssociator X Y Z +
          bundledAssociator X Y Z + bundledAssociator X Y Z + bundledAssociator X Y Z) := by
    rw [h_expand, h_yzx, h_zxy, h_xzy, h_yxz, h_zyx]
    abel
  rw [h_sum]
  change -(zornAssociator X Y Z + zornAssociator X Y Z + zornAssociator X Y Z +
           zornAssociator X Y Z + zornAssociator X Y Z + zornAssociator X Y Z) =
         (-6 : R) • zornAssociator X Y Z
  ext
  · simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          InfoGeometry.Algebra.zvm_smul_def, add, neg, smul]; ring
  · rename_i i
    fin_cases i <;>
      (simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_smul_def, add, neg, smul]; ring)
  · rename_i i
    fin_cases i <;>
      (simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_smul_def, add, neg, smul]; ring)
  · simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          InfoGeometry.Algebra.zvm_smul_def, add, neg, smul]; ring

/-- **Unit-Coefficient Associator–Nambu Theorem (`zornSpacetimeFrame_associator_spinConnectionPart_eq_neg_nambu`)**:
    For any three 6D frame elements `e(X), e(Y), e(Z)`, the singlet spin-connection projection
    of their non-associative associator `[e(X), e(Y), e(Z)]` has unit coefficient `-1` times
    the sum of the quark and antiquark Nambu 3-Bracket volumes along `zornGamma`! -/
theorem zornSpacetimeFrame_associator_spinConnectionPart_eq_neg_nambu
    (X Y Z : ZornVectorMatrix R) :
    zornSpinConnectionPart
      (zornAssociator (zornSpacetimeFramePart X)
                      (zornSpacetimeFramePart Y)
                      (zornSpacetimeFramePart Z)) =
      (-(zornNambuDet X.v Y.v Z.v + zornNambuDet X.w Y.w Z.w)) • zornGamma := by
  unfold zornAssociator
  simp only [_root_.sub_eq_add_neg]
  ext
  · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
          zornGamma, zornNambuDet, InfoGeometry.Algebra.zvm_add_def,
          InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
          InfoGeometry.Algebra.zvm_smul_def, add, neg, mul, smul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · rename_i i
    fin_cases i <;>
      simp [zornSpinConnectionPart, diagonalPart, zornGamma,
            InfoGeometry.Algebra.zvm_smul_def, smul]
  · rename_i i
    fin_cases i <;>
      simp [zornSpinConnectionPart, diagonalPart, zornGamma,
            InfoGeometry.Algebra.zvm_smul_def, smul]
  · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
          zornGamma, zornNambuDet, InfoGeometry.Algebra.zvm_add_def,
          InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
          InfoGeometry.Algebra.zvm_smul_def, add, neg, mul, smul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

/-- **The Nambu–Bianchi Frame Jacobiator Theorem (`zornSpacetimeFrame_jacobiator_spinConnectionPart_eq_nambu`)**:
    For any three 6D frame elements `e(X), e(Y), e(Z)`, the even singlet spin-connection
    projection of their cyclic Lie Jacobiator is `6` times the sum of the quark and
    antiquark Nambu 3-Bracket volumes along `zornGamma`:
    `ω_Zorn(J(e(X), e(Y), e(Z))) = ((6 : R) * (zornNambuDet X.v Y.v Z.v + zornNambuDet X.w Y.w Z.w)) • zornGamma`! -/
theorem zornSpacetimeFrame_jacobiator_spinConnectionPart_eq_nambu
    (X Y Z : ZornVectorMatrix R) :
    zornSpinConnectionPart
      (zornJacobiator (zornSpacetimeFramePart X)
                      (zornSpacetimeFramePart Y)
                      (zornSpacetimeFramePart Z)) =
      ((6 : R) * (zornNambuDet X.v Y.v Z.v + zornNambuDet X.w Y.w Z.w)) • zornGamma := by
  unfold zornJacobiator zornComm
  simp only [_root_.sub_eq_add_neg]
  ext
  · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
          zornGamma, zornNambuDet, InfoGeometry.Algebra.zvm_add_def,
          InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
          InfoGeometry.Algebra.zvm_smul_def, add, neg, mul, smul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · rename_i i
    fin_cases i <;>
      simp [zornSpinConnectionPart, diagonalPart, zornGamma,
            InfoGeometry.Algebra.zvm_smul_def, smul]
  · rename_i i
    fin_cases i <;>
      simp [zornSpinConnectionPart, diagonalPart, zornGamma,
            InfoGeometry.Algebra.zvm_smul_def, smul]
  · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
          zornGamma, zornNambuDet, InfoGeometry.Algebra.zvm_add_def,
          InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
          InfoGeometry.Algebra.zvm_smul_def, add, neg, mul, smul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

/-!
## 7. Tamm–Dancoff Singlet–Triplet Companionship & Nambu 3-Bracket Extraction
-/

/-- **Two-Body Tamm–Dancoff Product Decomposition into Singlet Dot + Triplet Cross**:
    The product of any two 6D triplet frame states `e(X)` and `e(Y)` has Singlet part
    `⟨X.v ⋅ Y.w, 0, 0, X.w ⋅ Y.v⟩` and Triplet part `⟨0, -(X.w × Y.w), X.v × Y.v, 0⟩`. -/
theorem zorn_tamm_dancoff_two_body_singlet_triplet_parts (X Y : ZornVectorMatrix R) :
    zornSpinConnectionPart (zornSpacetimeFramePart X * zornSpacetimeFramePart Y) =
      ⟨ZornVec3.dot X.v Y.w, fun _ => 0, fun _ => 0, ZornVec3.dot X.w Y.v⟩ ∧
    zornSpacetimeFramePart (zornSpacetimeFramePart X * zornSpacetimeFramePart Y) =
      ⟨0, fun i => -ZornVec3.cross X.w Y.w i, fun i => ZornVec3.cross X.v Y.v i, 0⟩ := by
  refine ⟨?_, ?_⟩ <;>
  · ext
    · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
            InfoGeometry.Algebra.zvm_mul_def, mul]
    · rename_i i
      fin_cases i <;>
        simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
              InfoGeometry.Algebra.zvm_mul_def, mul]
    · rename_i i
      fin_cases i <;>
        simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
              InfoGeometry.Algebra.zvm_mul_def, mul]
    · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
            InfoGeometry.Algebra.zvm_mul_def, mul]

/-- **Binet–Cauchy–Zorn Singlet–Triplet Norm Conservation (`zorn_tamm_dancoff_singlet_triplet_norm_conservation`)**:
    For any two 6D triplet states `e(X)` and `e(Y)`, the sum of the norm of the Singlet channel
    `ω_Zorn(e(X) * e(Y))` and the norm of the Triplet channel `e_Zorn(e(X) * e(Y))` equals the
    product of the incoming triplet norms! -/
theorem zorn_tamm_dancoff_singlet_triplet_norm_conservation (X Y : ZornVectorMatrix R) :
    norm (zornSpinConnectionPart (zornSpacetimeFramePart X * zornSpacetimeFramePart Y)) +
    norm (zornSpacetimeFramePart (zornSpacetimeFramePart X * zornSpacetimeFramePart Y)) =
      norm (zornSpacetimeFramePart X) * norm (zornSpacetimeFramePart Y) := by
  simp [norm, zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
        InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three]
  ring

/-- **Tamm–Dancoff Triplet-to-Nambu Singlet Extraction (`zorn_tamm_dancoff_triplet_to_nambu_singlet`)**:
    Multiplying the intermediate Tamm–Dancoff diquark triplet `e_Zorn(e(X) * e(Y))` by a third
    triplet `e(Z)` and projecting onto the Singlet sector `ω_Zorn` extracts the exact Nambu
    3-Determinant pair `⟨-zornNambuDet X.w Y.w Z.w, 0, 0, zornNambuDet X.v Y.v Z.v⟩`! -/
theorem zorn_tamm_dancoff_triplet_to_nambu_singlet (X Y Z : ZornVectorMatrix R) :
    zornSpinConnectionPart
      (zornSpacetimeFramePart (zornSpacetimeFramePart X * zornSpacetimeFramePart Y) *
       zornSpacetimeFramePart Z) =
      ⟨-zornNambuDet X.w Y.w Z.w, fun _ => 0, fun _ => 0, zornNambuDet X.v Y.v Z.v⟩ := by
  ext
  · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
          zornNambuDet, InfoGeometry.Algebra.zvm_mul_def, mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · rename_i i
    fin_cases i <;>
      simp [zornSpinConnectionPart, diagonalPart]
  · rename_i i
    fin_cases i <;>
      simp [zornSpinConnectionPart, diagonalPart]
  · simp [zornSpinConnectionPart, zornSpacetimeFramePart, diagonalPart, offDiagonalPart,
          zornNambuDet, InfoGeometry.Algebra.zvm_mul_def, mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

/-!
## 8. Tomita–Takesaki Modular Conjugations & KMS Transport of Nambu 3-Bracket Volumes
-/

/-- **Zorn Chiral-Swap Automorphism (`zornModularSwap`)**:
    `σ_swap ⟨a, v, w, b⟩ = ⟨b, -w, -v, a⟩` swaps the singlet poles `a ↔ b` and maps `(v, w) ↦ (-w, -v)`. -/
def zornModularSwap (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨X.b, fun i => -X.w i, fun i => -X.v i, X.a⟩

/-- **Tomita Modular Anti-Automorphism (`zornTomitaConj`)**:
    `J_Tomita ⟨a, v, w, b⟩ = ⟨a, w, v, b⟩` fixes the diagonal singlet poles `(a, b)` and swaps
    the quark and antiquark color triplets `v ↔ w`. -/
def zornTomitaConj (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨X.a, X.w, X.v, X.b⟩

/-- **Automorphism & Anti-Automorphism Laws of `zornModularSwap` and `zornTomitaConj`**:
    `zornModularSwap` is an exact multiplicative automorphism flipping `zornGamma`, while
    `zornTomitaConj` is an exact multiplicative anti-automorphism fixing `zornGamma`! -/
theorem zornModularSwap_and_tomitaConj_laws (X Y : ZornVectorMatrix R) :
    zornModularSwap (zornModularSwap X) = X ∧
    zornModularSwap (X * Y) = zornModularSwap X * zornModularSwap Y ∧
    zornModularSwap (zornGamma : ZornVectorMatrix R) = -zornGamma ∧
    zornTomitaConj (zornTomitaConj X) = X ∧
    zornTomitaConj (X * Y) = zornTomitaConj Y * zornTomitaConj X ∧
    zornTomitaConj (zornGamma : ZornVectorMatrix R) = zornGamma := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext
    · simp [zornModularSwap, zornTomitaConj, zornGamma,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_neg_def,
            mul, neg, ZornVec3.dot, Fin.sum_univ_three]
      try ring
    · rename_i i
      fin_cases i <;>
        (simp [zornModularSwap, zornTomitaConj, zornGamma,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_neg_def,
               mul, neg, ZornVec3.cross]; try ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornModularSwap, zornTomitaConj, zornGamma,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_neg_def,
               mul, neg, ZornVec3.cross]; try ring)
    · simp [zornModularSwap, zornTomitaConj, zornGamma,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_neg_def,
            mul, neg, ZornVec3.dot, Fin.sum_univ_three]
      try ring

/-- **KMS Modular Scaling of Nambu 3-Bracket Volumes & Baryon–Antibaryon Invariance (`u : Rˣ`)**:
    Under the antisymmetric KMS modular flow `Δ_u = zornTwoSidedHyperbolicLaplace u u⁻¹ u⁻¹ u`:
    - The quark Nambu 3-volume `zornNambuDet X'.v Y'.v Z'.v` scales by `u ^ 6`.
    - The antiquark Nambu 3-volume `zornNambuDet X'.w Y'.w Z'.w` scales by `(↑u⁻¹) ^ 6`.
    - The Baryon–Antibaryon Nambu Casimir product `zornNambuDet v * zornNambuDet w` is
      **strictly KMS-invariant**! -/
theorem zornNambuDet_kms_modular_transport
    (u : Rˣ) (X Y Z : ZornVectorMatrix R) :
    let X' := zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) X
    let Y' := zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) Y
    let Z' := zornTwoSidedHyperbolicLaplace (u : R) (↑u⁻¹ : R) (↑u⁻¹ : R) (u : R) Z
    zornNambuDet X'.v Y'.v Z'.v = ((u : R) ^ 6) * zornNambuDet X.v Y.v Z.v ∧
    zornNambuDet X'.w Y'.w Z'.w = ((↑u⁻¹ : R) ^ 6) * zornNambuDet X.w Y.w Z.w ∧
    zornNambuDet X'.v Y'.v Z'.v * zornNambuDet X'.w Y'.w Z'.w =
      zornNambuDet X.v Y.v Z.v * zornNambuDet X.w Y.w Z.w := by
  intro X' Y' Z'
  have hv : zornNambuDet X'.v Y'.v Z'.v = ((u : R) ^ 6) * zornNambuDet X.v Y.v Z.v := by
    simp [X', Y', Z', zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
          zornNambuDet, InfoGeometry.Algebra.zvm_mul_def, mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  have hw : zornNambuDet X'.w Y'.w Z'.w = ((↑u⁻¹ : R) ^ 6) * zornNambuDet X.w Y.w Z.w := by
    simp [X', Y', Z', zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
          zornNambuDet, InfoGeometry.Algebra.zvm_mul_def, mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  have h_inv : zornNambuDet X'.v Y'.v Z'.v * zornNambuDet X'.w Y'.w Z'.w =
      zornNambuDet X.v Y.v Z.v * zornNambuDet X.w Y.w Z.w := by
    rw [hv, hw]
    calc ((u : R) ^ 6 * zornNambuDet X.v Y.v Z.v) *
         ((↑u⁻¹ : R) ^ 6 * zornNambuDet X.w Y.w Z.w)
      _ = ((u : R) * (↑u⁻¹ : R)) ^ 6 *
          (zornNambuDet X.v Y.v Z.v * zornNambuDet X.w Y.w Z.w) := by ring
      _ = zornNambuDet X.v Y.v Z.v * zornNambuDet X.w Y.w Z.w := by
          simp
  exact ⟨hv, hw, h_inv⟩

/-- **Symmetric Modular Sandwich Preserves the 6D Frame & Nambu Volumes Without Decay (`u : Rˣ`)**. -/
theorem symmetric_modular_sandwich_preserves_frame_and_nambu
    (u : Rˣ) (X Y Z : ZornVectorMatrix R) :
    let K := zornHyperbolicKernel (u : R) (↑u⁻¹ : R)
    zornSpacetimeFramePart (twoSidedSandwich K X) = zornSpacetimeFramePart X ∧
    zornNambuDet (twoSidedSandwich K X).v (twoSidedSandwich K Y).v (twoSidedSandwich K Z).v =
      zornNambuDet X.v Y.v Z.v := by
  intro K
  have h_frame (W : ZornVectorMatrix R) :
      zornSpacetimeFramePart (twoSidedSandwich K W) = zornSpacetimeFramePart W := by
    ext
    · rfl
    · rename_i i
      fin_cases i <;>
        simp [K, twoSidedSandwich, zornHyperbolicKernel, zornSpacetimeFramePart,
              offDiagonalPart, mul, ZornVec3.cross]
    · rename_i i
      fin_cases i <;>
        simp [K, twoSidedSandwich, zornHyperbolicKernel, zornSpacetimeFramePart,
              offDiagonalPart, mul, ZornVec3.cross]
    · rfl
  have h_v (W : ZornVectorMatrix R) : (twoSidedSandwich K W).v = W.v := by
    simpa [zornSpacetimeFramePart, offDiagonalPart] using congrArg ZornVectorMatrix.v (h_frame W)
  rw [h_v X, h_v Y, h_v Z]
  exact ⟨h_frame X, rfl⟩

/-- **Tomita Conjugation Is a `+1` Ternary Homomorphism of the Associator & Jacobiator**:
    Even though `zornTomitaConj` reverses binary products (`J(X * Y) = J(Y) * J(X)`),
    double-sign cancellation under `S₃` makes `zornTomitaConj` an exact `+1` homomorphism
    of both `zornAssociator` and `zornJacobiator`! -/
theorem zornTomitaConj_associator_and_jacobiator_hom
    (X Y Z : ZornVectorMatrix R) :
    zornTomitaConj (zornAssociator X Y Z) =
      zornAssociator (zornTomitaConj X) (zornTomitaConj Y) (zornTomitaConj Z) ∧
    zornTomitaConj (zornJacobiator X Y Z) =
      zornJacobiator (zornTomitaConj X) (zornTomitaConj Y) (zornTomitaConj Z) := by
  have h_sub (A B : ZornVectorMatrix R) :
      zornTomitaConj (A - B) = zornTomitaConj A - zornTomitaConj B := by
    simp only [_root_.sub_eq_add_neg]; rfl
  have h_mul (A B : ZornVectorMatrix R) :
      zornTomitaConj (A * B) = zornTomitaConj B * zornTomitaConj A :=
    (zornModularSwap_and_tomitaConj_laws A B).2.2.2.2.1
  have h_smul (c : R) (A : ZornVectorMatrix R) :
      zornTomitaConj (c • A) = c • zornTomitaConj A := rfl
  have h_assoc :
      zornTomitaConj (zornAssociator X Y Z) =
        zornAssociator (zornTomitaConj X) (zornTomitaConj Y) (zornTomitaConj Z) := by
    let X' := zornTomitaConj X
    let Y' := zornTomitaConj Y
    let Z' := zornTomitaConj Z
    have h1 : zornTomitaConj (zornAssociator X Y Z) = -bundledAssociator Z' Y' X' := by
      unfold zornAssociator
      rw [h_sub, h_mul, h_mul, h_mul, h_mul]
      simp only [X', Y', Z', bundledAssociator, _root_.associator_apply]
      abel
    have h2 : bundledAssociator Z' Y' X' = -bundledAssociator X' Y' Z' := by
      have h_yxz : bundledAssociator Y' X' Z' = -bundledAssociator X' Y' Z' := by
        rw [bundledAssociator_swap12 X' Y' Z', neg_neg]
      exact (bundledAssociator_cycle Z' Y' X').symm.trans h_yxz
    rw [h1, h2, neg_neg]
    rfl
  refine ⟨h_assoc, ?_⟩
  rw [zornJacobiator_eq_neg_six_smul_zornAssociator X Y Z,
      zornJacobiator_eq_neg_six_smul_zornAssociator
        (zornTomitaConj X) (zornTomitaConj Y) (zornTomitaConj Z),
      h_smul, h_assoc]

/-- **Tomita Self-Duality of the Nambu–Bianchi Frame Curvature Anomaly**:
    Replacing `(X, Y, Z)` by their Tomita conjugates `(J X, J Y, J Z)` leaves the singlet
    spin-connection projection of the frame associator strictly invariant! -/
theorem zornSpacetimeFrame_nambu_anomaly_tomita_invariant
    (X Y Z : ZornVectorMatrix R) :
    zornSpinConnectionPart
      (zornAssociator (zornSpacetimeFramePart (zornTomitaConj X))
                      (zornSpacetimeFramePart (zornTomitaConj Y))
                      (zornSpacetimeFramePart (zornTomitaConj Z))) =
    zornSpinConnectionPart
      (zornAssociator (zornSpacetimeFramePart X)
                      (zornSpacetimeFramePart Y)
                      (zornSpacetimeFramePart Z)) := by
  have hv (W : ZornVectorMatrix R) : (zornTomitaConj W).v = W.w := rfl
  have hw (W : ZornVectorMatrix R) : (zornTomitaConj W).w = W.v := rfl
  rw [zornSpacetimeFrame_associator_spinConnectionPart_eq_neg_nambu,
      zornSpacetimeFrame_associator_spinConnectionPart_eq_neg_nambu,
      hv, hv, hv, hw, hw, hw]
  have h_comm : zornNambuDet X.w Y.w Z.w + zornNambuDet X.v Y.v Z.v =
      zornNambuDet X.v Y.v Z.v + zornNambuDet X.w Y.w Z.w := by
    ring
  rw [h_comm]

/-!
## 9. Chiral Maxwell / Gravitoelectromagnetic `(1 ⊕ 3)` Four-Potential & Stress–Energy Algebra
-/

/-- **Zorn `(1 ⊕ 3)` Four-Potential Embedding (`zornFourPotential`)**:
    Embeds a scalar potential `φ : R` (singlet `1`) and a 3-vector potential `A : ZornVec3 R`
    (triplet `3`) into the traceless involutive subspace `{ X | tr X = 0 ∧ J_Tomita X = -σ_swap X }`:
    `zornFourPotential φ A = ⟨φ, A, -A, -φ⟩`. -/
def zornFourPotential (φ : R) (A : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨φ, A, fun i => -A i, -φ⟩

/-- **Chiral Riemann–Silberstein / GEM Field Strength (`zornFieldStrength`)**:
    Embeds a polar 3-field `E : ZornVec3 R` (electric / gravitoelectric) and an axial 3-field
    `B : ZornVec3 R` (magnetic / gravitomagnetic) into the 6D spacetime frame:
    `zornFieldStrength E B = ⟨0, E - B, E + B, 0⟩`. -/
def zornFieldStrength (E B : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨0, fun i => E i - B i, fun i => E i + B i, 0⟩

/-- **Four-Potential Product Decomposition into Minkowski Singlet + Chiral Field Strength**:
    For any two `(1 ⊕ 3)` four-potentials `D = zornFourPotential d₀ d` and
    `A = zornFourPotential φ a`:
    1. The even singlet part `ω_Zorn(D * A)` is the Minkowski / Lorenz scalar contraction
       `⟨d₀ φ - d ⋅ a, 0, 0, d₀ φ - d ⋅ a⟩`.
    2. The odd 6D frame part `e_Zorn(D * A)` is the exact chiral field strength
       `zornFieldStrength E B` with `E = d₀ a - φ d` and `B = d × a`! -/
theorem zornFourPotential_mul_decomposition
    (d₀ φ : R) (d a : ZornVec3 R) :
    let D := zornFourPotential d₀ d
    let A := zornFourPotential φ a
    let E : ZornVec3 R := fun i => d₀ * a i - φ * d i
    let B : ZornVec3 R := ZornVec3.cross d a
    zornSpinConnectionPart (D * A) =
      ⟨d₀ * φ - ZornVec3.dot d a, fun _ => 0, fun _ => 0, d₀ * φ - ZornVec3.dot d a⟩ ∧
    zornSpacetimeFramePart (D * A) = zornFieldStrength E B := by
  intro D A E B
  refine ⟨?_, ?_⟩
  · ext
    · simp [D, A, zornFourPotential, zornSpinConnectionPart, diagonalPart,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;> simp [zornSpinConnectionPart, diagonalPart]
    · rename_i i
      fin_cases i <;> simp [zornSpinConnectionPart, diagonalPart]
    · simp [D, A, zornFourPotential, zornSpinConnectionPart, diagonalPart,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  · ext
    · rfl
    · rename_i i
      fin_cases i <;>
        (simp [D, A, E, B, zornFourPotential, zornFieldStrength, zornSpacetimeFramePart,
               offDiagonalPart, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; ring)
    · rename_i i
      fin_cases i <;>
        (simp [D, A, E, B, zornFourPotential, zornFieldStrength, zornSpacetimeFramePart,
               offDiagonalPart, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; ring)
    · rfl

/-- **Tomita Magnetic Parity Reversal & Poynting Stress–Energy Product (`zornFieldStrength_tomita_stress_energy`)**:
    For any chiral field strength `F = zornFieldStrength E B`:
    1. Tomita conjugation reverses the axial magnetic / gravitomagnetic field:
       `zornTomitaConj (zornFieldStrength E B) = zornFieldStrength E (-B)`.
    2. The Zorn norm of `F` is the first Lorentz/Poincaré Lagrangian invariant
       `norm F = B ⋅ B - E ⋅ E`.
    3. The Tamm–Dancoff self-interaction `F * zornTomitaConj F` simultaneously packages:
       - the energy density `E ⋅ E + B ⋅ B` along `1`,
       - the chiral Pontryagin pseudoscalar `-2 (E ⋅ B)` along `zornGamma`, and
       - the Poynting momentum flux `2 (E × B)` in both triplet channels! -/
theorem zornFieldStrength_tomita_stress_energy
    (E B : ZornVec3 R) :
    let F := zornFieldStrength E B
    zornTomitaConj F = zornFieldStrength E (fun i => -B i) ∧
    norm F = ZornVec3.dot B B - ZornVec3.dot E E ∧
    F * zornTomitaConj F =
      ⟨ZornVec3.dot E E + ZornVec3.dot B B - (2 : R) * ZornVec3.dot E B,
       fun i => (2 : R) * ZornVec3.cross E B i,
       fun i => (2 : R) * ZornVec3.cross E B i,
       ZornVec3.dot E E + ZornVec3.dot B B + (2 : R) * ZornVec3.dot E B⟩ := by
  intro F
  refine ⟨?_, ?_, ?_⟩
  · ext
    · rfl
    · rename_i i
      fin_cases i <;> simp [F, zornTomitaConj, zornFieldStrength]
    · rename_i i
      fin_cases i <;> (simp [F, zornTomitaConj, zornFieldStrength]; ring)
    · rfl
  · simp [F, norm, zornFieldStrength, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · ext
    · simp [F, zornTomitaConj, zornFieldStrength, InfoGeometry.Algebra.zvm_mul_def,
            mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;>
        (simp [F, zornTomitaConj, zornFieldStrength, InfoGeometry.Algebra.zvm_mul_def,
               mul, ZornVec3.cross]; ring)
    · rename_i i
      fin_cases i <;>
        (simp [F, zornTomitaConj, zornFieldStrength, InfoGeometry.Algebra.zvm_mul_def,
               mul, ZornVec3.cross]; ring)
    · simp [F, zornTomitaConj, zornFieldStrength, InfoGeometry.Algebra.zvm_mul_def,
            mul, ZornVec3.dot, Fin.sum_univ_three]
      ring

/-- **Relativistic Maxwell / GEM Stress–Energy Identity (`zorn_maxwell_gem_stress_energy_identity`)**:
    In `ZornVectorMatrix R`, the squared energy density `(E ⋅ E + B ⋅ B)²` minus `4` times the
    squared Poynting flux `(E × B) ⋅ (E × B)` equals the sum of the squares of the two
    Poincaré/Lorentz Casimir invariants `(E ⋅ E - B ⋅ B)² + 4 (E ⋅ B)²`! -/
theorem zorn_maxwell_gem_stress_energy_identity
    (E B : ZornVec3 R) :
    (ZornVec3.dot E E + ZornVec3.dot B B) ^ 2 -
      (4 : R) * ZornVec3.dot (ZornVec3.cross E B) (ZornVec3.cross E B) =
    (ZornVec3.dot E E - ZornVec3.dot B B) ^ 2 +
      (4 : R) * (ZornVec3.dot E B) ^ 2 := by
  simp [ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  ring

/-- **Electric / Gravito-Electric 3-Vector Field (`zornElectricField d₀ d φ A`)**:
    `E = d₀ • A - φ • d`. -/
def zornElectricField (d₀ : R) (d : ZornVec3 R) (φ : R) (A : ZornVec3 R) : ZornVec3 R :=
  fun i => d₀ * A i - φ * d i

/-- **Magnetic / Gravito-Magnetic 3-Vector Field (`zornMagneticField d A`)**:
    `B = d × A`. -/
def zornMagneticField (d A : ZornVec3 R) : ZornVec3 R :=
  ZornVec3.cross d A

/-- **Minkowski / Lorenz Gauge Scalar (`zornLorenzScalar d₀ d φ A`)**:
    `G = d₀ * φ - d ⋅ A`. -/
def zornLorenzScalar (d₀ : R) (d : ZornVec3 R) (φ : R) (A : ZornVec3 R) : R :=
  d₀ * φ - ZornVec3.dot d A

/-- **Four-Potential Product Splits into Lorenz Gauge Singlet, Field Strength, & Pure-Gauge Vanishing**:
    Multiplying `D = zornFourPotential d₀ d` and `P = zornFourPotential φ A` yields:
    - Singlet part `ω_Zorn(D * P) = ⟨G, 0, 0, G⟩` where `G = zornLorenzScalar d₀ d φ A`,
    - Triplet part `e_Zorn(D * P) = zornFieldStrength E B`,
    - Pure gauge vanishing: `e_Zorn(D * D) = 0`! -/
theorem zornFourPotential_mul_lorenz_and_fieldStrength
    (d₀ : R) (d : ZornVec3 R) (φ : R) (A : ZornVec3 R) :
    let D := zornFourPotential d₀ d
    let P := zornFourPotential φ A
    let E := zornElectricField d₀ d φ A
    let B := zornMagneticField d A
    let G := zornLorenzScalar d₀ d φ A
    zornSpinConnectionPart (D * P) = ⟨G, fun _ => 0, fun _ => 0, G⟩ ∧
    zornSpacetimeFramePart (D * P) = zornFieldStrength E B ∧
    zornSpacetimeFramePart (D * D) = 0 := by
  intro D P E B G
  refine ⟨(zornFourPotential_mul_decomposition d₀ φ d A).1,
          (zornFourPotential_mul_decomposition d₀ φ d A).2, ?_⟩
  ext
  · rfl
  · rename_i i
    fin_cases i <;>
      (simp [D, zornFourPotential, zornSpacetimeFramePart, offDiagonalPart,
             InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
             mul, zero, ZornVec3.cross]; ring)
  · rename_i i
    fin_cases i <;>
      (simp [D, zornFourPotential, zornSpacetimeFramePart, offDiagonalPart,
             InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
             mul, zero, ZornVec3.cross]; ring)
  · rfl

/-- **Tomita Stress-Energy-Poynting Decomposition of `F * zornTomitaConj F`**:
    Separates `F * zornTomitaConj F` into its even Singlet part (Energy density `±` Pontryagin
    helicity) and its odd 6D Frame Triplet part (Poynting / GEM Frame-Dragging flux `2 (E × B)`)! -/
theorem zornFieldStrength_tomita_stress_energy_poynting (E B : ZornVec3 R) :
    let F := zornFieldStrength E B
    norm F = ZornVec3.dot B B - ZornVec3.dot E E ∧
    zornSpinConnectionPart (F * zornTomitaConj F) =
      ⟨ZornVec3.dot E E + ZornVec3.dot B B - (2 : R) * ZornVec3.dot E B,
       fun _ => 0, fun _ => 0,
       ZornVec3.dot E E + ZornVec3.dot B B + (2 : R) * ZornVec3.dot E B⟩ ∧
    zornSpacetimeFramePart (F * zornTomitaConj F) =
      ⟨0, fun i => (2 : R) * ZornVec3.cross E B i,
       fun i => (2 : R) * ZornVec3.cross E B i, 0⟩ := by
  intro F
  have h := zornFieldStrength_tomita_stress_energy E B
  refine ⟨h.2.1, ?_, ?_⟩
  · rw [h.2.2]; rfl
  · rw [h.2.2]; rfl

/-- **Universal Maxwell / GEM Stress-Energy-Poynting Identity (`zorn_maxwell_gem_stress_identity`)**:
    `(E⋅E + B⋅B)² - 4(E⋅B)² - 4(E × B)⋅(E × B) = (E⋅E - B⋅B)²`! -/
theorem zorn_maxwell_gem_stress_identity (E B : ZornVec3 R) :
    (ZornVec3.dot E E + ZornVec3.dot B B) ^ 2 -
      (4 : R) * (ZornVec3.dot E B) ^ 2 -
      (4 : R) * ZornVec3.dot (ZornVec3.cross E B) (ZornVec3.cross E B) =
    (ZornVec3.dot E E - ZornVec3.dot B B) ^ 2 := by
  simp [ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  ring

/-!
## 10. Non-Abelian Gluon Self-Interaction & Vectorlike vs. Chiral Bianchi Anomaly
-/

/-- **Chiral Color Gauge Potential (`zornChiralPotential φ A`)**:
    A purely left-handed color gauge potential `⟨φ, A, 0, -φ⟩` supported in the upper quark triplet. -/
def zornChiralPotential (φ : R) (A : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨φ, A, fun _ => 0, -φ⟩

/-- **1. Non-Abelian Gluon Self-Interaction Commutator (`[A₁, A₂]`)**:
    For any two 4-potentials `P₁ = zornFourPotential φ₁ A₁` and `P₂ = zornFourPotential φ₂ A₂`:
    - Their symmetric anticommutator `{P₁, P₂}` is the Minkowski 4-dot singlet
      `⟨2 G, 0, 0, 2 G⟩` where `G = zornLorenzScalar φ₁ A₁ φ₂ A₂`.
    - Their antisymmetric commutator `[P₁, P₂]` is `2` times the non-Abelian self-interaction
      field strength `zornFieldStrength (φ₁ • A₂ - φ₂ • A₁) (A₁ × A₂)`! -/
theorem zornFourPotential_commutator_gluon_self_interaction
    (φ₁ : R) (A₁ : ZornVec3 R) (φ₂ : R) (A₂ : ZornVec3 R) :
    let P₁ := zornFourPotential φ₁ A₁
    let P₂ := zornFourPotential φ₂ A₂
    let G := zornLorenzScalar φ₁ A₁ φ₂ A₂
    P₁ * P₂ + P₂ * P₁ = ⟨(2 : R) * G, fun _ => 0, fun _ => 0, (2 : R) * G⟩ ∧
    zornComm P₁ P₂ =
      (2 : R) • zornFieldStrength (zornElectricField φ₁ A₁ φ₂ A₂) (zornMagneticField A₁ A₂) := by
  intro P₁ P₂ G
  refine ⟨?_, ?_⟩
  · ext
    · simp [P₁, P₂, G, zornFourPotential, zornLorenzScalar,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
            add, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;>
        (simp [P₁, P₂, zornFourPotential, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_mul_def, add, mul, ZornVec3.cross]; ring)
    · rename_i i
      fin_cases i <;>
        (simp [P₁, P₂, zornFourPotential, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_mul_def, add, mul, ZornVec3.cross]; ring)
    · simp [P₁, P₂, G, zornFourPotential, zornLorenzScalar,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
            add, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  · unfold zornComm
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [P₁, P₂, zornFourPotential, zornFieldStrength,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;>
        (simp [P₁, P₂, zornFourPotential, zornFieldStrength, zornElectricField,
               zornMagneticField, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, add, neg, mul, smul, ZornVec3.cross]; ring)
    · rename_i i
      fin_cases i <;>
        (simp [P₁, P₂, zornFourPotential, zornFieldStrength, zornElectricField,
               zornMagneticField, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, add, neg, mul, smul, ZornVec3.cross]; ring)
    · simp [P₁, P₂, zornFourPotential, zornFieldStrength,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
      ring

/-- **2. Vectorlike Bianchi Identity vs. Chiral Color Nambu Anomaly**:
    1. For any three vectorlike 4-potentials `P_i = zornFourPotential φ_i A_i` (`w = -v`),
       the quark and antiquark Nambu 3-volumes cancel (`det A + det (-A) = 0`), so the
       singlet Bianchi Jacobiator and Associator anomalies vanish identically (`= 0`)!
    2. For any three chiral color potentials `C_i = zornChiralPotential φ_i A_i` (`w = 0`),
       the singlet Bianchi Jacobiator anomaly is `(6 * zornNambuDet A₁ A₂ A₃) • zornGamma`! -/
theorem zornFourPotential_vectorlike_bianchi_vs_chiral_nambu_anomaly
    (φ₁ : R) (A₁ : ZornVec3 R) (φ₂ : R) (A₂ : ZornVec3 R) (φ₃ : R) (A₃ : ZornVec3 R) :
    let P₁ := zornFourPotential φ₁ A₁
    let P₂ := zornFourPotential φ₂ A₂
    let P₃ := zornFourPotential φ₃ A₃
    let C₁ := zornChiralPotential φ₁ A₁
    let C₂ := zornChiralPotential φ₂ A₂
    let C₃ := zornChiralPotential φ₃ A₃
    zornSpinConnectionPart (zornJacobiator P₁ P₂ P₃) = 0 ∧
    zornSpinConnectionPart (zornAssociator P₁ P₂ P₃) = 0 ∧
    zornSpinConnectionPart (zornJacobiator C₁ C₂ C₃) =
      ((6 : R) * zornNambuDet A₁ A₂ A₃) • zornGamma := by
  intro P₁ P₂ P₃ C₁ C₂ C₃
  refine ⟨?_, ?_, ?_⟩
  · unfold zornJacobiator zornComm
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [P₁, P₂, P₃, zornFourPotential, zornSpinConnectionPart, diagonalPart,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;> simp [zornSpinConnectionPart, diagonalPart,
                            InfoGeometry.Algebra.zvm_zero_def, zero]
    · rename_i i
      fin_cases i <;> simp [zornSpinConnectionPart, diagonalPart,
                            InfoGeometry.Algebra.zvm_zero_def, zero]
    · simp [P₁, P₂, P₃, zornFourPotential, zornSpinConnectionPart, diagonalPart,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [P₁, P₂, P₃, zornFourPotential, zornSpinConnectionPart, diagonalPart,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;> simp [zornSpinConnectionPart, diagonalPart,
                            InfoGeometry.Algebra.zvm_zero_def, zero]
    · rename_i i
      fin_cases i <;> simp [zornSpinConnectionPart, diagonalPart,
                            InfoGeometry.Algebra.zvm_zero_def, zero]
    · simp [P₁, P₂, P₃, zornFourPotential, zornSpinConnectionPart, diagonalPart,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
  · unfold zornJacobiator zornComm
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [C₁, C₂, C₃, zornChiralPotential, zornSpinConnectionPart, diagonalPart,
            zornGamma, zornNambuDet, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, add, neg, mul, smul,
            ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;> simp [zornSpinConnectionPart, diagonalPart, zornGamma,
                            InfoGeometry.Algebra.zvm_smul_def, smul]
    · rename_i i
      fin_cases i <;> simp [zornSpinConnectionPart, diagonalPart, zornGamma,
                            InfoGeometry.Algebra.zvm_smul_def, smul]
    · simp [C₁, C₂, C₃, zornChiralPotential, zornSpinConnectionPart, diagonalPart,
            zornGamma, zornNambuDet, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, add, neg, mul, smul,
            ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring

/-!
## 11. Machian Relational Inertia, Sciama–Lense–Thirring Induction, & Collinear Volume Vanishing
-/

/-- **1. Machian Collinear Degeneracy of Lense–Thirring Curl & 3-Current Associator Volume**:
    Proves the unconditional Zorn bridge for the Machian relational volume law
    (`docs/Observational_Gauge_Theory_Synthesis.md` §VIII–IX):
    1. Collinear 3-currents `j` and `c • j` have vanishing 2-body gravitomagnetic curl (`= 0`).
    2. Collinear 3-currents `j` and `c • j` have vanishing 3-body Nambu scalar triple product
       `zornNambuDet ω j (c • j) = 0` for any collective rotation vector `ω`.
    3. For any 6D frame elements `e(Z)` and `e(X)` and collinear partner `c • e(X)`, both the
       singlet Zorn Associator volume and singlet Zorn Jacobiator volume vanish identically! -/
theorem zorn_machian_collinear_curl_and_nambu_vanishing
    (c : R) (ω j : ZornVec3 R) (Z X : ZornVectorMatrix R) :
    zornMagneticField j (fun i => c * j i) = (fun _ => 0) ∧
    zornNambuDet ω j (fun i => c * j i) = 0 ∧
    zornSpinConnectionPart
      (zornAssociator (zornSpacetimeFramePart Z)
                      (zornSpacetimeFramePart X)
                      (c • zornSpacetimeFramePart X)) = 0 ∧
    zornSpinConnectionPart
      (zornJacobiator (zornSpacetimeFramePart Z)
                      (zornSpacetimeFramePart X)
                      (c • zornSpacetimeFramePart X)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> (simp [zornMagneticField, ZornVec3.cross]; ring)
  · simp [zornNambuDet, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · have h_scale : c • zornSpacetimeFramePart X = zornSpacetimeFramePart (c • X) := by
      ext
      · simp [zornSpacetimeFramePart, offDiagonalPart, InfoGeometry.Algebra.zvm_smul_def, smul]
      · rename_i i; fin_cases i <;> rfl
      · rename_i i; fin_cases i <;> rfl
      · simp [zornSpacetimeFramePart, offDiagonalPart, InfoGeometry.Algebra.zvm_smul_def, smul]
    rw [h_scale, zornSpacetimeFrame_associator_spinConnectionPart_eq_neg_nambu]
    have h_det_zero :
        zornNambuDet Z.v X.v (c • X).v + zornNambuDet Z.w X.w (c • X).w = 0 := by
      simp [zornNambuDet, InfoGeometry.Algebra.zvm_smul_def, smul,
            ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
    rw [h_det_zero, neg_zero]
    ext <;> simp [zornGamma, InfoGeometry.Algebra.zvm_zero_def, zero]
  · have h_scale : c • zornSpacetimeFramePart X = zornSpacetimeFramePart (c • X) := by
      ext
      · simp [zornSpacetimeFramePart, offDiagonalPart, InfoGeometry.Algebra.zvm_smul_def, smul]
      · rename_i i; fin_cases i <;> rfl
      · rename_i i; fin_cases i <;> rfl
      · simp [zornSpacetimeFramePart, offDiagonalPart, InfoGeometry.Algebra.zvm_smul_def, smul]
    rw [h_scale, zornSpacetimeFrame_jacobiator_spinConnectionPart_eq_nambu]
    have h_det_zero :
        zornNambuDet Z.v X.v (c • X).v + zornNambuDet Z.w X.w (c • X).w = 0 := by
      simp [zornNambuDet, InfoGeometry.Algebra.zvm_smul_def, smul,
            ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
    rw [h_det_zero]
    ext <;> simp [zornGamma, InfoGeometry.Algebra.zvm_zero_def, zero]

/-- **2. Sciama Relational Inertial Induction Law (`zorn_machian_sciama_relative_induction_law`)**:
    1. **Co-Moving Vanishing**: Any two proportional 4-potentials `P = zornFourPotential φ v` and
       `c • P = zornFourPotential (c * φ) (c • v)` have zero relative commutator (`[P, c • P] = 0`)
       and zero relative gravitoelectric and gravitomagnetic fields.
    2. **Sciama Linear Induction**: Against a cosmic scalar background potential
       `P_bg = zornFourPotential Φ_bg 0` (`A_bg = 0`), a test 4-gradient `D = zornFourPotential d₀ a`
       experiences the exact inertial gravitoelectric field `-Φ_bg • a` with zero magnetic curl:
       `e_Zorn(D * P_bg) = zornFieldStrength (fun i => -Φ_bg * a i) 0`! -/
theorem zorn_machian_sciama_relative_induction_law
    (c d₀ φ Φ_bg : R) (v a : ZornVec3 R) :
    let P := zornFourPotential φ v
    let P_scaled := zornFourPotential (c * φ) (fun i => c * v i)
    let D := zornFourPotential d₀ a
    let P_bg := zornFourPotential Φ_bg (fun _ => 0)
    zornComm P P_scaled = 0 ∧
    zornSpacetimeFramePart (D * P_bg) =
      zornFieldStrength (fun i => -Φ_bg * a i) (fun _ => 0) := by
  intro P P_scaled D P_bg
  refine ⟨?_, ?_⟩
  · unfold zornComm
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [P, P_scaled, zornFourPotential, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero,
            ZornVec3.dot, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;>
        (simp [P, P_scaled, zornFourPotential, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero, ZornVec3.cross]; ring)
    · rename_i i
      fin_cases i <;>
        (simp [P, P_scaled, zornFourPotential, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero, ZornVec3.cross]; ring)
    · simp [P, P_scaled, zornFourPotential, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero,
            ZornVec3.dot, Fin.sum_univ_three]
      ring
  · rw [(zornFourPotential_mul_decomposition d₀ Φ_bg a (fun _ => 0)).2]
    ext
    · rfl
    · rename_i i
      fin_cases i <;> simp [zornFieldStrength, ZornVec3.cross]
    · rename_i i
      fin_cases i <;> simp [zornFieldStrength, ZornVec3.cross]
    · rfl

/-! ## 12. Nucleus-vs-Periphery Nambu Anomaly & Tomita–GEM Frame-Dragging Associator -/

/-- General diagonal singlet charge operator `H(h_+, h_-) = ⟨h_+, 0, 0, h_-⟩` in `ZornVectorMatrix R`.
    When `h_+ = h_- = h`, `H(h, h)` lies in the associative nucleus `N(O_s)` (`h • 1`).
    When `h_+ ≠ h_-`, `H(h_+, h_-)` acquires a chiral component `(h_+ - h_-) / 2 • Γ_Zorn`
    that drives the non-associative periphery torsion and Nambu 3-bracket anomaly. -/
def zornDiagonalCharge (hPlus hMinus : R) : ZornVectorMatrix R :=
  ⟨hPlus, fun _ => 0, fun _ => 0, hMinus⟩

/-- **Associative Nucleus vs. Non-Associative Periphery Dichotomy**:
    1. **Inside the Associative Nucleus (`h_+ = h_- = h`)**:
       A vectorlike scalar charge `zornDiagonalCharge h h` associates strictly with *every* pair
       of elements `X, Y ∈ ZornVectorMatrix R`:
       `[X, Y, H(h, h)] = 0`.
    2. **In the Non-Associative Periphery (`h_+ ≠ h_-`)**:
       On any pair of odd-grade spacetime frames `E₁ = zornSpacetimeFramePart X` and
       `E₂ = zornSpacetimeFramePart Y`, the ternary associator with `H(h_+, h_-)` is purely
       proportional to the chiral charge asymmetry `h_+ - h_-` times the cross-product torsion:
       `[E₁, E₂, H(h_+, h_-)] = (h_+ - h_-) • ⟨0, X.w × Y.w, X.v × Y.v, 0⟩`. -/
theorem zornAssociator_nucleus_zero_vs_periphery_torsion
    (X Y : ZornVectorMatrix R) (h hPlus hMinus : R) :
    zornAssociator X Y (zornDiagonalCharge h h) = 0 ∧
    zornAssociator (zornSpacetimeFramePart X) (zornSpacetimeFramePart Y)
      (zornDiagonalCharge hPlus hMinus) =
      (hPlus - hMinus) •
        (⟨0, ZornVec3.cross X.w Y.w, ZornVec3.cross X.v Y.v, 0⟩ : ZornVectorMatrix R) := by
  constructor
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [zornDiagonalCharge, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero,
            ZornVec3.dot, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;>
        (simp [zornDiagonalCharge, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero,
               ZornVec3.cross]; ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornDiagonalCharge, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero,
               ZornVec3.cross]; ring)
    · simp [zornDiagonalCharge, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero,
            ZornVec3.dot, Fin.sum_univ_three]
      ring
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [zornSpacetimeFramePart, offDiagonalPart, zornDiagonalCharge,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;>
        (simp [zornSpacetimeFramePart, offDiagonalPart, zornDiagonalCharge,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, neg, mul, smul, ZornVec3.cross]; ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornSpacetimeFramePart, offDiagonalPart, zornDiagonalCharge,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, neg, mul, smul, ZornVec3.cross]; ring)
    · simp [zornSpacetimeFramePart, offDiagonalPart, zornDiagonalCharge,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
      ring

/-- **Periphery Charge Associator Contracting with a Third Frame Generates the Nambu 3-Bracket**:
    Multiplying the periphery associator `[E₁, E₂, H(h_+, h_-)]` by a third spacetime frame
    `E₃ = zornSpacetimeFramePart Z` and projecting onto the diagonal spin-connection nucleus
    yields the chiral Nambu 3-bracket determinants `(h_+ - h_-) * det(w₁, w₂, w₃)` and
    `(h_+ - h_-) * det(v₁, v₂, v₃)`. -/
theorem zornAssociator_charge_mul_frame_eq_nambu
    (X Y Z : ZornVectorMatrix R) (hPlus hMinus : R) :
    zornSpinConnectionPart
      (zornAssociator (zornSpacetimeFramePart X) (zornSpacetimeFramePart Y)
        (zornDiagonalCharge hPlus hMinus) * zornSpacetimeFramePart Z) =
      (hPlus - hMinus) •
        (⟨zornNambuDet X.w Y.w Z.w, fun _ => 0, fun _ => 0,
          zornNambuDet X.v Y.v Z.v⟩ : ZornVectorMatrix R) := by
  rw [(zornAssociator_nucleus_zero_vs_periphery_torsion X Y 0 hPlus hMinus).2]
  ext
  · simp [zornSpinConnectionPart, diagonalPart, zornSpacetimeFramePart, offDiagonalPart,
          zornNambuDet, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
          mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · simp [zornSpinConnectionPart, diagonalPart, InfoGeometry.Algebra.zvm_smul_def, smul]
  · simp [zornSpinConnectionPart, diagonalPart, InfoGeometry.Algebra.zvm_smul_def, smul]
  · simp [zornSpinConnectionPart, diagonalPart, zornSpacetimeFramePart, offDiagonalPart,
          zornNambuDet, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
          mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

/-- **Unified Tomita–Maxwell–GEM Stress-Energy and Non-Associative Frame-Dragging Law**:
    For any field strength `F = zornFieldStrength E B = ⟨0, E + B, -E + B, 0⟩` and any diagonal
    charge operator `H(h_+, h_-) = zornDiagonalCharge hPlus hMinus`:
    1. **Binary Tomita Stress-Energy Product (`F * J_Tomita(F)`)**:
       Carries the symmetric energy density `E⋅E + B⋅B`, chiral Pontryagin helicity `∓ 2(E⋅B)`,
       and vectorlike Poynting / GEM momentum flux `+2(E × B)` on both off-diagonal triplets.
    2. **Ternary Non-Associative Tomita–GEM Frame-Dragging Associator (`[F, J_Tomita(F), H(h_+, h_-)]`)**:
       Vanishes identically in the associative nucleus (`h_+ = h_-`), and in the chiral periphery
       isolates the pure axial Poynting / Lense–Thirring frame-dragging cross product `E × B`
       with opposite signs on the two chiral sectors:
       `[F, J_Tomita(F), H(h_+, h_-)] = (2 * (h_+ - h_-)) • ⟨0, -(E × B), E × B, 0⟩`. -/
theorem zornFieldStrength_tomita_stress_and_frame_dragging
    (E B : ZornVec3 R) (hPlus hMinus : R) :
    let F := zornFieldStrength E B
    F * zornTomitaConj F =
      ⟨ZornVec3.dot E E + ZornVec3.dot B B - 2 * ZornVec3.dot E B,
       fun i => 2 * ZornVec3.cross E B i,
       fun i => 2 * ZornVec3.cross E B i,
       ZornVec3.dot E E + ZornVec3.dot B B + 2 * ZornVec3.dot E B⟩ ∧
    zornAssociator F (zornTomitaConj F) (zornDiagonalCharge hPlus hMinus) =
      ((2 : R) * (hPlus - hMinus)) •
        (⟨0, fun i => -ZornVec3.cross E B i, ZornVec3.cross E B, 0⟩ : ZornVectorMatrix R) := by
  refine ⟨(zornFieldStrength_tomita_stress_energy E B).2.2, ?_⟩
  unfold zornAssociator
  simp only [_root_.sub_eq_add_neg]
  ext
  · simp [zornFieldStrength, zornTomitaConj, zornDiagonalCharge,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
          add, neg, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · rename_i i
    fin_cases i <;>
      (simp [zornFieldStrength, zornTomitaConj, zornDiagonalCharge,
             InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
             add, neg, mul, smul, ZornVec3.cross]; ring)
  · rename_i i
    fin_cases i <;>
      (simp [zornFieldStrength, zornTomitaConj, zornDiagonalCharge,
             InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
             add, neg, mul, smul, ZornVec3.cross]; ring)
  · simp [zornFieldStrength, zornTomitaConj, zornDiagonalCharge,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
          add, neg, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
    ring

/-- **Nucleus vs. Periphery Charge Associator & Tomita–GEM Frame-Dragging Conversion**:
    - Inside the associative nucleus (`h_+ = h_- = h`), `[X, Y, H(h, h)] = 0` for all `X, Y`.
    - In the periphery (`h_+ ≠ h_-`), contracting `[e(X), e(Y), H(h_+, h_-)]` with `e(Z)`
      sources the Nambu 3-Bracket volume `(h_+ - h_-) • ⟨det w, 0, 0, det v⟩`.
    - On `(F, zornTomitaConj F)`, the charge associator `[F, zornTomitaConj F, H(h_+, h_-)]`
      converts the local charge splitting `h_+ - h_-` directly into the macroscopic GEM
      frame-dragging vector `(2 * (h_+ - h_-)) • ⟨0, -(E × B), E × B, 0⟩`! -/
theorem zornAssociator_nucleus_vs_periphery_nambu_and_frame_dragging
    (h hPlus hMinus : R) (X Y Z : ZornVectorMatrix R) (E B : ZornVec3 R) :
    let E₁ := zornSpacetimeFramePart X
    let E₂ := zornSpacetimeFramePart Y
    let E₃ := zornSpacetimeFramePart Z
    let F := zornFieldStrength E B
    zornAssociator X Y (zornDiagonalCharge h h) = 0 ∧
    zornSpinConnectionPart
      (zornAssociator E₁ E₂ (zornDiagonalCharge hPlus hMinus) * E₃) =
      (hPlus - hMinus) •
        (⟨zornNambuDet X.w Y.w Z.w, fun _ => 0, fun _ => 0,
          zornNambuDet X.v Y.v Z.v⟩ : ZornVectorMatrix R) ∧
    zornAssociator F (zornTomitaConj F) (zornDiagonalCharge hPlus hMinus) =
      ((2 : R) * (hPlus - hMinus)) •
        (⟨0, fun i => -ZornVec3.cross E B i, ZornVec3.cross E B, 0⟩ : ZornVectorMatrix R) :=
  ⟨(zornAssociator_nucleus_zero_vs_periphery_torsion X Y h hPlus hMinus).1,
   zornAssociator_charge_mul_frame_eq_nambu X Y Z hPlus hMinus,
   (zornFieldStrength_tomita_stress_and_frame_dragging E B hPlus hMinus).2⟩

/-- **Sciama–Lense–Thirring Orthogonality, Nucleus Stress-Energy, & Transverse Frame Dragging**:
    For a spatial gradient `D₀ = zornFourPotential 0 a` in a rotating cosmic background
    `P_{bg} = zornFourPotential Φ_{bg} J_{bg}`, let `E_g = -Φ_{bg} • a` and `B_g = a × J_{bg}`:
    - `E_g` and `B_g` are strictly orthogonal (`E_g ⋅ B_g = 0`).
    - The singlet stress-energy `ω_Zorn(F * zornTomitaConj F)` has zero chiral anomaly and
      lands purely in the scalar associative nucleus `(Φ_{bg}²(a⋅a) + |a×J_{bg}|²) • one`!
    - The frame-dragging flux `E_g × B_g` is the Helmholtz transverse projection
      `Φ_{bg} • ((a ⋅ a) • J_{bg} - (a ⋅ J_{bg}) • a)`, satisfying `a ⋅ (E_g × B_g) = 0`! -/
theorem zorn_sciama_lense_thirring_transverse_frame_dragging
    (Φ_bg : R) (a J_bg : ZornVec3 R) :
    let E_g := zornElectricField 0 a Φ_bg J_bg
    let B_g := zornMagneticField a J_bg
    let F := zornFieldStrength E_g B_g
    ZornVec3.dot E_g B_g = 0 ∧
    zornSpinConnectionPart (F * zornTomitaConj F) =
      (Φ_bg * Φ_bg * ZornVec3.dot a a + ZornVec3.dot B_g B_g) • (one : ZornVectorMatrix R) ∧
    ZornVec3.cross E_g B_g =
      (fun i => Φ_bg * (ZornVec3.dot a a * J_bg i - ZornVec3.dot a J_bg * a i)) ∧
    ZornVec3.dot a (ZornVec3.cross E_g B_g) = 0 := by
  intro E_g B_g F
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [E_g, B_g, zornElectricField, zornMagneticField, ZornVec3.dot, ZornVec3.cross,
          Fin.sum_univ_three]
    ring
  · rw [(zornFieldStrength_tomita_stress_energy_poynting E_g B_g).2.1]
    ext
    · simp [E_g, B_g, zornElectricField, zornMagneticField, one,
            InfoGeometry.Algebra.zvm_smul_def, smul, ZornVec3.dot, ZornVec3.cross,
            Fin.sum_univ_three]
      ring
    · simp [one, InfoGeometry.Algebra.zvm_smul_def, smul]
    · simp [one, InfoGeometry.Algebra.zvm_smul_def, smul]
    · simp [E_g, B_g, zornElectricField, zornMagneticField, one,
            InfoGeometry.Algebra.zvm_smul_def, smul, ZornVec3.dot, ZornVec3.cross,
            Fin.sum_univ_three]
      ring
  · funext i
    fin_cases i <;>
      (simp [E_g, B_g, zornElectricField, zornMagneticField, ZornVec3.dot, ZornVec3.cross,
             Fin.sum_univ_three]; ring)
  · simp [E_g, B_g, zornElectricField, zornMagneticField, ZornVec3.dot, ZornVec3.cross,
          Fin.sum_univ_three]
    ring

/-!
## 13. Machian Relational Inertia, Scalar Readout Bridge (§IX), & Coplanar Nambu Degeneracy
-/

/-- **Positive-Pole Scalar Readout (`zornPoleReadout X = X.a`)**:
    Explicit scalar readout map from `ZornVectorMatrix R` to `R` closing §IX of
    `docs/Observational_Gauge_Theory_Synthesis.md`. -/
def zornPoleReadout (X : ZornVectorMatrix R) : R := X.a

/-- **Krein / Chiral Supertrace Readout (`zornSupertrace X = X.a - X.b`)**:
    Matches the chiral supertrace `str(Γ X)` of `MachianPauliRealization.lean` and
    `ModularPhaseSeparation.lean`. -/
def zornSupertrace (X : ZornVectorMatrix R) : R := X.a - X.b

/-- **Pure Chiral Current Embedding (`zornChiralCurrent j = ⟨0, j, 0, 0⟩`)**. -/
def zornChiralCurrent (j : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨0, j, fun _ => 0, 0⟩

/-- **1. Explicit Zorn-to-Scalar Readout of the Associator & Supertrace–Curvature Bridge**:
    Closes the §IX formal synthesis gap with zero hypotheses:
    - `zornSupertrace (zornComm X Y) = 2 * zornEmergentCurvature X Y`,
    - `zornPoleReadout (zornAssociator (e X) (e Y) (e Z)) = -(det v + det w)`,
    - `zornSupertrace (zornAssociator (e X) (e Y) (e Z)) = -2 * (det v + det w)`,
    - `zornPoleReadout (zornAssociator ⟨0, ω, 0, 0⟩ ⟨0, j_π, 0, 0⟩ ⟨0, j_ν, 0, 0⟩) = -(ω ⋅ (j_π × j_ν))`! -/
theorem zorn_scalar_readout_associator_and_supertrace_curvature
    (X Y Z : ZornVectorMatrix R) (ω j_pi j_nu : ZornVec3 R) :
    zornSupertrace (zornComm X Y) = (2 : R) * zornEmergentCurvature X Y ∧
    zornPoleReadout
      (zornAssociator (zornSpacetimeFramePart X)
                      (zornSpacetimeFramePart Y)
                      (zornSpacetimeFramePart Z)) =
      -(zornNambuDet X.v Y.v Z.v + zornNambuDet X.w Y.w Z.w) ∧
    zornSupertrace
      (zornAssociator (zornSpacetimeFramePart X)
                      (zornSpacetimeFramePart Y)
                      (zornSpacetimeFramePart Z)) =
      (-2 : R) * (zornNambuDet X.v Y.v Z.v + zornNambuDet X.w Y.w Z.w) ∧
    zornPoleReadout
      (zornAssociator (zornChiralCurrent ω)
                      (zornChiralCurrent j_pi)
                      (zornChiralCurrent j_nu)) =
      -zornNambuDet ω j_pi j_nu := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold zornComm
    simp only [_root_.sub_eq_add_neg]
    simp [zornSupertrace, zornEmergentCurvature,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
          ZornVec3.dot, Fin.sum_univ_three]
    ring
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    simp [zornPoleReadout, zornSpacetimeFramePart, offDiagonalPart, zornNambuDet,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    simp [zornSupertrace, zornSpacetimeFramePart, offDiagonalPart, zornNambuDet,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    simp [zornPoleReadout, zornChiralCurrent, zornNambuDet,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

/-- **2. Two-Body Machian Collinear Degeneracy (Sciama & Lense–Thirring Vanishing)**:
    Proportional 4-potentials `(c * φ, c • A)` have vanishing relative gravitoelectric
    induction `E = 0`, vanishing gravitomagnetic curl `B = 0`, vanishing frame product
    `e_Zorn(P * (c • P)) = 0`, and vanishing spinning anomaly supertrace! -/
theorem zorn_machian_two_body_collinear_degeneracy
    (c φ : R) (A : ZornVec3 R) (X : ZornVectorMatrix R) :
    let P := zornFourPotential φ A
    zornElectricField φ A (c * φ) (fun i => c * A i) = (fun _ => 0) ∧
    zornMagneticField A (fun i => c * A i) = (fun _ => 0) ∧
    zornSpacetimeFramePart (P * (c • P)) = 0 ∧
    zornSupertrace (zornComm X (c • X)) = 0 := by
  intro P
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i
    simp [zornElectricField]; ring
  · funext i
    fin_cases i <;> (simp [zornMagneticField, ZornVec3.cross]; ring)
  · ext
    · rfl
    · rename_i i
      fin_cases i <;>
        (simp [P, zornFourPotential, zornSpacetimeFramePart, offDiagonalPart,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               InfoGeometry.Algebra.zvm_zero_def, mul, smul, zero, ZornVec3.cross]; ring)
    · rename_i i
      fin_cases i <;>
        (simp [P, zornFourPotential, zornSpacetimeFramePart, offDiagonalPart,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               InfoGeometry.Algebra.zvm_zero_def, mul, smul, zero, ZornVec3.cross]; ring)
    · rfl
  · rw [(zorn_scalar_readout_associator_and_supertrace_curvature X (c • X) X A A A).1]
    simp [zornEmergentCurvature, InfoGeometry.Algebra.zvm_smul_def, smul,
          ZornVec3.dot, Fin.sum_univ_three]
    ring

/-- **3. Three-Body Machian Coplanar & Collinear Nambu Degeneracy**:
    Whenever the third 6D current lies in the plane of the first two (`Z = c₁ • X + c₂ • Y`,
    including collinear currents `c₁ = 0`), the Nambu 3-volumes, the singlet frame associator,
    the singlet frame Jacobiator, and the full chiral-current associator all vanish identically! -/
theorem zorn_machian_three_body_coplanar_degeneracy
    (c₁ c₂ : R) (X Y : ZornVectorMatrix R) (ω j_pi : ZornVec3 R) :
    let E₁ := zornSpacetimeFramePart X
    let E₂ := zornSpacetimeFramePart Y
    let E₃ := zornSpacetimeFramePart (c₁ • X + c₂ • Y)
    zornNambuDet X.v Y.v (fun i => c₁ * X.v i + c₂ * Y.v i) = 0 ∧
    zornSpinConnectionPart (zornAssociator E₁ E₂ E₃) = 0 ∧
    zornSpinConnectionPart (zornJacobiator E₁ E₂ E₃) = 0 ∧
    zornAssociator (zornChiralCurrent ω)
                   (zornChiralCurrent j_pi)
                   (zornChiralCurrent (fun i => c₁ * ω i + c₂ * j_pi i)) = 0 := by
  intro E₁ E₂ E₃
  have h_det_zero :
      zornNambuDet X.v Y.v (c₁ • X + c₂ • Y).v +
      zornNambuDet X.w Y.w (c₁ • X + c₂ • Y).w = 0 := by
    simp [zornNambuDet, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_smul_def,
          add, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [zornNambuDet, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
  · rw [show E₁ = zornSpacetimeFramePart X from rfl,
        show E₂ = zornSpacetimeFramePart Y from rfl,
        show E₃ = zornSpacetimeFramePart (c₁ • X + c₂ • Y) from rfl,
        zornSpacetimeFrame_associator_spinConnectionPart_eq_neg_nambu, h_det_zero, neg_zero]
    ext <;> simp [zornGamma, InfoGeometry.Algebra.zvm_zero_def, zero]
  · rw [show E₁ = zornSpacetimeFramePart X from rfl,
        show E₂ = zornSpacetimeFramePart Y from rfl,
        show E₃ = zornSpacetimeFramePart (c₁ • X + c₂ • Y) from rfl,
        zornSpacetimeFrame_jacobiator_spinConnectionPart_eq_nambu, h_det_zero]
    ext <;> simp [zornGamma, InfoGeometry.Algebra.zvm_zero_def, zero]
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [zornChiralCurrent, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
    · rename_i i
      fin_cases i <;>
        simp [zornChiralCurrent, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
              InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
              add, neg, mul, zero, ZornVec3.cross]
    · rename_i i
      fin_cases i <;>
        simp [zornChiralCurrent, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
              InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
              add, neg, mul, zero, ZornVec3.cross]
    · simp [zornChiralCurrent, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring

/-!
## 14. Max Zorn (1930): Viereridentität, Peirce Zweierregeln/Dreierregeln, & Lagrange Identity
-/

/-- Zorn's (1,1) Peirce projection `𝔖₁₁` (`⟨X.a, 0, 0, 0⟩`, 1930 §2 Eq. 6' & §4 p. 145). -/
def zornPeirce11 (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨X.a, fun _ => 0, fun _ => 0, 0⟩

/-- Zorn's (2,2) Peirce projection `𝔖₂₂` (`⟨0, 0, 0, X.b⟩`, 1930 §2 Eq. 6' & §4 p. 145). -/
def zornPeirce22 (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨0, fun _ => 0, fun _ => 0, X.b⟩

/-- Zorn's (1,2) Peirce projection `𝔖₁₂` (`⟨0, X.v, 0, 0⟩`, 1930 §2 Eq. 6' & §4 p. 145). -/
def zornPeirce12 (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨0, X.v, fun _ => 0, 0⟩

/-- Zorn's (2,1) Peirce projection `𝔖₂₁` (`⟨0, 0, X.w, 0⟩`, 1930 §2 Eq. 6' & §4 p. 145). -/
def zornPeirce21 (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨0, fun _ => 0, X.w, 0⟩

/-- **1. Zorn's Viereridentität (1930, §1 Eq. 2, p. 125) & Associator Factorization (§4 p. 142)**:
    - `[X * Y, Z, W] - [X, Y * Z, W] + [X, Y, Z * W] = X * [Y, Z, W] + [X, Y, Z] * W`.
    - `[X, Y * X, Z] = X * [X, Y, Z]` and `[Z, X * Y, X] = [Z, Y, X] * X`! -/
theorem zorn_1930_viereridentitaet_and_associator_factorization
    (X Y Z W : ZornVectorMatrix R) :
    zornAssociator (X * Y) Z W - zornAssociator X (Y * Z) W + zornAssociator X Y (Z * W) =
      X * zornAssociator Y Z W + zornAssociator X Y Z * W ∧
    zornAssociator X (Y * X) Z = X * zornAssociator X Y Z ∧
    zornAssociator Z (X * Y) X = zornAssociator Z Y X * X := by
  have hb (A B C : ZornVectorMatrix R) : zornAssociator A B C = bundledAssociator A B C := rfl
  simp only [hb]
  refine ⟨?_, ?_, ?_⟩
  · have ht := teichmuller X Y Z W
    have hz :
        (bundledAssociator (X * Y) Z W - bundledAssociator X (Y * Z) W +
          bundledAssociator X Y (Z * W)) -
        (X * bundledAssociator Y Z W + bundledAssociator X Y Z * W) = 0 := by
      abel_nf at ht ⊢
      exact ht
    exact sub_eq_zero.mp hz
  · rw [bundledAssociator_swap23 X (Y * X) Z, bundledAssociator_right_product X Z Y,
        bundledAssociator_swap23 X Z Y]
    simp only [_root_.mul_neg, neg_neg]
  · rw [bundledAssociator_swap12 Z (X * Y) X, bundledAssociator_mul_right X Y Z,
        bundledAssociator_cycle Z X Y, bundledAssociator_swap23 Z X Y]
    simp only [_root_.neg_mul, neg_neg]

/-- **2. Zorn's Peirce Zweierregeln (§2 Eq. 15, p. 132) & Scalar Pull-Through (§2 Eq. 21, p. 135)**:
    For `X₁₂ = zornPeirce12 X`, `Y₁₂ = zornPeirce12 Y`, and `Z₂₂ = zornPeirce22 Z`:
    - **Eq. (15)**: `X₁₂ * Y₁₂` lands in the opposite corner `𝔖₂₁` (`zornPeirce21 (X₁₂ * Y₁₂) = X₁₂ * Y₁₂`),
      is skew-symmetric (`X₁₂ * Y₁₂ + Y₁₂ * X₁₂ = 0`), and is square-zero (`X₁₂ * X₁₂ = 0`).
    - **Eq. (21) („Durchziehen eines skalaren Faktors“)**:
      `X₁₂ * (Y₁₂ * Z₂₂) = (X₁₂ * Z₂₂) * Y₁₂` and `(X₁₂ * Z₂₂) * Y₁₂ = Z₂₂ * (X₁₂ * Y₁₂)`! -/
theorem zorn_1930_peirce_zweierregeln_and_scalar_pullthrough
    (X Y Z : ZornVectorMatrix R) :
    let X₁₂ := zornPeirce12 X
    let Y₁₂ := zornPeirce12 Y
    let Z₂₂ := zornPeirce22 Z
    zornPeirce21 (X₁₂ * Y₁₂) = X₁₂ * Y₁₂ ∧
    X₁₂ * Y₁₂ + Y₁₂ * X₁₂ = 0 ∧
    X₁₂ * X₁₂ = 0 ∧
    X₁₂ * (Y₁₂ * Z₂₂) = (X₁₂ * Z₂₂) * Y₁₂ ∧
    (X₁₂ * Z₂₂) * Y₁₂ = Z₂₂ * (X₁₂ * Y₁₂) := by
  intro X₁₂ Y₁₂ Z₂₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext
    · simp [X₁₂, Y₁₂, Z₂₂, zornPeirce12, zornPeirce21, zornPeirce22,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, mul, zero, ZornVec3.dot]
    · rename_i i
      fin_cases i <;>
        simp [X₁₂, Y₁₂, Z₂₂, zornPeirce12, zornPeirce21, zornPeirce22,
              InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
              InfoGeometry.Algebra.zvm_zero_def, add, mul, zero, ZornVec3.cross]
    · rename_i i
      fin_cases i <;>
        (simp [X₁₂, Y₁₂, Z₂₂, zornPeirce12, zornPeirce21, zornPeirce22,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_zero_def, add, mul, zero, ZornVec3.cross]; try ring)
    · simp [X₁₂, Y₁₂, Z₂₂, zornPeirce12, zornPeirce21, zornPeirce22,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, mul, zero, ZornVec3.dot]

/-- **3. Zorn's Peirce „Identität von Lagrange“ (§2 Eq. 22, p. 135) & Triple Pole Split (§4 Eqs. 11–12, p. 146)**:
    - **Eq. (22) („Identität von Lagrange“)**:
      For `X₁₂ ∈ 𝔖₁₂` and `Y₂₁, Z₂₁ ∈ 𝔖₂₁`,
      `X₁₂ * (Y₂₁ * Z₂₁) = Z₂₁ * (X₁₂ * Y₂₁) - (Z₂₁ * X₁₂) * Y₂₁`!
    - **Eqs. (11)–(12) & (23) (Triple-Product Pole Split)**:
      `(X₁₂ * Y₁₂) * Z₁₂ = ⟨0, 0, 0, zornNambuDet X.v Y.v Z.v⟩`,
      `X₁₂ * (Y₁₂ * Z₁₂) = ⟨zornNambuDet X.v Y.v Z.v, 0, 0, 0⟩`, and
      `[X₁₂, Y₁₂, Z₁₂] = (-zornNambuDet X.v Y.v Z.v) • zornGamma`! -/
theorem zorn_1930_peirce_lagrange_and_triple_pole_split
    (X Y Z : ZornVectorMatrix R) :
    let X₁₂ := zornPeirce12 X
    let Y₁₂ := zornPeirce12 Y
    let Z₁₂ := zornPeirce12 Z
    let Y₂₁ := zornPeirce21 Y
    let Z₂₁ := zornPeirce21 Z
    X₁₂ * (Y₂₁ * Z₂₁) = Z₂₁ * (X₁₂ * Y₂₁) - (Z₂₁ * X₁₂) * Y₂₁ ∧
    (X₁₂ * Y₁₂) * Z₁₂ = ⟨0, fun _ => 0, fun _ => 0, zornNambuDet X.v Y.v Z.v⟩ ∧
    X₁₂ * (Y₁₂ * Z₁₂) = ⟨zornNambuDet X.v Y.v Z.v, fun _ => 0, fun _ => 0, 0⟩ ∧
    zornAssociator X₁₂ Y₁₂ Z₁₂ = (-zornNambuDet X.v Y.v Z.v) • zornGamma := by
  intro X₁₂ Y₁₂ Z₁₂ Y₂₁ Z₂₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [_root_.sub_eq_add_neg]
    ext
    · simp [X₁₂, Y₂₁, Z₂₁, zornPeirce12, zornPeirce21,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, add, neg, mul, ZornVec3.dot]
    · rename_i i
      fin_cases i <;>
        simp [X₁₂, Y₂₁, Z₂₁, zornPeirce12, zornPeirce21,
              InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
              InfoGeometry.Algebra.zvm_mul_def, add, neg, mul, ZornVec3.cross]
    · rename_i i
      fin_cases i <;>
        (simp [X₁₂, Y₂₁, Z₂₁, zornPeirce12, zornPeirce21,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
               ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring)
    · simp [X₁₂, Y₂₁, Z₂₁, zornPeirce12, zornPeirce21,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, add, neg, mul, ZornVec3.dot]
  · ext
    · simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i
      fin_cases i <;>
        simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · rename_i i
      fin_cases i <;>
        simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, zornNambuDet,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
  · ext
    · simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, zornNambuDet,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i
      fin_cases i <;>
        simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · rename_i i
      fin_cases i <;>
        simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, zornGamma, zornNambuDet,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i
      fin_cases i <;>
        simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, zornGamma,
              InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
              InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
              add, neg, mul, smul, ZornVec3.cross]
    · rename_i i
      fin_cases i <;>
        simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, zornGamma,
              InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
              InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
              add, neg, mul, smul, ZornVec3.cross]
    · simp [X₁₂, Y₁₂, Z₁₂, zornPeirce12, zornGamma, zornNambuDet,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring

/-!
## 15. Two-Sided Hyperbolic Laplace Spectral Semigroup, Walsh–Hadamard Grading Transform, & Octonionic Gauss–Bruhat Trifactorization
-/

/-- **Octonionic Upper Nilpotent Exponential Shear (`zornExpUpperNil v = ⟨1, v, 0, 1⟩ = exp(e₁₂(v))`)**. -/
def zornExpUpperNil (v : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨1, v, fun _ => 0, 1⟩

/-- **Octonionic Lower Nilpotent Exponential Shear (`zornExpLowerNil w = ⟨1, 0, w, 1⟩ = exp(e₂₁(w))`)**. -/
def zornExpLowerNil (w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨1, fun _ => 0, w, 1⟩

/-- **1. Two-Sided Hyperbolic Laplace 4-Sector Spectral Multiplier & Semigroup Composition Law**:
    With zero hypotheses on non-associative `ZornVectorMatrix R`:
    - 4-sector Peirce completeness: `zornPeirce11 X + zornPeirce22 X + zornPeirce12 X + zornPeirce21 X = X`.
    - **4-Sector Twin-Wave Spectral Decomposition**:
      `zornTwoSidedHyperbolicLaplace lamL muL lamR muR X = (lamL * lamR) • zornPeirce11 X + (muL * muR) • zornPeirce22 X + (lamL * muR) • zornPeirce12 X + (muL * lamR) • zornPeirce21 X`.
    - **Exact Two-Sided Laplace Semigroup Law**:
      `zornTwoSidedHyperbolicLaplace lamL₁ muL₁ lamR₁ muR₁ (zornTwoSidedHyperbolicLaplace lamL₂ muL₂ lamR₂ muR₂ X) = zornTwoSidedHyperbolicLaplace (lamL₁ * lamL₂) (muL₁ * muL₂) (lamR₂ * lamR₁) (muR₂ * muR₁) X`! -/
theorem zornTwoSidedHyperbolicLaplace_spectral_and_semigroup_laws
    (lamL muL lamR muR lamL₁ muL₁ lamR₁ muR₁ lamL₂ muL₂ lamR₂ muR₂ : R)
    (X : ZornVectorMatrix R) :
    zornPeirce11 X + zornPeirce22 X + zornPeirce12 X + zornPeirce21 X = X ∧
    zornTwoSidedHyperbolicLaplace lamL muL lamR muR X =
      (lamL * lamR) • zornPeirce11 X + (muL * muR) • zornPeirce22 X +
      (lamL * muR) • zornPeirce12 X + (muL * lamR) • zornPeirce21 X ∧
    zornTwoSidedHyperbolicLaplace lamL₁ muL₁ lamR₁ muR₁
      (zornTwoSidedHyperbolicLaplace lamL₂ muL₂ lamR₂ muR₂ X) =
      zornTwoSidedHyperbolicLaplace (lamL₁ * lamL₂) (muL₁ * muL₂)
        (lamR₂ * lamR₁) (muR₂ * muR₁) X := by
  refine ⟨?_, ?_, ?_⟩
  · ext
    · simp [zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
            InfoGeometry.Algebra.zvm_add_def, add]
    · rename_i i
      fin_cases i <;>
        simp [zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
              InfoGeometry.Algebra.zvm_add_def, add]
    · rename_i i
      fin_cases i <;>
        simp [zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
              InfoGeometry.Algebra.zvm_add_def, add]
    · simp [zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
            InfoGeometry.Algebra.zvm_add_def, add]
  · ext
    · simp [zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
            zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.dot]
      ring
    · rename_i i
      fin_cases i <;>
        (simp [zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
               zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.cross]; ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
               zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.cross]; ring)
    · simp [zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
            zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.dot]
      ring
  · ext
    · simp [zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
      ring
    · rename_i i
      fin_cases i <;>
        (simp [zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; ring)
    · simp [zornTwoSidedHyperbolicLaplace, zornHyperbolicKernel,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
      ring

/-- **2. Discrete `ℤ₂ × ℤ₂` Walsh–Hadamard / Fourier Grading Inversion on Split Octonions via `zornGamma`**:
    With zero hypotheses, evaluating the two-sided grading characters `((one ± zornGamma) * X) * (one ± zornGamma)`
    projects any split-octonion `X : ZornVectorMatrix R` onto its 4 Peirce grading sectors:
    - `((one + zornGamma) * X) * (one + zornGamma) = 4 • zornPeirce11 X`
    - `((one - zornGamma) * X) * (one - zornGamma) = 4 • zornPeirce22 X`
    - `((one + zornGamma) * X) * (one - zornGamma) = 4 • zornPeirce12 X`
    - `((one - zornGamma) * X) * (one + zornGamma) = 4 • zornPeirce21 X`. -/
theorem zorn_walsh_hadamard_peirce_fourier_inversion (X : ZornVectorMatrix R) :
    ((one + zornGamma) * X) * (one + zornGamma) = (4 : R) • zornPeirce11 X ∧
    ((one - zornGamma) * X) * (one - zornGamma) = (4 : R) • zornPeirce22 X ∧
    ((one + zornGamma) * X) * (one - zornGamma) = (4 : R) • zornPeirce12 X ∧
    ((one - zornGamma) * X) * (one + zornGamma) = (4 : R) • zornPeirce21 X := by
  simp only [_root_.sub_eq_add_neg]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext
    · simp [one, zornGamma, zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot]
      try ring
    · rename_i i
      fin_cases i <;>
        (simp [one, zornGamma, zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, neg, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i
      fin_cases i <;>
        (simp [one, zornGamma, zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, neg, mul, smul, ZornVec3.cross]; try ring)
    · simp [one, zornGamma, zornPeirce11, zornPeirce22, zornPeirce12, zornPeirce21,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot]
      try ring

/-- **3. Octonionic Nilpotent–Idempotent–Nilpotent Gauss–Bruhat `L D U` Trifactorization & Diquark Cross-Product Cocycle**:
    With zero hypotheses on `ZornVectorMatrix R`:
    - **Non-Associative Diquark Cross-Product Cocycles**:
      `zornExpUpperNil v₁ * zornExpUpperNil v₂ = ⟨1, v₁ + v₂, v₁ × v₂, 1⟩` and
      `zornExpLowerNil w₁ * zornExpLowerNil w₂ = ⟨1, -w₁ × w₂, w₁ + w₂, 1⟩`.
    - **Exact Octonionic Gauss–Bruhat `L D U` Trifactorization**:
      `(zornExpLowerNil w * zornHyperbolicKernel lam mu) * zornExpUpperNil v = ⟨lam, lam • v, lam • w, lam * (w ⋅ v) + mu⟩`,
      with exact multiplicative Casimir norm `norm ((zornExpLowerNil w * zornHyperbolicKernel lam mu) * zornExpUpperNil v) = lam * mu`! -/
theorem zorn_gauss_bruhat_trifactor_and_torsion_residual
    (lam mu : R) (v₁ v₂ w₁ w₂ v w : ZornVec3 R) :
    zornExpUpperNil v₁ * zornExpUpperNil v₂ =
      ⟨1, fun i => v₁ i + v₂ i, fun i => ZornVec3.cross v₁ v₂ i, 1⟩ ∧
    zornExpLowerNil w₁ * zornExpLowerNil w₂ =
      ⟨1, fun i => -ZornVec3.cross w₁ w₂ i, fun i => w₁ i + w₂ i, 1⟩ ∧
    (zornExpLowerNil w * zornHyperbolicKernel lam mu) * zornExpUpperNil v =
      ⟨lam, fun i => lam * v i, fun i => lam * w i, lam * ZornVec3.dot w v + mu⟩ ∧
    norm ((zornExpLowerNil w * zornHyperbolicKernel lam mu) * zornExpUpperNil v) =
      lam * mu := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext
    · simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i
      fin_cases i <;>
        (simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
  · ext
    · simp [zornExpLowerNil, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i
      fin_cases i <;>
        (simp [zornExpLowerNil, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornExpLowerNil, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornExpLowerNil, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
  · ext
    · simp [zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i
      fin_cases i <;>
        (simp [zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i
      fin_cases i <;>
        (simp [zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  · simp [zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel, norm,
          InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

/-- **Octonionic Hyperbolic Flow Velocity (`zornVelocityQ v w = ⟨0, v, w, 0⟩`)**. -/
def zornVelocityQ (v w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨0, v, w, 0⟩

/-- **Octonionic Symplectic Wheel (`zornWheelJ v w = ⟨0, v, -w, 0⟩`)**. -/
def zornWheelJ (v w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨0, v, fun i => -w i, 0⟩

/-- **General 8D Traceless Octonionic Flow Generator (`zornTracelessFlowGen α v w = ⟨α, v, w, -α⟩`)**. -/
def zornTracelessFlowGen (α : R) (v w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨α, v, w, -α⟩

/-- **Octonionic Affine Wavelet Generator (`zornAffineWavelet lam mu v = ⟨lam, v, 0, mu⟩`)**. -/
def zornAffineWavelet (lam mu : R) (v : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨lam, v, fun _ => 0, mu⟩

/-- **4. Octonionic Orientability–Flow–Wheel Clifford Casimir On-Shell & Affine Wavelet Semigroup**:
    With zero hypotheses on `ZornVectorMatrix R`:
    - **Chiral Orientability Factorization & Anticommutation**:
      `zornGamma * zornVelocityQ v w = zornWheelJ v w`, `zornVelocityQ v w * zornGamma = -zornWheelJ v w`,
      `zornGamma * zornWheelJ v w = zornVelocityQ v w`, and `zornWheelJ v w * zornGamma = -zornVelocityQ v w`.
    - **Universal Octonionic `(4, 4)` Casimir Mass-Shell Law**:
      `zornVelocityQ v w * zornVelocityQ v w = (v ⋅ w) • 1`,
      `zornWheelJ v w * zornWheelJ v w = -(v ⋅ w) • 1`, and
      `zornTracelessFlowGen α v w * zornTracelessFlowGen α v w = (α² + v ⋅ w) • 1`!
    - **Octonionic Affine Wavelet Semigroup with Diquark Cross-Product Cocycle**:
      `zornAffineWavelet lam₁ mu₁ v₁ * zornAffineWavelet lam₂ mu₂ v₂ = ⟨lam₁ * lam₂, lam₁ • v₂ + mu₂ • v₁, v₁ × v₂, mu₁ * mu₂⟩`! -/
theorem zorn_orientability_flow_clifford_casimir_and_affine_wavelet
    (α lam₁ mu₁ lam₂ mu₂ : R) (v w v₁ v₂ : ZornVec3 R) :
    zornGamma * zornVelocityQ v w = zornWheelJ v w ∧
    zornVelocityQ v w * zornGamma = -zornWheelJ v w ∧
    zornGamma * zornWheelJ v w = zornVelocityQ v w ∧
    zornWheelJ v w * zornGamma = -zornVelocityQ v w ∧
    zornVelocityQ v w * zornVelocityQ v w = (ZornVec3.dot v w) • (one : ZornVectorMatrix R) ∧
    zornWheelJ v w * zornWheelJ v w = (-(ZornVec3.dot v w)) • (one : ZornVectorMatrix R) ∧
    zornTracelessFlowGen α v w * zornTracelessFlowGen α v w =
      (α * α + ZornVec3.dot v w) • (one : ZornVectorMatrix R) ∧
    zornAffineWavelet lam₁ mu₁ v₁ * zornAffineWavelet lam₂ mu₂ v₂ =
      ⟨lam₁ * lam₂, fun i => lam₁ * v₂ i + v₁ i * mu₂, fun i => ZornVec3.cross v₁ v₂ i, mu₁ * mu₂⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext
    · simp [zornGamma, zornVelocityQ, zornWheelJ,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornGamma, zornVelocityQ, zornWheelJ,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornGamma, zornVelocityQ, zornWheelJ,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornGamma, zornVelocityQ, zornWheelJ,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
  · ext
    · simp [zornGamma, zornVelocityQ, zornWheelJ,
            InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, neg, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornGamma, zornVelocityQ, zornWheelJ,
               InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, neg, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornGamma, zornVelocityQ, zornWheelJ,
               InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, neg, mul, ZornVec3.cross]; try ring)
    · simp [zornGamma, zornVelocityQ, zornWheelJ,
            InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, neg, mul, ZornVec3.dot]
  · ext
    · simp [zornGamma, zornVelocityQ, zornWheelJ,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornGamma, zornVelocityQ, zornWheelJ,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornGamma, zornVelocityQ, zornWheelJ,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornGamma, zornVelocityQ, zornWheelJ,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
  · ext
    · simp [zornGamma, zornVelocityQ, zornWheelJ,
            InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, neg, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornGamma, zornVelocityQ, zornWheelJ,
               InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, neg, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornGamma, zornVelocityQ, zornWheelJ,
               InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, neg, mul, ZornVec3.cross]; try ring)
    · simp [zornGamma, zornVelocityQ, zornWheelJ,
            InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, neg, mul, ZornVec3.dot]
  · ext
    · simp [zornVelocityQ, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornVelocityQ, one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornVelocityQ, one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.cross]; try ring)
    · simp [zornVelocityQ, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  · ext
    · simp [zornWheelJ, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        (simp [zornWheelJ, one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_neg_def,
               mul, smul, neg, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornWheelJ, one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_neg_def,
               mul, smul, neg, ZornVec3.cross]; try ring)
    · simp [zornWheelJ, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  · ext
    · simp [zornTracelessFlowGen, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        (simp [zornTracelessFlowGen, one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornTracelessFlowGen, one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.cross]; try ring)
    · simp [zornTracelessFlowGen, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  · ext
    · simp [zornAffineWavelet, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornAffineWavelet, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornAffineWavelet, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornAffineWavelet, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]

/-- Lower parabolic nilpotent exponential `U_-(w) = ⟨1, 0, w, 1⟩`. -/
abbrev zornParabolicMinus (w : ZornVec3 R) : ZornVectorMatrix R := zornExpLowerNil w

/-- Upper parabolic nilpotent exponential `U_+(v) = ⟨1, v, 0, 1⟩`. -/
abbrev zornParabolicPlus (v : ZornVec3 R) : ZornVectorMatrix R := zornExpUpperNil v

/-- **8D Octonionic Nilpotent–Idempotent Trifactor Flow (`zornTrifactorFlow w λ μ v`)**:
    `(U_-(w) * D(λ, μ)) * U_+(v) = ⟨λ, λ • v, λ • w, μ + λ * (w ⋅ v)⟩`. -/
noncomputable def zornTrifactorFlow (w : ZornVec3 R) (lam mu : R) (v : ZornVec3 R) : ZornVectorMatrix R :=
  (zornParabolicMinus w * zornHyperbolicKernel lam mu) * zornParabolicPlus v

/-- **5. Octonionic Trifactor Associativity (`[U_-(w), D(λ, μ), U_+(v)] = 0`), Casimir On-Shell Norm, & Universal Schur Reconstruction**:
    Even though `ZornVectorMatrix R` is non-associative, for ALL `w, v : ZornVec3 R` and `λ, μ : R`:
    1. **Zero Trifactor Associator**: `zornAssociator (zornParabolicMinus w) (zornHyperbolicKernel lam mu) (zornParabolicPlus v) = 0`!
    2. **Explicit Coordinate Form**: `zornTrifactorFlow w lam mu v = ⟨lam, λ • v, λ • w, mu + lam * (w ⋅ v)⟩`.
    3. **Casimir On-Shell Norm Invariance**: `norm (zornTrifactorFlow w lam mu v) = lam * mu`
       (completely independent of the 6 nilpotent vector parameters `v, w`!).
    4. **Universal Schur Reconstruction (`u : Rˣ`)**:
       Every split-octonion `⟨u, v, w, b⟩` equals
       `zornTrifactorFlow (u⁻¹ • w) u (b - u⁻¹ * (w ⋅ v)) (u⁻¹ • v)`! -/
theorem zornTrifactorFlow_assoc_casimir_and_reconstruction
    (w v : ZornVec3 R) (lam mu b : R) (u : Rˣ) :
    zornAssociator (zornParabolicMinus w) (zornHyperbolicKernel lam mu) (zornParabolicPlus v) = 0 ∧
    zornTrifactorFlow w lam mu v =
      ⟨lam, fun i => lam * v i, fun i => lam * w i, mu + lam * ZornVec3.dot w v⟩ ∧
    norm (zornTrifactorFlow w lam mu v) = lam * mu ∧
    zornTrifactorFlow (fun i => (↑u⁻¹ : R) * w i) (u : R)
      (b - (↑u⁻¹ : R) * ZornVec3.dot w v) (fun i => (↑u⁻¹ : R) * v i) =
      ⟨(u : R), v, w, b⟩ := by
  have h_form (w' v' : ZornVec3 R) (lam' mu' : R) :
      zornTrifactorFlow w' lam' mu' v' =
      ⟨lam', fun i => lam' * v' i, fun i => lam' * w' i, mu' + lam' * ZornVec3.dot w' v'⟩ := by
    ext
    · simp [zornTrifactorFlow, zornParabolicMinus, zornParabolicPlus,
            zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornTrifactorFlow, zornParabolicMinus, zornParabolicPlus,
               zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornTrifactorFlow, zornParabolicMinus, zornParabolicPlus,
               zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornTrifactorFlow, zornParabolicMinus, zornParabolicPlus,
            zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  refine ⟨?_, h_form w v lam mu, ?_, ?_⟩
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [zornParabolicMinus, zornParabolicPlus, zornExpLowerNil, zornExpUpperNil,
            zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornParabolicMinus, zornParabolicPlus, zornExpLowerNil, zornExpUpperNil,
               zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornParabolicMinus, zornParabolicPlus, zornExpLowerNil, zornExpUpperNil,
               zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero, ZornVec3.cross]; try ring)
    · simp [zornParabolicMinus, zornParabolicPlus, zornExpLowerNil, zornExpUpperNil,
            zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero, ZornVec3.dot, Fin.sum_univ_three]
      ring
  · exact (zorn_gauss_bruhat_trifactor_and_torsion_residual lam mu v v w w v w).2.2.2
  · rw [h_form]
    ext
    · rfl
    · rename_i i
      dsimp
      rw [← _root_.mul_assoc, Units.mul_inv, _root_.one_mul]
    · rename_i i
      dsimp
      rw [← _root_.mul_assoc, Units.mul_inv, _root_.one_mul]
    · dsimp [ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      calc
        (b - (↑u⁻¹ : R) * (w 0 * v 0 + w 1 * v 1 + w 2 * v 2)) +
          (u : R) *
            ((↑u⁻¹ : R) * w 0 * ((↑u⁻¹ : R) * v 0) +
             (↑u⁻¹ : R) * w 1 * ((↑u⁻¹ : R) * v 1) +
             (↑u⁻¹ : R) * w 2 * ((↑u⁻¹ : R) * v 2)) =
        b + ((u : R) * (↑u⁻¹ : R) - 1) * (↑u⁻¹ : R) *
          (w 0 * v 0 + w 1 * v 1 + w 2 * v 2) := by ring
      _ = b := by simp [Units.mul_inv]

/-- **6. Universal 7D `(4, 3)` Casimir On-Shell & Exact 8D Klein–Gordon Propagation Law**:
    For ANY 7D traceless split-octonion generator `M = zornTracelessFlowGen α v w` and ANY 8D state `X`:
    1. **Casimir Mass-Shell Square**: `M * M = (α * α + v ⋅ w) • 1` (all cross-products cancel!).
    2. **Exact Left & Right 8D Klein–Gordon Propagation**:
       `M * (M * X) = (α * α + v ⋅ w) • X` and `(X * M) * M = (α * α + v ⋅ w) • X`!
    3. **4D `Pin_+` Hyperbolic Sheet (`w = v`)**: `M(α, v, v)² = (α * α + v ⋅ v) • 1`.
    4. **3D `SU(2)` Quaternion Sphere (`α = 0, w = -v`)**: `M(0, v, -v)² = -(v ⋅ v) • 1`! -/
theorem zornTracelessFlowGen_casimir_onshell_and_klein_gordon
    (α : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    zornTracelessFlowGen α v w * zornTracelessFlowGen α v w =
      (α * α + ZornVec3.dot v w) • (one : ZornVectorMatrix R) ∧
    zornTracelessFlowGen α v w * (zornTracelessFlowGen α v w * X) =
      (α * α + ZornVec3.dot v w) • X ∧
    (X * zornTracelessFlowGen α v w) * zornTracelessFlowGen α v w =
      (α * α + ZornVec3.dot v w) • X ∧
    zornTracelessFlowGen α v v * zornTracelessFlowGen α v v =
      (α * α + ZornVec3.dot v v) • (one : ZornVectorMatrix R) ∧
    zornTracelessFlowGen 0 v (-v) * zornTracelessFlowGen 0 v (-v) =
      (-ZornVec3.dot v v) • (one : ZornVectorMatrix R) := by
  have h_sq (α' : R) (v' w' : ZornVec3 R) :
      zornTracelessFlowGen α' v' w' * zornTracelessFlowGen α' v' w' =
      (α' * α' + ZornVec3.dot v' w') • (one : ZornVectorMatrix R) :=
    (zorn_orientability_flow_clifford_casimir_and_affine_wavelet α' 0 0 0 0 v' w' v' w').2.2.2.2.2.2.1
  have h_left_alt :
      zornTracelessFlowGen α v w * (zornTracelessFlowGen α v w * X) =
      (zornTracelessFlowGen α v w * zornTracelessFlowGen α v w) * X := by
    have h0 := bundledAssociator_left_alt (zornTracelessFlowGen α v w) X
    simp only [bundledAssociator, _root_.associator_apply] at h0
    exact (sub_eq_zero.mp h0).symm
  have h_right_alt :
      (X * zornTracelessFlowGen α v w) * zornTracelessFlowGen α v w =
      X * (zornTracelessFlowGen α v w * zornTracelessFlowGen α v w) := by
    have h0 := bundledAssociator_right_alt X (zornTracelessFlowGen α v w)
    simp only [bundledAssociator, _root_.associator_apply] at h0
    exact sub_eq_zero.mp h0
  refine ⟨h_sq α v w, ?_, ?_, h_sq α v v, ?_⟩
  · rw [h_left_alt, h_sq α v w]
    ext
    · simp [one, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            mul, smul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        simp [one, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
              mul, smul, ZornVec3.cross]
    · rename_i i; fin_cases i <;>
        simp [one, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
              mul, smul, ZornVec3.cross]
    · simp [one, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            mul, smul, ZornVec3.dot]
  · rw [h_right_alt, h_sq α v w]
    ext
    · simp [one, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            mul, smul, ZornVec3.dot]; ring
    · rename_i i; fin_cases i <;>
        (simp [one, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [one, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, ZornVec3.cross]; try ring)
    · simp [one, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            mul, smul, ZornVec3.dot]; ring
  · rw [h_sq 0 v (-v)]
    ext
    · simp [one, InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_neg_def,
            smul, neg, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        simp [one, InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_neg_def, smul, neg]
    · rename_i i; fin_cases i <;>
        simp [one, InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_neg_def, smul, neg]
    · simp [one, InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_neg_def,
            smul, neg, ZornVec3.dot, Fin.sum_univ_three]; try ring

/-- **7. Exponential Diquark 2-Cocycle & Jackiw–WZW Nambu 3-Cocycle**:
    For any upper nilpotent exponentials `U_i = zornExpUpperNil v_i` and lower nilpotent exponentials
    `L_i = zornExpLowerNil w_i`:
    1. **Jordan Average Recovers Abelian Addition**:
       `U₁ * U₂ + U₂ * U₁ = (2 : R) • zornExpUpperNil (v₁ + v₂)`.
    2. **Commutator Isolates the Diquark 2-Cocycle**:
       `U₁ * U₂ - U₂ * U₁ = ⟨0, 0, (2 : R) • (v₁ × v₂), 0⟩`.
    3. **Upper & Lower Group Associators Are the Jackiw–WZW Nambu 3-Cocycles**:
       `zornAssociator U₁ U₂ U₃ = (-zornNambuDet v₁ v₂ v₃) • zornGamma` and
       `zornAssociator L₁ L₂ L₃ = (-zornNambuDet w₁ w₂ w₃) • zornGamma`! -/
theorem zornExpUpperNil_diquark_two_cocycle_and_wzw_three_cocycle
    (v₁ v₂ v₃ w₁ w₂ w₃ : ZornVec3 R) :
    zornExpUpperNil v₁ * zornExpUpperNil v₂ + zornExpUpperNil v₂ * zornExpUpperNil v₁ =
      (2 : R) • zornExpUpperNil (v₁ + v₂) ∧
    zornExpUpperNil v₁ * zornExpUpperNil v₂ - zornExpUpperNil v₂ * zornExpUpperNil v₁ =
      ⟨0, 0, fun i => (2 : R) * ZornVec3.cross v₁ v₂ i, 0⟩ ∧
    zornAssociator (zornExpUpperNil v₁) (zornExpUpperNil v₂) (zornExpUpperNil v₃) =
      (-zornNambuDet v₁ v₂ v₃) • zornGamma ∧
    zornAssociator (zornExpLowerNil w₁) (zornExpLowerNil w₂) (zornExpLowerNil w₃) =
      (-zornNambuDet w₁ w₂ w₃) • zornGamma := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext
    · simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.dot]; ring
    · rename_i i; fin_cases i <;>
        (simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.cross]; try ring)
    · simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, add, mul, smul, ZornVec3.dot]; ring
  · simp only [_root_.sub_eq_add_neg]
    ext
    · simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, add, neg, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, add, neg, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, add, neg, mul, ZornVec3.cross]; try ring)
    · simp [zornExpUpperNil, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, add, neg, mul, ZornVec3.dot]
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [zornExpUpperNil, zornGamma, zornNambuDet,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornExpUpperNil, zornGamma,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, neg, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornExpUpperNil, zornGamma,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, neg, mul, smul, ZornVec3.cross]; try ring)
    · simp [zornExpUpperNil, zornGamma, zornNambuDet,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [zornExpLowerNil, zornGamma, zornNambuDet,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornExpLowerNil, zornGamma,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, neg, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornExpLowerNil, zornGamma,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, neg, mul, smul, ZornVec3.cross]; try ring)
    · simp [zornExpLowerNil, zornGamma, zornNambuDet,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, neg, mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring

end InfoGeometry.Algebra.ZornVectorMatrix
