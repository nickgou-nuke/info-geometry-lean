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
      simp only [_root_.mul_neg, neg_neg] at h2
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

end InfoGeometry.Algebra.ZornVectorMatrix
