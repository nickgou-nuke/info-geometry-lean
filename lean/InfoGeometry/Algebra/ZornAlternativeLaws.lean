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
    · simp [one, InfoGeometry.Algebra.zvm_smul_def, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        simp [one, InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_neg_def, smul, neg]
    · rename_i i; fin_cases i <;>
        simp [one, InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_neg_def, smul, neg]
    · simp [one, InfoGeometry.Algebra.zvm_smul_def, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring

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

/-- **8D Octonionic Reversed Trifactor Inverse Flow (`zornTrifactorFlowInv v invLam invMu w`)**:
    `(U_+(-v) * D(invLam, invMu)) * U_-(-w) = ⟨invLam + invMu * (v ⋅ w), -invMu • v, -invMu • w, invMu⟩`. -/
noncomputable def zornTrifactorFlowInv (v : ZornVec3 R) (invLam invMu : R) (w : ZornVec3 R) :
    ZornVectorMatrix R :=
  (zornParabolicPlus (-v) * zornHyperbolicKernel invLam invMu) * zornParabolicMinus (-w)

/-- **8D Octonionic Affine Wavelet Operator (`zornWaveletOp a v = ⟨a, v, 0, 1⟩`)**. -/
def zornWaveletOp (a : R) (v : ZornVec3 R) : ZornVectorMatrix R := ⟨a, v, 0, 1⟩

/-- **8. Forward & Reversed Trifactor Zero Associator, Explicit Coordinates, & Casimir Norm**:
    With zero hypotheses:
    1. `[U_-(w), D(λ, μ), U_+(v)] = 0` and `[U_+(-v), D(invLam, invMu), U_-(-w)] = 0`.
    2. `zornTrifactorFlow w λ μ v = ⟨λ, λ • v, λ • w, μ + λ * (w ⋅ v)⟩`.
    3. `zornTrifactorFlowInv v invLam invMu w = ⟨invLam + invMu * (v ⋅ w), -invMu • v, -invMu • w, invMu⟩`.
    4. `norm (zornTrifactorFlow w λ μ v) = λ * μ`! -/
theorem zornTrifactorFlow_assoc_coords_and_casimir
    (w v : ZornVec3 R) (lam mu invLam invMu : R) :
    zornAssociator (zornParabolicMinus w) (zornHyperbolicKernel lam mu) (zornParabolicPlus v) = 0 ∧
    zornAssociator (zornParabolicPlus (-v)) (zornHyperbolicKernel invLam invMu) (zornParabolicMinus (-w)) = 0 ∧
    zornTrifactorFlow w lam mu v =
      ⟨lam, fun i => lam * v i, fun i => lam * w i, mu + lam * ZornVec3.dot w v⟩ ∧
    zornTrifactorFlowInv v invLam invMu w =
      ⟨invLam + invMu * ZornVec3.dot v w, fun i => -(invMu * v i), fun i => -(invMu * w i), invMu⟩ ∧
    norm (zornTrifactorFlow w lam mu v) = lam * mu := by
  have h_fwd := zornTrifactorFlow_assoc_casimir_and_reconstruction w v lam mu 0 1
  refine ⟨h_fwd.1, ?_, h_fwd.2.1, ?_, h_fwd.2.2.1⟩
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [zornParabolicMinus, zornParabolicPlus, zornExpLowerNil, zornExpUpperNil,
            zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero,
            ZornVec3.dot, Fin.sum_univ_three]; try ring
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
            InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero,
            ZornVec3.dot, Fin.sum_univ_three]; try ring
  · ext
    · simp [zornTrifactorFlowInv, zornParabolicMinus, zornParabolicPlus,
            zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornTrifactorFlowInv, zornParabolicMinus, zornParabolicPlus,
               zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornTrifactorFlowInv, zornParabolicMinus, zornParabolicPlus,
               zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornTrifactorFlowInv, zornParabolicMinus, zornParabolicPlus,
            zornExpLowerNil, zornExpUpperNil, zornHyperbolicKernel,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]; try ring

/-- **9. Universal Schur Reconstruction & Exact Reversed-Trifactor Inversion (`u, m : Rˣ`)**:
    Even though `ZornVectorMatrix R` is non-associative, the reversed trifactor product
    `zornTrifactorFlowInv v u⁻¹ m⁻¹ w = (U_+(-v) * D(u⁻¹, m⁻¹)) * U_-(-w)` is the exact
    two-sided inverse of `zornTrifactorFlow w u m v = (U_-(w) * D(u, m)) * U_+(v)`! -/
theorem zornTrifactorFlow_schur_and_two_sided_inverse
    (w v : ZornVec3 R) (b : R) (u m : Rˣ) :
    zornTrifactorFlow (fun i => (↑u⁻¹ : R) * w i) (u : R)
      (b - (↑u⁻¹ : R) * ZornVec3.dot w v) (fun i => (↑u⁻¹ : R) * v i) =
      ⟨(u : R), v, w, b⟩ ∧
    zornTrifactorFlow w (u : R) (m : R) v *
      zornTrifactorFlowInv v (↑u⁻¹ : R) (↑m⁻¹ : R) w = one ∧
    zornTrifactorFlowInv v (↑u⁻¹ : R) (↑m⁻¹ : R) w *
      zornTrifactorFlow w (u : R) (m : R) v = one := by
  have hu : (u : R) * (↑u⁻¹ : R) = 1 := Units.mul_inv u
  have hm : (m : R) * (↑m⁻¹ : R) = 1 := Units.mul_inv m
  have hc := zornTrifactorFlow_assoc_coords_and_casimir w v (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R)
  refine ⟨(zornTrifactorFlow_assoc_casimir_and_reconstruction w v (u : R) (m : R) b u).2.2.2, ?_, ?_⟩
  · rw [hc.2.2.1, hc.2.2.2.1]
    ext
    · dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination hu
    · rename_i i; fin_cases i <;>
        (dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.dot, ZornVec3.cross]
        simp only [Fin.sum_univ_three]
        linear_combination (w 0) * hu - (w 0) * hm
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.dot, ZornVec3.cross]
        simp only [Fin.sum_univ_three]
        linear_combination (w 1) * hu - (w 1) * hm
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.dot, ZornVec3.cross]
        simp only [Fin.sum_univ_three]
        linear_combination (w 2) * hu - (w 2) * hm
    · dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination hm
  · rw [hc.2.2.1, hc.2.2.2.1]
    ext
    · dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination hu
    · rename_i i; fin_cases i
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.dot, ZornVec3.cross]
        simp only [Fin.sum_univ_three]
        linear_combination (v 0) * hu - (v 0) * hm
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.dot, ZornVec3.cross]
        simp only [Fin.sum_univ_three]
        linear_combination (v 1) * hu - (v 1) * hm
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.dot, ZornVec3.cross]
        simp only [Fin.sum_univ_three]
        linear_combination (v 2) * hu - (v 2) * hm
    · rename_i i; fin_cases i <;>
        (dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.cross]; ring)
    · dsimp [InfoGeometry.Algebra.zvm_mul_def, mul, one, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination hm

/-- **10. 8D Wavelet Cross-Product Vorticity Defect & Jackiw–WZW Exponential 3-Cocycle**:
    - `zornWaveletOp a₁ v₁ * zornWaveletOp a₂ v₂ = zornWaveletOp (a₁ * a₂) (v₁ + a₁ • v₂) + ⟨0, 0, v₁ × v₂, 0⟩`.
    - `zornAssociator (U_+(v₁)) (U_+(v₂)) (U_+(v₃)) = (-zornNambuDet v₁ v₂ v₃) • zornGamma`! -/
theorem zornWaveletOp_vorticity_and_wzw_three_cocycle
    (a₁ a₂ : R) (v₁ v₂ v₃ : ZornVec3 R) :
    zornWaveletOp a₁ v₁ * zornWaveletOp a₂ v₂ =
      zornWaveletOp (a₁ * a₂) (fun i => v₁ i + a₁ * v₂ i) + ⟨0, 0, ZornVec3.cross v₁ v₂, 0⟩ ∧
    zornAssociator (zornParabolicPlus v₁) (zornParabolicPlus v₂) (zornParabolicPlus v₃) =
      (-zornNambuDet v₁ v₂ v₃) • zornGamma := by
  refine ⟨?_, (zornExpUpperNil_diquark_two_cocycle_and_wzw_three_cocycle v₁ v₂ v₃ v₁ v₂ v₃).2.2.1⟩
  ext
  · simp [zornWaveletOp, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
          add, mul, ZornVec3.dot]
  · rename_i i; fin_cases i <;>
      (simp [zornWaveletOp, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
             add, mul, ZornVec3.cross]; try ring)
  · rename_i i; fin_cases i <;>
      (simp [zornWaveletOp, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
             add, mul, ZornVec3.cross]; try ring)
  · simp [zornWaveletOp, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
          add, mul, ZornVec3.dot]

/-! ### 8D Two-Sided Loxodromic Twin-Wave Kernel, Moving Projectors, & Weak-Value Syzygy -/

/-- **General 6D Off-Diagonal Wheel Generator (`zornOffDiagWheel v w = ⟨0, v, w, 0⟩`)**
    in `ZornVectorMatrix R`. -/
def zornOffDiagWheel (v w : ZornVec3 R) : ZornVectorMatrix R := ⟨0, v, w, 0⟩

/-- **8D Split-Octonion Fourier–Phase Rotor (`zornFourierRotor c s v w = c • 1 + s • J(v, w)`)**. -/
def zornFourierRotor (c s : R) (v w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨c, fun i => s * v i, fun i => s * w i, c⟩

/-- **8D Forward Loxodromic Kernel (`K_lox(λ, μ, c, s, v, w) = D(λ, μ) * R(c, s, v, w)`)**. -/
noncomputable def zornLoxodromicKernel (lam mu c s : R) (v w : ZornVec3 R) : ZornVectorMatrix R :=
  zornHyperbolicKernel lam mu * zornFourierRotor c s v w

/-- **8D Twin Loxodromic Kernel (`K_twin(c, s, invLam, invMu, v, w) = R(c, -s, v, w) * D(invLam, invMu)`)**. -/
noncomputable def zornLoxodromicTwinKernel (c s invLam invMu : R) (v w : ZornVec3 R) :
    ZornVectorMatrix R :=
  zornFourierRotor c (-s) v w * zornHyperbolicKernel invLam invMu

/-- **8D Moving Loxodromic Positive-Chiral Projector (`(K_lox * E11) * K_twin`)**. -/
noncomputable def zornMovingLoxodromicPlus (lam mu invLam invMu c s : R) (v w : ZornVec3 R) :
    ZornVectorMatrix R :=
  (zornLoxodromicKernel lam mu c s v w * E11) * zornLoxodromicTwinKernel c s invLam invMu v w

/-- **8D Moving Loxodromic Negative-Chiral Projector (`(K_lox * E22) * K_twin`)**. -/
noncomputable def zornMovingLoxodromicMinus (lam mu invLam invMu c s : R) (v w : ZornVec3 R) :
    ZornVectorMatrix R :=
  (zornLoxodromicKernel lam mu c s v w * E22) * zornLoxodromicTwinKernel c s invLam invMu v w

/-- **8D Tilted Off-Diagonal Velocity Observable (`⟨0, ratio₁ • v, -ratio₂ • w, 0⟩`)**. -/
def zornTiltedVelocity (ratio₁ ratio₂ : R) (v w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨0, fun i => ratio₁ * v i, fun i => -(ratio₂ * w i), 0⟩

/-- **11. 8D Off-Diagonal Wheel Square, Chiral Anticommutation, & Fourier Rotor Norm**:
    Because `v × v = 0` and `w × w = 0`, the off-diagonal wheel `J(v, w) = ⟨0, v, w, 0⟩`
    squares to `(v ⋅ w) • 1`, anticommutes with `Γ = ⟨1, 0, 0, -1⟩`, and the 8D Fourier rotor
    satisfies `R(c, s, v, w) * R(c, -s, v, w) = (c² - s² (v ⋅ w)) • 1`! -/
theorem zornOffDiagWheel_sq_anticomm_and_fourierRotor_inv
    (c s : R) (v w : ZornVec3 R) :
    zornOffDiagWheel v w * zornOffDiagWheel v w =
      (ZornVec3.dot v w) • (one : ZornVectorMatrix R) ∧
    zornGamma * zornOffDiagWheel v w + zornOffDiagWheel v w * zornGamma = 0 ∧
    zornFourierRotor c s v w * zornFourierRotor c (-s) v w =
      (c * c - s * s * ZornVec3.dot v w) • (one : ZornVectorMatrix R) := by
  refine ⟨?_, ?_, ?_⟩
  · ext
    · simp [zornOffDiagWheel, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        (simp [zornOffDiagWheel, one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornOffDiagWheel, one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.cross]; try ring)
    · simp [zornOffDiagWheel, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring
  · ext
    · simp [zornOffDiagWheel, zornGamma, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, mul, zero, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornOffDiagWheel, zornGamma, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, mul, zero, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornOffDiagWheel, zornGamma, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, mul, zero, ZornVec3.cross]; try ring)
    · simp [zornOffDiagWheel, zornGamma, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, mul, zero, ZornVec3.dot]
  · ext
    · simp [zornFourierRotor, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornFourierRotor, one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornFourierRotor, one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.cross]; try ring)
    · simp [zornFourierRotor, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring

/-- **12. Two-Sided Cartan Sandwich Associativity & Chiral Grading Reversal**:
    - Any two diagonal Cartan kernels `D(λ₁, μ₁)` and `D(λ₂, μ₂)` associate identically across
      any 8D split-octonion `X : ZornVectorMatrix R`: `[D(λ₁, μ₁), X, D(λ₂, μ₂)] = 0`.
    - Conjugating `K_lox(λ, μ, c, s, v, w)` by `Γ = ⟨1, 0, 0, -1⟩` reverses the Fourier phase
      `s ↦ -s` without associative defect! -/
theorem zornCartan_sandwich_assoc_and_loxodromic_grading
    (lam₁ mu₁ lam₂ mu₂ lam mu c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    zornAssociator (zornHyperbolicKernel lam₁ mu₁) X (zornHyperbolicKernel lam₂ mu₂) = 0 ∧
    (zornGamma * zornLoxodromicKernel lam mu c s v w) * zornGamma =
      zornLoxodromicKernel lam mu c (-s) v w ∧
    zornGamma * (zornLoxodromicKernel lam mu c s v w * zornGamma) =
      zornLoxodromicKernel lam mu c (-s) v w := by
  refine ⟨?_, ?_, ?_⟩
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero, ZornVec3.dot]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero, ZornVec3.cross]; try ring)
    · simp [zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_zero_def, add, neg, mul, zero, ZornVec3.dot]; try ring
  · ext
    · simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor, zornGamma,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor, zornGamma,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor, zornGamma,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor, zornGamma,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]; try ring
  · ext
    · simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor, zornGamma,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor, zornGamma,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor, zornGamma,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor, zornGamma,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]; try ring

/-- **13. 8D Loxodromic Coordinates, Factored Casimir Norm, & Twin-Kernel Synthesis**:
    - `K_lox(λ, μ, c, s, v, w) = ⟨λ c, (λ s) • v, (μ s) • w, μ c⟩`.
    - `K_twin(c, s, invLam, invMu, v, w) = ⟨c * invLam, (-invMu * s) • v, (-invLam * s) • w, c * invMu⟩`.
    - `norm (K_lox) = (λ * μ) * (c² - s² (v ⋅ w))`.
    - `K_lox * K_twin = (c² - s² (v ⋅ w)) • D(λ * invLam, μ * invMu)`! -/
theorem zornLoxodromicKernel_coords_casimir_and_twin_mul
    (lam mu invLam invMu c s : R) (v w : ZornVec3 R) :
    zornLoxodromicKernel lam mu c s v w =
      ⟨lam * c, fun i => (lam * s) * v i, fun i => (mu * s) * w i, mu * c⟩ ∧
    zornLoxodromicTwinKernel c s invLam invMu v w =
      ⟨c * invLam, fun i => -(invMu * s * v i), fun i => -(invLam * s * w i), c * invMu⟩ ∧
    norm (zornLoxodromicKernel lam mu c s v w) =
      (lam * mu) * (c * c - s * s * ZornVec3.dot v w) ∧
    zornLoxodromicKernel lam mu c s v w * zornLoxodromicTwinKernel c s invLam invMu v w =
      (c * c - s * s * ZornVec3.dot v w) •
        zornHyperbolicKernel (lam * invLam) (mu * invMu) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext
    · simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
  · ext
    · simp [zornLoxodromicTwinKernel, zornHyperbolicKernel, zornFourierRotor,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [zornLoxodromicTwinKernel, zornHyperbolicKernel, zornFourierRotor,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornLoxodromicTwinKernel, zornHyperbolicKernel, zornFourierRotor,
               InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornLoxodromicTwinKernel, zornHyperbolicKernel, zornFourierRotor,
            InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
  · simp [zornLoxodromicKernel, zornHyperbolicKernel, zornFourierRotor,
          InfoGeometry.Algebra.zvm_mul_def, mul, norm, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · ext
    · simp [zornLoxodromicKernel, zornLoxodromicTwinKernel, zornHyperbolicKernel, zornFourierRotor,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornLoxodromicKernel, zornLoxodromicTwinKernel, zornHyperbolicKernel, zornFourierRotor,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornLoxodromicKernel, zornLoxodromicTwinKernel, zornHyperbolicKernel, zornFourierRotor,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, ZornVec3.cross]; try ring)
    · simp [zornLoxodromicKernel, zornLoxodromicTwinKernel, zornHyperbolicKernel, zornFourierRotor,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring

/-- **14. Two-Sided Unit Loxodromic Inversion (`u, m : Rˣ`)**:
    When `lam = u`, `mu = m`, `invLam = u⁻¹`, `invMu = m⁻¹` for `u, m : Rˣ`, both
    `K_lox * K_twin` and `K_twin * K_lox` collapse to the pure scalar multiple
    `(c² - s² (v ⋅ w)) • 1`! -/
theorem zornLoxodromicKernel_twin_unit_inversion
    (u m : Rˣ) (c s : R) (v w : ZornVec3 R) :
    zornLoxodromicKernel (u : R) (m : R) c s v w *
      zornLoxodromicTwinKernel c s (↑u⁻¹ : R) (↑m⁻¹ : R) v w =
        (c * c - s * s * ZornVec3.dot v w) • (one : ZornVectorMatrix R) ∧
    zornLoxodromicTwinKernel c s (↑u⁻¹ : R) (↑m⁻¹ : R) v w *
      zornLoxodromicKernel (u : R) (m : R) c s v w =
        (c * c - s * s * ZornVec3.dot v w) • (one : ZornVectorMatrix R) := by
  have hu : (u : R) * (↑u⁻¹ : R) = 1 := Units.mul_inv u
  have hm : (m : R) * (↑m⁻¹ : R) = 1 := Units.mul_inv m
  have hc := zornLoxodromicKernel_coords_casimir_and_twin_mul (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w
  refine ⟨?_, ?_⟩
  · rw [hc.2.2.2, hu, hm]
    rfl
  · rw [hc.1, hc.2.1]
    ext
    · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
             mul, smul, one, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination (c * c) * hu - (s * s * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2)) * hm
    · rename_i i; fin_cases i
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, one, ZornVec3.cross]
        linear_combination (c * s * v 0) * hu - (c * s * v 0) * hm
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, one, ZornVec3.cross]
        linear_combination (c * s * v 1) * hu - (c * s * v 1) * hm
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, one, ZornVec3.cross]
        linear_combination (c * s * v 2) * hu - (c * s * v 2) * hm
    · rename_i i; fin_cases i
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, one, ZornVec3.cross]
        linear_combination (c * s * w 0) * hm - (c * s * w 0) * hu
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, one, ZornVec3.cross]
        linear_combination (c * s * w 1) * hm - (c * s * w 1) * hu
      · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, one, ZornVec3.cross]
        linear_combination (c * s * w 2) * hm - (c * s * w 2) * hu
    · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
             mul, smul, one, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination (c * c) * hm - (s * s * (w 0 * v 0 + w 1 * v 1 + w 2 * v 2)) * hu

/-- **15. 8D Moving Loxodromic Projector Associativity, Coordinates, & Partition of Unity**:
    - Both `(K_lox, E11, K_twin)` and `(K_lox, E22, K_twin)` have identically vanishing associator.
    - Explicit coordinates of `P_+^lox` and `P_-^lox`.
    - `P_+^lox + P_-^lox = (c² - s² (v ⋅ w)) • D(λ * invLam, μ * invMu)`! -/
theorem zornMovingLoxodromic_assoc_coords_and_sum
    (lam mu invLam invMu c s : R) (v w : ZornVec3 R) :
    zornAssociator (zornLoxodromicKernel lam mu c s v w) E11
      (zornLoxodromicTwinKernel c s invLam invMu v w) = 0 ∧
    zornAssociator (zornLoxodromicKernel lam mu c s v w) E22
      (zornLoxodromicTwinKernel c s invLam invMu v w) = 0 ∧
    zornMovingLoxodromicPlus lam mu invLam invMu c s v w =
      ⟨lam * invLam * (c * c),
       fun i => -(lam * invMu * c * s * v i),
       fun i => (mu * invLam * c * s) * w i,
       -(mu * invMu * (s * s) * ZornVec3.dot v w)⟩ ∧
    zornMovingLoxodromicMinus lam mu invLam invMu c s v w =
      ⟨-(lam * invLam * (s * s) * ZornVec3.dot v w),
       fun i => (lam * invMu * c * s) * v i,
       fun i => -(mu * invLam * c * s * w i),
       mu * invMu * (c * c)⟩ ∧
    zornMovingLoxodromicPlus lam mu invLam invMu c s v w +
      zornMovingLoxodromicMinus lam mu invLam invMu c s v w =
        (c * c - s * s * ZornVec3.dot v w) •
          zornHyperbolicKernel (lam * invLam) (mu * invMu) := by
  have hc := zornLoxodromicKernel_coords_casimir_and_twin_mul lam mu invLam invMu c s v w
  have hp : zornMovingLoxodromicPlus lam mu invLam invMu c s v w =
      ⟨lam * invLam * (c * c),
       fun i => -(lam * invMu * c * s * v i),
       fun i => (mu * invLam * c * s) * w i,
       -(mu * invMu * (s * s) * ZornVec3.dot v w)⟩ := by
    unfold zornMovingLoxodromicPlus
    rw [hc.1, hc.2.1]
    ext
    · simp [E11, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]; try ring
    · rename_i i; fin_cases i <;>
        (simp [E11, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [E11, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [E11, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]; try ring
  have hm_coord : zornMovingLoxodromicMinus lam mu invLam invMu c s v w =
      ⟨-(lam * invLam * (s * s) * ZornVec3.dot v w),
       fun i => (lam * invMu * c * s) * v i,
       fun i => -(mu * invLam * c * s * w i),
       mu * invMu * (c * c)⟩ := by
    unfold zornMovingLoxodromicMinus
    rw [hc.1, hc.2.1]
    ext
    · simp [E22, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [E22, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [E22, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [E22, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]; try ring
  refine ⟨?_, ?_, hp, hm_coord, ?_⟩
  · unfold zornAssociator
    rw [hc.1, hc.2.1]
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [E11, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [E11, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, neg, mul, zero, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [E11, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, neg, mul, zero, ZornVec3.cross]; try ring)
    · simp [E11, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, Fin.sum_univ_three]; try ring
  · unfold zornAssociator
    rw [hc.1, hc.2.1]
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [E22, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [E22, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, neg, mul, zero, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [E22, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, neg, mul, zero, ZornVec3.cross]; try ring)
    · simp [E22, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, Fin.sum_univ_three]; try ring
  · rw [hp, hm_coord]
    ext
    · simp [zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_smul_def, add, smul]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_smul_def, add, smul]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_smul_def, add, smul]; try ring)
    · simp [zornHyperbolicKernel, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_smul_def, add, smul]; try ring

/-- **Helper: On-Shell Moving Loxodromic Projector Coordinates (`u, m : Rˣ`)**. -/
theorem zornMovingLoxodromic_unit_coords
    (u m : Rˣ) (c s : R) (v w : ZornVec3 R) :
    zornMovingLoxodromicPlus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w =
      ⟨c * c,
       fun i => -((u : R) * (↑m⁻¹ : R) * c * s * v i),
       fun i => ((m : R) * (↑u⁻¹ : R) * c * s) * w i,
       -(s * s * ZornVec3.dot v w)⟩ ∧
    zornMovingLoxodromicMinus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w =
      ⟨-(s * s * ZornVec3.dot v w),
       fun i => ((u : R) * (↑m⁻¹ : R) * c * s) * v i,
       fun i => -((m : R) * (↑u⁻¹ : R) * c * s * w i),
       c * c⟩ := by
  have hu : (u : R) * (↑u⁻¹ : R) = 1 := Units.mul_inv u
  have hm : (m : R) * (↑m⁻¹ : R) = 1 := Units.mul_inv m
  have hc := zornMovingLoxodromic_assoc_coords_and_sum (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w
  refine ⟨?_, ?_⟩
  · rw [hc.2.2.1, hu, hm, _root_.one_mul, _root_.one_mul]
  · rw [hc.2.2.2.1, hu, hm, _root_.one_mul, _root_.one_mul]

/-- **16. Moving Loxodromic Idempotence, Orthogonality, & Boost-Invariant Chordal Metric**:
    For any `u, m : Rˣ` and `N_vw := c² - s² (v ⋅ w)`:
    1. `Π_+ + Π_- = N_vw • 1` (Complete resolution of the identity).
    2. `Π_+ * Π_- = 0` (Exact mutual orthogonality).
    3. `Π_+ * Π_+ = N_vw • Π_+` (Exact scaled idempotence).
    4. `(Π_+ - N_vw • E11)² = (-(s² (v ⋅ w)) * N_vw) • 1` (Boost-invariant Fubini–Study chordal
       distance, completely independent of the hyperbolic scales `(u, m)`)! -/
theorem zornMovingLoxodromic_idem_orth_and_chordal_metric
    (u m : Rˣ) (c s : R) (v w : ZornVec3 R) :
    zornMovingLoxodromicPlus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w +
      zornMovingLoxodromicMinus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w =
        (c * c - s * s * ZornVec3.dot v w) • (one : ZornVectorMatrix R) ∧
    zornMovingLoxodromicPlus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w *
      zornMovingLoxodromicMinus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w = 0 ∧
    zornMovingLoxodromicPlus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w *
      zornMovingLoxodromicPlus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w =
        (c * c - s * s * ZornVec3.dot v w) •
          zornMovingLoxodromicPlus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w ∧
    (zornMovingLoxodromicPlus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w -
        (c * c - s * s * ZornVec3.dot v w) • E11) *
      (zornMovingLoxodromicPlus (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w -
        (c * c - s * s * ZornVec3.dot v w) • E11) =
        (-(s * s * ZornVec3.dot v w) * (c * c - s * s * ZornVec3.dot v w)) •
          (one : ZornVectorMatrix R) := by
  have hu : (u : R) * (↑u⁻¹ : R) = 1 := Units.mul_inv u
  have hm : (m : R) * (↑m⁻¹ : R) = 1 := Units.mul_inv m
  have hum : ((u : R) * (↑m⁻¹ : R)) * ((m : R) * (↑u⁻¹ : R)) = 1 := by
    calc ((u : R) * (↑m⁻¹ : R)) * ((m : R) * (↑u⁻¹ : R))
      _ = ((u : R) * (↑u⁻¹ : R)) * ((m : R) * (↑m⁻¹ : R)) := by ring
      _ = (1 : R) * 1 := by rw [hu, hm]
      _ = 1 := _root_.mul_one (1 : R)
  have huc := zornMovingLoxodromic_unit_coords u m c s v w
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsum := (zornMovingLoxodromic_assoc_coords_and_sum (u : R) (m : R) (↑u⁻¹ : R) (↑m⁻¹ : R) c s v w).2.2.2.2
    rw [hsum, hu, hm]
    rfl
  · rw [huc.1, huc.2]
    ext
    · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
             mul, zero, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination (c * c * s * s * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2)) * hum
    · rename_i i; fin_cases i <;>
        (dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
                mul, zero, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
                mul, zero, ZornVec3.cross]; ring)
    · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
             mul, zero, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination (c * c * s * s * (w 0 * v 0 + w 1 * v 1 + w 2 * v 2)) * hum
  · rw [huc.1]
    ext
    · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
             mul, smul, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination -(c * c * s * s * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2)) * hum
    · rename_i i; fin_cases i <;>
        (dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
                mul, smul, ZornVec3.dot, ZornVec3.cross]; simp only [Fin.sum_univ_three]; ring)
    · rename_i i; fin_cases i <;>
        (dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
                mul, smul, ZornVec3.dot, ZornVec3.cross]; simp only [Fin.sum_univ_three]; ring)
    · dsimp [InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
             mul, smul, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination -(c * c * s * s * (w 0 * v 0 + w 1 * v 1 + w 2 * v 2)) * hum
  · rw [huc.1]
    simp only [_root_.sub_eq_add_neg]
    ext
    · dsimp [E11, one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
             add, neg, mul, smul, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination -(c * c * s * s * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2)) * hum
    · rename_i i; fin_cases i <;>
        (dsimp [E11, one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
                InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
                add, neg, mul, smul, ZornVec3.dot, ZornVec3.cross];
         simp only [Fin.sum_univ_three]; ring)
    · rename_i i; fin_cases i <;>
        (dsimp [E11, one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
                InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
                add, neg, mul, smul, ZornVec3.dot, ZornVec3.cross];
         simp only [Fin.sum_univ_three]; ring)
    · dsimp [E11, one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
             add, neg, mul, smul, ZornVec3.dot]
      simp only [Fin.sum_univ_three]
      linear_combination -(c * c * s * s * (w 0 * v 0 + w 1 * v 1 + w 2 * v 2)) * hum

/-- **17. 8D Two-State Aharonov Weak-Value Syzygy**:
    With zero hypotheses on `lam, mu, invLam, invMu, c, s`:
    1. `E11 * P_+^lox = ⟨λ * invLam * c², -(λ * invMu * c * s) • v, 0, 0⟩`.
    2. `(E11 * Q(r₁, r₂)) * P_+^lox = ⟨r₁ * μ * invLam * c * s * (v ⋅ w), -(r₁ * μ * invMu * s² * (v ⋅ w)) • v, 0, 0⟩`.
    3. Both the unscaled tilted velocity `Q(λ, μ)` and the Cartan-ratio tilted velocity
       `Q(λ * invMu, μ * invLam)` satisfy the division-free Two-State Aharonov Weak-Value
       operator syzygy with `E11 * P_+^lox`! -/
theorem zornMovingLoxodromic_two_state_weak_syzygy
    (lam mu invLam invMu r₁ r₂ c s : R) (v w : ZornVec3 R) :
    E11 * zornMovingLoxodromicPlus lam mu invLam invMu c s v w =
      ⟨lam * invLam * (c * c), fun i => -(lam * invMu * c * s * v i), 0, 0⟩ ∧
    (E11 * zornTiltedVelocity r₁ r₂ v w) *
      zornMovingLoxodromicPlus lam mu invLam invMu c s v w =
      ⟨r₁ * mu * invLam * c * s * ZornVec3.dot v w,
       fun i => -(r₁ * mu * invMu * (s * s) * ZornVec3.dot v w * v i), 0, 0⟩ ∧
    (mu * s * ZornVec3.dot v w) •
        (E11 * zornMovingLoxodromicPlus lam mu invLam invMu c s v w) -
      c • ((E11 * zornTiltedVelocity lam mu v w) *
        zornMovingLoxodromicPlus lam mu invLam invMu c s v w) = 0 ∧
    (mu * invMu * s * ZornVec3.dot v w) •
        (E11 * zornMovingLoxodromicPlus lam mu invLam invMu c s v w) -
      c • ((E11 * zornTiltedVelocity (lam * invMu) (mu * invLam) v w) *
        zornMovingLoxodromicPlus lam mu invLam invMu c s v w) = 0 := by
  have hp := (zornMovingLoxodromic_assoc_coords_and_sum lam mu invLam invMu c s v w).2.2.1
  have h1 : E11 * zornMovingLoxodromicPlus lam mu invLam invMu c s v w =
      ⟨lam * invLam * (c * c), fun i => -(lam * invMu * c * s * v i), 0, 0⟩ := by
    rw [hp]
    ext
    · simp [E11, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [E11, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [E11, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [E11, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot]
  have h2 : ∀ q₁ q₂ : R,
      (E11 * zornTiltedVelocity q₁ q₂ v w) *
        zornMovingLoxodromicPlus lam mu invLam invMu c s v w =
        ⟨q₁ * mu * invLam * c * s * ZornVec3.dot v w,
         fun i => -(q₁ * mu * invMu * (s * s) * ZornVec3.dot v w * v i), 0, 0⟩ := by
    intro q₁ q₂
    rw [hp]
    ext
    · simp [E11, zornTiltedVelocity, InfoGeometry.Algebra.zvm_mul_def,
            mul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [E11, zornTiltedVelocity, InfoGeometry.Algebra.zvm_mul_def,
               mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [E11, zornTiltedVelocity, InfoGeometry.Algebra.zvm_mul_def,
               mul, ZornVec3.cross]; try ring)
    · simp [E11, zornTiltedVelocity, InfoGeometry.Algebra.zvm_mul_def,
            mul, ZornVec3.dot]
  refine ⟨h1, h2 r₁ r₂, ?_, ?_⟩
  · rw [h1, h2 lam mu]
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, smul, zero]; try ring
    · rename_i i; fin_cases i <;>
        (simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, neg, smul, zero]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, neg, smul, zero]; try ring)
    · simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, smul, zero]
  · rw [h1, h2 (lam * invMu) (mu * invLam)]
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, smul, zero]; try ring
    · rename_i i; fin_cases i <;>
        (simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, neg, smul, zero]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, neg, smul, zero]; try ring)
    · simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, smul, zero]

/-!
### Two-Mode Cayley–Hamilton Exponential Flow (`zornTracelessExp`), Clifford Polarization, & Malcev Closure
-/

/-- **7D `(4, 3)` Casimir Mass-Shell Scalar (`zornTracelessCasimir α v w = α² + v ⋅ w`)**:
    Satisfies `M(α, v, w) * M(α, v, w) = zornTracelessCasimir α v w • 1`
    and `norm (M(α, v, w)) = -zornTracelessCasimir α v w`. -/
def zornTracelessCasimir (α : R) (v w : ZornVec3 R) : R :=
  α * α + ZornVec3.dot v w

/-- **7D Two-Mode Cayley–Hamilton Exponential Flow (`zornTracelessExp c s α v w`)**:
    `exp_{(c, s)}(M(α, v, w)) = c • 1 + s • zornTracelessFlowGen α v w`. -/
noncomputable def zornTracelessExp (c s α : R) (v w : ZornVec3 R) : ZornVectorMatrix R :=
  c • (one : ZornVectorMatrix R) + s • zornTracelessFlowGen α v w

private lemma bundledAssociator_smul_left (r : R) (X Y Z : ZornVectorMatrix R) :
    bundledAssociator (r • X) Y Z = r • bundledAssociator X Y Z := by
  change mul (mul (smul r X) Y) Z - mul (smul r X) (mul Y Z) =
    r • (mul (mul X Y) Z - mul X (mul Y Z))
  rw [smul_mul, smul_mul, smul_mul]
  exact (_root_.smul_sub r (mul (mul X Y) Z) (mul X (mul Y Z))).symm

private lemma bundledAssociator_smul_mid (r : R) (X Y Z : ZornVectorMatrix R) :
    bundledAssociator X (r • Y) Z = r • bundledAssociator X Y Z := by
  change mul (mul X (smul r Y)) Z - mul X (mul (smul r Y) Z) =
    r • (mul (mul X Y) Z - mul X (mul Y Z))
  rw [mul_smul, smul_mul, smul_mul, mul_smul]
  exact (_root_.smul_sub r (mul (mul X Y) Z) (mul X (mul Y Z))).symm

private lemma bundledAssociator_smul_right (r : R) (X Y Z : ZornVectorMatrix R) :
    bundledAssociator X Y (r • Z) = r • bundledAssociator X Y Z := by
  change mul (mul X Y) (smul r Z) - mul X (mul Y (smul r Z)) =
    r • (mul (mul X Y) Z - mul X (mul Y Z))
  rw [mul_smul, mul_smul, mul_smul]
  exact (_root_.smul_sub r (mul (mul X Y) Z) (mul X (mul Y Z))).symm

private lemma bundledAssociator_one_left (Y Z : ZornVectorMatrix R) :
    bundledAssociator one Y Z = 0 := by
  change mul (mul one Y) Z - mul one (mul Y Z) = 0
  rw [one_mul, one_mul, _root_.sub_self]

private lemma bundledAssociator_one_mid (X Z : ZornVectorMatrix R) :
    bundledAssociator X one Z = 0 := by
  change mul (mul X one) Z - mul X (mul one Z) = 0
  rw [mul_one, one_mul, _root_.sub_self]

private lemma bundledAssociator_one_right (X Y : ZornVectorMatrix R) :
    bundledAssociator X Y one = 0 := by
  change mul (mul X Y) one - mul X (mul Y one) = 0
  rw [mul_one, mul_one, _root_.sub_self]

/-- **18. Universal 7D `(4, 3)` Casimir On-Shell, Two-Sided Klein–Gordon, & Clifford Polarization**:
    For ANY 7D traceless flow generators `M = zornTracelessFlowGen α v w`,
    `M' = zornTracelessFlowGen α' v' w'`, and ANY 8D state `X`:
    - **On-Shell Square**: `M * M = zornTracelessCasimir α v w • 1`.
    - **Left & Right Klein–Gordon Wave Action**:
      `M * (M * X) = zornTracelessCasimir α v w • X` and `(X * M) * M = zornTracelessCasimir α v w • X`.
    - **7D Clifford Symmetric Anticommutator**:
      `M * M' + M' * M = (2 * α * α' + v ⋅ w' + v' ⋅ w) • 1`. -/
theorem zornTracelessFlowGen_casimir_klein_gordon_and_clifford
    (α α' : R) (v w v' w' : ZornVec3 R) (X : ZornVectorMatrix R) :
    let M := zornTracelessFlowGen α v w
    let M' := zornTracelessFlowGen α' v' w'
    M * M = zornTracelessCasimir α v w • (one : ZornVectorMatrix R) ∧
    M * (M * X) = zornTracelessCasimir α v w • X ∧
    (X * M) * M = zornTracelessCasimir α v w • X ∧
    M * M' + M' * M =
      (2 * α * α' + ZornVec3.dot v w' + ZornVec3.dot v' w) • (one : ZornVectorMatrix R) := by
  intro M M'
  have h12 := zornTracelessFlowGen_casimir_onshell_and_klein_gordon α v w X
  refine ⟨h12.1, h12.2.1, h12.2.2.1, ?_⟩
  · ext
    · simp [M, M', zornTracelessFlowGen, one, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [M, M', zornTracelessFlowGen, one, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [M, M', zornTracelessFlowGen, one, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               add, mul, smul, ZornVec3.cross]; try ring)
    · simp [M, M', zornTracelessFlowGen, one, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            add, mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring

/-- **19. Hyperbolic `Pin_+` (4D) vs. Elliptic `SU(2)` (3D) Specializations of `zornTracelessFlowGen`**:
    - On the 4D hyperbolic sheet (`w = v`), `M(α, v, v)² = (α² + v ⋅ v) • 1`.
    - On the 3D quaternion sphere (`α = 0, w = -v`), `M(0, v, -v)² = -(v ⋅ v) • 1`. -/
theorem zornTracelessFlowGen_hyperbolic_and_elliptic_sheets
    (α : R) (v : ZornVec3 R) :
    zornTracelessFlowGen α v v * zornTracelessFlowGen α v v =
      (α * α + ZornVec3.dot v v) • (one : ZornVectorMatrix R) ∧
    zornTracelessFlowGen 0 v (-v) * zornTracelessFlowGen 0 v (-v) =
      (-ZornVec3.dot v v) • (one : ZornVectorMatrix R) :=
  ⟨(zornTracelessFlowGen_casimir_onshell_and_klein_gordon α v v 0).2.2.2.1,
   (zornTracelessFlowGen_casimir_onshell_and_klein_gordon α v v 0).2.2.2.2⟩

/-- **20. Upper & Lower Exponential Diquark 2-Cocycles & Jackiw–WZW Nambu 3-Cocycles**:
    For any `v₁, v₂, v₃, w₁, w₂, w₃ : ZornVec3 R` with `U_i = zornExpUpperNil v_i` and `L_i = zornExpLowerNil w_i`:
    - **Jordan Additivity**: `U₁ * U₂ + U₂ * U₁ = (2 : R) • zornExpUpperNil (v₁ + v₂)`.
    - **Upper Diquark 2-Cocycle**: `U₁ * U₂ - U₂ * U₁ = ⟨0, 0, (2 : R) • (v₁ × v₂), 0⟩`.
    - **Lower Anti-Diquark 2-Cocycle**: `L₁ * L₂ - L₂ * L₁ = ⟨0, -(2 : R) • (w₁ × w₂), 0, 0⟩`.
    - **Dual Jackiw–WZW Nambu 3-Cocycles**:
      `[U₁, U₂, U₃] = (-zornNambuDet v₁ v₂ v₃) • zornGamma` and
      `[L₁, L₂, L₃] = (-zornNambuDet w₁ w₂ w₃) • zornGamma`! -/
theorem zornExpNil_diquark_two_cocycles_and_wzw_three_cocycles
    (v₁ v₂ v₃ w₁ w₂ w₃ : ZornVec3 R) :
    let U₁ := zornExpUpperNil v₁
    let U₂ := zornExpUpperNil v₂
    let U₃ := zornExpUpperNil v₃
    let L₁ := zornExpLowerNil w₁
    let L₂ := zornExpLowerNil w₂
    let L₃ := zornExpLowerNil w₃
    U₁ * U₂ + U₂ * U₁ = (2 : R) • zornExpUpperNil (v₁ + v₂) ∧
    U₁ * U₂ - U₂ * U₁ = ⟨0, 0, fun i => (2 : R) * ZornVec3.cross v₁ v₂ i, 0⟩ ∧
    L₁ * L₂ - L₂ * L₁ = ⟨0, fun i => -((2 : R) * ZornVec3.cross w₁ w₂ i), 0, 0⟩ ∧
    zornAssociator U₁ U₂ U₃ = (-zornNambuDet v₁ v₂ v₃) • zornGamma ∧
    zornAssociator L₁ L₂ L₃ = (-zornNambuDet w₁ w₂ w₃) • zornGamma := by
  intro U₁ U₂ U₃ L₁ L₂ L₃
  have h := zornExpUpperNil_diquark_two_cocycle_and_wzw_three_cocycle v₁ v₂ v₃ w₁ w₂ w₃
  refine ⟨h.1, h.2.1, ?_, h.2.2.1, h.2.2.2⟩
  simp only [_root_.sub_eq_add_neg]
  ext
  · simp [L₁, L₂, zornExpLowerNil, InfoGeometry.Algebra.zvm_add_def,
          InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
          add, neg, mul, ZornVec3.dot]
  · rename_i i; fin_cases i <;>
      (simp [L₁, L₂, zornExpLowerNil, InfoGeometry.Algebra.zvm_add_def,
             InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
             add, neg, mul, ZornVec3.cross]; try ring)
  · rename_i i; fin_cases i <;>
      (simp [L₁, L₂, zornExpLowerNil, InfoGeometry.Algebra.zvm_add_def,
             InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
             add, neg, mul, ZornVec3.cross]; try ring)
  · simp [L₁, L₂, zornExpLowerNil, InfoGeometry.Algebra.zvm_add_def,
          InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_mul_def,
          add, neg, mul, ZornVec3.dot]

/-- **21. Explicit Coordinates, Casimir Norm, 1-Parameter Group Law, & Conjugate Inversion**:
    For all mode weights `c, s, c₁, s₁, c₂, s₂, α : R` and 3-vectors `v, w : ZornVec3 R`:
    - **Explicit Coordinates**:
      `zornTracelessExp c s α v w = ⟨c + s * α, s • v, s • w, c - s * α⟩`.
    - **Casimir Norm Identity**:
      `norm (zornTracelessExp c s α v w) = c * c - s * s * zornTracelessCasimir α v w`.
    - **1-Parameter Cayley–Hamilton Group Multiplication Law**:
      `E(c₁, s₁) * E(c₂, s₂) = E(c₁ * c₂ + s₁ * s₂ * κ, c₁ * s₂ + s₁ * c₂)`.
    - **Conjugate Inversion (`s ↦ -s`)**:
      `E(c, s) * E(c, -s) = (c * c - s * s * κ) • 1`. -/
theorem zornTracelessExp_coords_casimir_norm_and_group_law
    (c s c₁ s₁ c₂ s₂ α : R) (v w : ZornVec3 R) :
    zornTracelessExp c s α v w =
      ⟨c + s * α, fun i => s * v i, fun i => s * w i, c - s * α⟩ ∧
    norm (zornTracelessExp c s α v w) =
      c * c - s * s * zornTracelessCasimir α v w ∧
    zornTracelessExp c₁ s₁ α v w * zornTracelessExp c₂ s₂ α v w =
      zornTracelessExp (c₁ * c₂ + s₁ * s₂ * zornTracelessCasimir α v w)
        (c₁ * s₂ + s₁ * c₂) α v w ∧
    zornTracelessExp c s α v w * zornTracelessExp c (-s) α v w =
      (c * c - s * s * zornTracelessCasimir α v w) • (one : ZornVectorMatrix R) := by
  have hc : ∀ p q : R,
      zornTracelessExp p q α v w =
        ⟨p + q * α, fun i => q * v i, fun i => q * w i, p - q * α⟩ := by
    intro p q
    ext
    · simp [zornTracelessExp, zornTracelessFlowGen, one,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_smul_def, add, smul]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornTracelessExp, zornTracelessFlowGen, one,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_smul_def, add, smul]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornTracelessExp, zornTracelessFlowGen, one,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_smul_def, add, smul]; try ring)
    · simp [zornTracelessExp, zornTracelessFlowGen, one,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_smul_def, add, smul]; try ring
  refine ⟨hc c s, ?_, ?_, ?_⟩
  · rw [hc c s]
    simp [zornTracelessCasimir, norm, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · rw [hc c₁ s₁, hc c₂ s₂,
        hc (c₁ * c₂ + s₁ * s₂ * zornTracelessCasimir α v w) (c₁ * s₂ + s₁ * c₂)]
    ext
    · simp [zornTracelessCasimir, InfoGeometry.Algebra.zvm_mul_def,
            mul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]; try ring)
    · simp [zornTracelessCasimir, InfoGeometry.Algebra.zvm_mul_def,
            mul, ZornVec3.dot, Fin.sum_univ_three]; try ring
  · rw [hc c s, hc c (-s)]
    ext
    · simp [zornTracelessCasimir, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [one, InfoGeometry.Algebra.zvm_mul_def,
               InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.cross]; try ring)
    · simp [zornTracelessCasimir, one, InfoGeometry.Algebra.zvm_mul_def,
            InfoGeometry.Algebra.zvm_smul_def, mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring

/-- **22. Artin–Moufang Associativity of `zornTracelessExp` on Arbitrary 8D States `X`**:
    For any two exponentials `E₁, E₂` sharing the same 7D generator `M(α, v, w)` and ANY 8D state `X`:
    - **Left Representation Associativity**: `zornAssociator E₁ E₂ X = 0`.
    - **Right Representation Associativity**: `zornAssociator X E₁ E₂ = 0`.
    - **Two-Sided Sandwich Associativity**: `zornAssociator E₁ X E₂ = 0`.
    - **Exact Left Inversion on `X`**:
      `E(c, -s) * (E(c, s) * X) = (c * c - s * s * zornTracelessCasimir α v w) • X`! -/
theorem zornTracelessExp_artin_associativity_and_state_inversion
    (c s c₁ s₁ c₂ s₂ α : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    let E₁ := zornTracelessExp c₁ s₁ α v w
    let E₂ := zornTracelessExp c₂ s₂ α v w
    let E := zornTracelessExp c s α v w
    let E_inv := zornTracelessExp c (-s) α v w
    zornAssociator E₁ E₂ X = 0 ∧
    zornAssociator X E₁ E₂ = 0 ∧
    zornAssociator E₁ X E₂ = 0 ∧
    E_inv * (E * X) = (c * c - s * s * zornTracelessCasimir α v w) • X := by
  intro E₁ E₂ E E_inv
  have h_left : ∀ p₁ q₁ p₂ q₂ : R,
      zornAssociator (zornTracelessExp p₁ q₁ α v w) (zornTracelessExp p₂ q₂ α v w) X = 0 := by
    intro p₁ q₁ p₂ q₂
    change bundledAssociator
      (p₁ • one + q₁ • zornTracelessFlowGen α v w)
      (p₂ • one + q₂ • zornTracelessFlowGen α v w) X = 0
    simp only [bundledAssociator_add_left, bundledAssociator_add_mid,
               bundledAssociator_smul_left, bundledAssociator_smul_mid,
               bundledAssociator_one_left, bundledAssociator_one_mid,
               bundledAssociator_left_alt, _root_.smul_zero, _root_.add_zero]
  have h_right :
      zornAssociator X (zornTracelessExp c₁ s₁ α v w) (zornTracelessExp c₂ s₂ α v w) = 0 := by
    change bundledAssociator X
      (c₁ • one + s₁ • zornTracelessFlowGen α v w)
      (c₂ • one + s₂ • zornTracelessFlowGen α v w) = 0
    simp only [bundledAssociator_add_mid, bundledAssociator_add_right,
               bundledAssociator_smul_mid, bundledAssociator_smul_right,
               bundledAssociator_one_mid, bundledAssociator_one_right,
               bundledAssociator_right_alt, _root_.smul_zero, _root_.add_zero]
  have h_mid :
      zornAssociator (zornTracelessExp c₁ s₁ α v w) X (zornTracelessExp c₂ s₂ α v w) = 0 := by
    change bundledAssociator
      (c₁ • one + s₁ • zornTracelessFlowGen α v w) X
      (c₂ • one + s₂ • zornTracelessFlowGen α v w) = 0
    simp only [bundledAssociator_add_left, bundledAssociator_add_right,
               bundledAssociator_smul_left, bundledAssociator_smul_right,
               bundledAssociator_one_left, bundledAssociator_one_right,
               bundledAssociator_flexible, _root_.smul_zero, _root_.add_zero]
  refine ⟨h_left c₁ s₁ c₂ s₂, h_right, h_mid, ?_⟩
  have h_assoc_inv : (E_inv * E) * X = E_inv * (E * X) :=
    sub_eq_zero.mp (h_left c (-s) c s)
  have h_inv_mul : E_inv * E =
      (c * c - s * s * zornTracelessCasimir α v w) • (one : ZornVectorMatrix R) := by
    have h0 := (zornTracelessExp_coords_casimir_norm_and_group_law c (-s) 0 0 0 0 α v w).2.2.2
    simpa [neg_neg, neg_mul, mul_neg] using h0
  rw [← h_assoc_inv, h_inv_mul]
  change mul (smul (c * c - s * s * zornTracelessCasimir α v w) one) X =
    smul (c * c - s * s * zornTracelessCasimir α v w) X
  rw [ZornVectorMatrix.smul_mul, ZornVectorMatrix.one_mul]

/-- **23. Unification of Cartan, Parabolic Nilpotent, Hyperbolic, & Elliptic Regimes**:
    `zornTracelessExp` specializes directly to all four canonical Zorn operators:
    - **Cartan Diagonal Kernel (`α = 1, v = 0, w = 0`)**:
      `zornTracelessExp c s 1 0 0 = zornHyperbolicKernel (c + s) (c - s)`.
    - **Upper Parabolic Exponential (`c = 1, α = 0, w = 0`)**:
      `zornTracelessExp 1 s 0 v 0 = zornExpUpperNil (s • v)`.
    - **Lower Parabolic Exponential (`c = 1, α = 0, v = 0`)**:
      `zornTracelessExp 1 s 0 0 w = zornExpLowerNil (s • w)`.
    - **Elliptic Fourier Rotor (`α = 0`)**:
      `zornTracelessExp c s 0 v w = zornFourierRotor c s v w`. -/
theorem zornTracelessExp_unifies_cartan_parabolic_and_fourier
    (c s : R) (v w : ZornVec3 R) :
    zornTracelessExp c s 1 0 0 = zornHyperbolicKernel (c + s) (c - s) ∧
    zornTracelessExp 1 s 0 v 0 = zornExpUpperNil (fun i => s * v i) ∧
    zornTracelessExp 1 s 0 0 w = zornExpLowerNil (fun i => s * w i) ∧
    zornTracelessExp c s 0 v w = zornFourierRotor c s v w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(zornTracelessExp_coords_casimir_norm_and_group_law c s 0 0 0 0 1 0 0).1]
    ext <;> (simp [zornHyperbolicKernel]; try ring)
  · rw [(zornTracelessExp_coords_casimir_norm_and_group_law 1 s 0 0 0 0 0 v 0).1]
    ext <;> (simp [zornExpUpperNil]; try ring)
  · rw [(zornTracelessExp_coords_casimir_norm_and_group_law 1 s 0 0 0 0 0 0 w).1]
    ext <;> (simp [zornExpLowerNil]; try ring)
  · rw [(zornTracelessExp_coords_casimir_norm_and_group_law c s 0 0 0 0 0 v w).1]
    ext <;> (simp [zornFourierRotor]; try ring)

/-- **24. Two-Generator Malcev Commutator Closure of 7D Exponential Flows**:
    For any two exponential flows `E₁ = zornTracelessExp c₁ s₁ α₁ v₁ w₁` and
    `E₂ = zornTracelessExp c₂ s₂ α₂ v₂ w₂` with distinct 7D generators `M₁, M₂`,
    their commutator `E₁ * E₂ - E₂ * E₁` closes inside the 7D traceless Malcev algebra! -/
theorem zornTracelessExp_two_generator_malcev_commutator
    (c₁ s₁ α₁ c₂ s₂ α₂ : R) (v₁ w₁ v₂ w₂ : ZornVec3 R) :
    let E₁ := zornTracelessExp c₁ s₁ α₁ v₁ w₁
    let E₂ := zornTracelessExp c₂ s₂ α₂ v₂ w₂
    E₁ * E₂ - E₂ * E₁ =
      (s₁ * s₂) • zornTracelessFlowGen
        (ZornVec3.dot v₁ w₂ - ZornVec3.dot v₂ w₁)
        (fun i => (2 : R) * (α₁ * v₂ i - α₂ * v₁ i - ZornVec3.cross w₁ w₂ i))
        (fun i => (2 : R) * (α₂ * w₁ i - α₁ * w₂ i + ZornVec3.cross v₁ v₂ i)) := by
  intro E₁ E₂
  have hc1 := (zornTracelessExp_coords_casimir_norm_and_group_law c₁ s₁ 0 0 0 0 α₁ v₁ w₁).1
  have hc2 := (zornTracelessExp_coords_casimir_norm_and_group_law c₂ s₂ 0 0 0 0 α₂ v₂ w₂).1
  dsimp [E₁, E₂]; rw [hc1, hc2]
  simp only [_root_.sub_eq_add_neg]
  ext
  · simp [zornTracelessFlowGen, InfoGeometry.Algebra.zvm_add_def,
          InfoGeometry.Algebra.zvm_neg_def,
          add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]; try ring
  · rename_i i; fin_cases i <;>
      (simp [zornTracelessFlowGen, InfoGeometry.Algebra.zvm_add_def,
             InfoGeometry.Algebra.zvm_neg_def,
             add, neg, mul, ZornVec3.cross]; try ring)
  · rename_i i; fin_cases i <;>
      (simp [zornTracelessFlowGen, InfoGeometry.Algebra.zvm_add_def,
             InfoGeometry.Algebra.zvm_neg_def,
             add, neg, mul, ZornVec3.cross]; try ring)
  · simp [zornTracelessFlowGen, InfoGeometry.Algebra.zvm_add_def,
          InfoGeometry.Algebra.zvm_neg_def,
          add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]; try ring

/-- **25. Exponential Norm Multiplicativity & Adjoint Axis Invariance**:
    For any 7D exponential flow `E = zornTracelessExp c s α v w`, its conjugate
    `E_inv = zornTracelessExp c (-s) α v w`, and ANY 8D state `X`:
    - **Left & Right Norm Multiplicativity**:
      `norm (E * X) = (c * c - s * s * zornTracelessCasimir α v w) * norm X` and
      `norm (X * E) = norm X * (c * c - s * s * zornTracelessCasimir α v w)`.
    - **Adjoint Generator Invariance**:
      `(E * M) * E_inv = (c * c - s * s * zornTracelessCasimir α v w) • M`. -/
theorem zornTracelessExp_norm_multiplicativity_and_adjoint_axis
    (c s α : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    let E := zornTracelessExp c s α v w
    let E_inv := zornTracelessExp c (-s) α v w
    let M := zornTracelessFlowGen α v w
    let κ := zornTracelessCasimir α v w
    norm (E * X) = (c * c - s * s * κ) * norm X ∧
    norm (X * E) = norm X * (c * c - s * s * κ) ∧
    (E * M) * E_inv = (c * c - s * s * κ) • M := by
  intro E E_inv M κ
  have h_norm := (zornTracelessExp_coords_casimir_norm_and_group_law c s 0 0 0 0 α v w).2.1
  have hce := (zornTracelessExp_coords_casimir_norm_and_group_law c s 0 0 0 0 α v w).1
  have hci := (zornTracelessExp_coords_casimir_norm_and_group_law c (-s) 0 0 0 0 α v w).1
  refine ⟨?_, ?_, ?_⟩
  · dsimp [E, κ]; rw [norm_mul, h_norm]
  · dsimp [E, κ]; rw [norm_mul, h_norm]
  · dsimp [E, E_inv, M, κ]; rw [hce, hci]
    ext
    · simp [zornTracelessFlowGen, zornTracelessCasimir,
            mul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornTracelessFlowGen, zornTracelessCasimir,
               mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornTracelessFlowGen, zornTracelessCasimir,
               mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · simp [zornTracelessFlowGen, zornTracelessCasimir,
            mul, ZornVec3.dot, Fin.sum_univ_three]; try ring

/-!
### Two-Sided Moufang Adjoint Spinor Action, Rodrigues–Cartan–Malcev Closure, & Isotropic Eichler–Siegel Cone
-/

/-- **7D Symmetric Clifford Bilinear Pairing (`zornTracelessPairing`)**:
    Satisfies `M * M' + M' * M = zornTracelessPairing α v w α' v' w' • 1`
    and `zornTracelessPairing α v w α v w = 2 * zornTracelessCasimir α v w`. -/
def zornTracelessPairing (α : R) (v w : ZornVec3 R) (α' : R) (v' w' : ZornVec3 R) : R :=
  2 * α * α' + ZornVec3.dot v w' + ZornVec3.dot v' w

/-- **Two-Sided Moufang Adjoint Spinor Action (`zornAdjointSpinorAction c s α v w X`)**:
    `(E(c, s) * X) * E(c, -s)` where `E(c, s) = zornTracelessExp c s α v w`. -/
noncomputable def zornAdjointSpinorAction
    (c s α : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  (zornTracelessExp c s α v w * X) * zornTracelessExp c (-s) α v w

/-- Transformed Cartan scalar coordinate `α''` of `zornAdjointSpinorAction c s α v w (M(α', v', w'))`. -/
def zornAdjointAlpha (c s α : R) (v w : ZornVec3 R) (α' : R) (v' w' : ZornVec3 R) : R :=
  (c * c + s * s * zornTracelessCasimir α v w) * α' -
    s * s * zornTracelessPairing α v w α' v' w' * α +
    c * s * (ZornVec3.dot v w' - ZornVec3.dot v' w)

/-- Transformed upper 3-vector `v''` of `zornAdjointSpinorAction c s α v w (M(α', v', w'))`. -/
def zornAdjointVecV (c s α : R) (v w : ZornVec3 R) (α' : R) (v' w' : ZornVec3 R) : ZornVec3 R :=
  fun i =>
    (c * c + s * s * zornTracelessCasimir α v w) * v' i -
      (s * s * zornTracelessPairing α v w α' v' w') * v i +
      (2 * c * s) * (α * v' i - α' * v i - ZornVec3.cross w w' i)

/-- Transformed lower 3-vector `w''` of `zornAdjointSpinorAction c s α v w (M(α', v', w'))`. -/
def zornAdjointVecW (c s α : R) (v w : ZornVec3 R) (α' : R) (v' w' : ZornVec3 R) : ZornVec3 R :=
  fun i =>
    (c * c + s * s * zornTracelessCasimir α v w) * w' i -
      (s * s * zornTracelessPairing α v w α' v' w') * w i +
      (2 * c * s) * (α' * w i - α * w' i + ZornVec3.cross v v' i)

/-- **26. Cartan–Dieudonné Householder Reflection, Rodrigues–Malcev Decomposition, & 7D Subspace Closure**:
    For any two 7D traceless generators `M = zornTracelessFlowGen α v w` and
    `M' = zornTracelessFlowGen α' v' w'`, and any mode weights `c, s : R`:
    - **7D Householder Reflection Identity**:
      `(M * M') * M = zornTracelessPairing α v w α' v' w' • M - zornTracelessCasimir α v w • M'`
      and `M * (M' * M) = (M * M') * M`.
    - **Rodrigues–Cartan–Malcev Decomposition**:
      `zornAdjointSpinorAction c s α v w M' = (c² + s² κ) • M' - (s² ⟨M, M'⟩) • M + (c s) • (M * M' - M' * M)`.
    - **Exact 7D Traceless Closure**:
      `zornAdjointSpinorAction c s α v w M' = zornTracelessFlowGen α'' v'' w''`. -/
theorem zornAdjointSpinorAction_householder_rodrigues_and_closure
    (c s α : R) (v w : ZornVec3 R) (α' : R) (v' w' : ZornVec3 R) :
    let M := zornTracelessFlowGen α v w
    let M' := zornTracelessFlowGen α' v' w'
    let κ := zornTracelessCasimir α v w
    let pair := zornTracelessPairing α v w α' v' w'
    (M * M') * M = pair • M - κ • M' ∧
    M * (M' * M) = (M * M') * M ∧
    zornAdjointSpinorAction c s α v w M' =
      (c * c + s * s * κ) • M' - (s * s * pair) • M + (c * s) • (M * M' - M' * M) ∧
    zornAdjointSpinorAction c s α v w M' =
      zornTracelessFlowGen
        (zornAdjointAlpha c s α v w α' v' w')
        (zornAdjointVecV c s α v w α' v' w')
        (zornAdjointVecW c s α v w α' v' w') := by
  intro M M' κ pair
  have h_hh : (M * M') * M = pair • M - κ • M' := by
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [M, M', κ, pair, zornTracelessFlowGen, zornTracelessCasimir, zornTracelessPairing,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
            ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [M, M', κ, pair, zornTracelessFlowGen, zornTracelessCasimir, zornTracelessPairing,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
               ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [M, M', κ, pair, zornTracelessFlowGen, zornTracelessCasimir, zornTracelessPairing,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
               ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · simp [M, M', κ, pair, zornTracelessFlowGen, zornTracelessCasimir, zornTracelessPairing,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
            ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring
  have h_flex : M * (M' * M) = (M * M') * M :=
    (sub_eq_zero.mp (bundledAssociator_flexible M M')).symm
  have hce := (zornTracelessExp_coords_casimir_norm_and_group_law c s 0 0 0 0 α v w).1
  have hci := (zornTracelessExp_coords_casimir_norm_and_group_law c (-s) 0 0 0 0 α v w).1
  have h_clos : zornAdjointSpinorAction c s α v w M' =
      zornTracelessFlowGen
        (zornAdjointAlpha c s α v w α' v' w')
        (zornAdjointVecV c s α v w α' v' w')
        (zornAdjointVecW c s α v w α' v' w') := by
    dsimp [zornAdjointSpinorAction, M']; rw [hce, hci]
    ext
    · simp [zornTracelessFlowGen, zornAdjointAlpha, zornTracelessCasimir, zornTracelessPairing,
            mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [zornTracelessFlowGen, zornAdjointVecV, zornTracelessCasimir, zornTracelessPairing,
               mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [zornTracelessFlowGen, zornAdjointVecW, zornTracelessCasimir, zornTracelessPairing,
               mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · simp [zornTracelessFlowGen, zornAdjointAlpha, zornTracelessCasimir, zornTracelessPairing,
            mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring
  refine ⟨h_hh, h_flex, ?_, h_clos⟩
  rw [h_clos]
  simp only [_root_.sub_eq_add_neg]
  ext
  · simp [M, M', κ, pair, zornTracelessFlowGen, zornAdjointAlpha,
          zornTracelessCasimir, zornTracelessPairing,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
          ZornVec3.dot, Fin.sum_univ_three]; try ring
  · rename_i i; fin_cases i <;>
      (simp [M, M', κ, pair, zornTracelessFlowGen, zornAdjointVecV,
             zornTracelessCasimir, zornTracelessPairing,
             InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
             ZornVec3.cross]; try ring)
  · rename_i i; fin_cases i <;>
      (simp [M, M', κ, pair, zornTracelessFlowGen, zornAdjointVecW,
             zornTracelessCasimir, zornTracelessPairing,
             InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
             ZornVec3.cross]; try ring)
  · simp [M, M', κ, pair, zornTracelessFlowGen, zornAdjointAlpha,
          zornTracelessCasimir, zornTracelessPairing,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
          ZornVec3.dot, Fin.sum_univ_three]; try ring

/-- **27. Tracelessness Preservation & Conformal Norm Similitude (`Spin(4, 3)` Action)**:
    For any 7D traceless generator `M' = zornTracelessFlowGen α' v' w'` and ANY 8D state `X`:
    - **Tracelessness**: `trace (zornAdjointSpinorAction c s α v w M') = 0`.
    - **8D Quadratic Norm Similitude**:
      `norm (zornAdjointSpinorAction c s α v w X) = (c² - s² κ)² * norm X`. -/
theorem zornAdjointSpinorAction_norm_scaling
    (c s α : R) (v w : ZornVec3 R) (α' : R) (v' w' : ZornVec3 R) (X : ZornVectorMatrix R) :
    let M' := zornTracelessFlowGen α' v' w'
    let κ := zornTracelessCasimir α v w
    trace (zornAdjointSpinorAction c s α v w M') = 0 ∧
    norm (zornAdjointSpinorAction c s α v w X) =
      (c * c - s * s * κ) * (c * c - s * s * κ) * norm X := by
  intro M' κ
  have h_clos :=
    (zornAdjointSpinorAction_householder_rodrigues_and_closure c s α v w α' v' w').2.2.2
  have h_n1 := (zornTracelessExp_coords_casimir_norm_and_group_law c s 0 0 0 0 α v w).2.1
  have h_n2 : norm (zornTracelessExp c (-s) α v w) = c * c - s * s * κ := by
    have h0 := (zornTracelessExp_coords_casimir_norm_and_group_law c (-s) 0 0 0 0 α v w).2.1
    simpa [κ, neg_mul, mul_neg] using h0
  refine ⟨?_, ?_⟩
  · dsimp [M']; rw [h_clos]
    simp [trace, zornTracelessFlowGen]
  · dsimp [zornAdjointSpinorAction, κ]
    rw [norm_mul, norm_mul, h_n1, h_n2]
    ring

/-- **28. 7D `(4, 3)` Casimir & Operator Square Similitude of the Adjoint Spinor Action**:
    The transformed 7D coordinates `(α'', v'', w'')` satisfy:
    - `zornTracelessCasimir α'' v'' w'' = (c² - s² κ)² * zornTracelessCasimir α' v' w'`.
    - `(zornAdjointSpinorAction c s α v w M')² = ((c² - s² κ)² * zornTracelessCasimir α' v' w') • 1`. -/
theorem zornAdjointSpinorAction_casimir_and_square_scaling
    (c s α : R) (v w : ZornVec3 R) (α' : R) (v' w' : ZornVec3 R) :
    let M' := zornTracelessFlowGen α' v' w'
    let κ := zornTracelessCasimir α v w
    let κ' := zornTracelessCasimir α' v' w'
    let α'' := zornAdjointAlpha c s α v w α' v' w'
    let v'' := zornAdjointVecV c s α v w α' v' w'
    let w'' := zornAdjointVecW c s α v w α' v' w'
    zornTracelessCasimir α'' v'' w'' = (c * c - s * s * κ) * (c * c - s * s * κ) * κ' ∧
    zornAdjointSpinorAction c s α v w M' * zornAdjointSpinorAction c s α v w M' =
      ((c * c - s * s * κ) * (c * c - s * s * κ) * κ') • (one : ZornVectorMatrix R) := by
  intro M' κ κ' α'' v'' w''
  have h_norm_cas : ∀ (β : R) (x y : ZornVec3 R),
      norm (zornTracelessFlowGen β x y) = -zornTracelessCasimir β x y := by
    intro β x y
    simp [norm, zornTracelessFlowGen, zornTracelessCasimir]
    ring
  have h_clos : zornAdjointSpinorAction c s α v w M' = zornTracelessFlowGen α'' v'' w'' :=
    (zornAdjointSpinorAction_householder_rodrigues_and_closure c s α v w α' v' w').2.2.2
  have h_ns := (zornAdjointSpinorAction_norm_scaling c s α v w α' v' w' M').2
  have h_cas : zornTracelessCasimir α'' v'' w'' =
      (c * c - s * s * κ) * (c * c - s * s * κ) * κ' := by
    have h1 : norm (zornTracelessFlowGen α'' v'' w'') =
        (c * c - s * s * κ) * (c * c - s * s * κ) * norm M' := by
      rw [← h_clos]; exact h_ns
    rw [h_norm_cas α'' v'' w'', h_norm_cas α' v' w'] at h1
    dsimp [κ']
    linear_combination -h1
  refine ⟨h_cas, ?_⟩
  rw [h_clos, (zornTracelessFlowGen_casimir_klein_gordon_and_clifford α'' 0 v'' w'' 0 0 0).1, h_cas]

/-- **29. 1-Parameter Group Composition Law of the Moufang Adjoint Spinor Action**:
    For ANY 8D split-octonion `X : ZornVectorMatrix R`, two successive adjoint actions
    sharing the same 7D generator `(α, v, w)` compose strictly by the 1-parameter
    Cayley–Hamilton group law! -/
theorem zornAdjointSpinorAction_comp
    (c₁ s₁ c₂ s₂ α : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    zornAdjointSpinorAction c₁ s₁ α v w (zornAdjointSpinorAction c₂ s₂ α v w X) =
      zornAdjointSpinorAction
        (c₁ * c₂ + s₁ * s₂ * zornTracelessCasimir α v w)
        (c₁ * s₂ + s₁ * c₂) α v w X := by
  let κ := zornTracelessCasimir α v w
  let c₁₂ := c₁ * c₂ + s₁ * s₂ * κ
  let s₁₂ := c₁ * s₂ + s₁ * c₂
  let E₁ := zornTracelessExp c₁ s₁ α v w
  let E₂ := zornTracelessExp c₂ s₂ α v w
  let E₁' := zornTracelessExp c₁ (-s₁) α v w
  let E₂' := zornTracelessExp c₂ (-s₂) α v w
  let E₁₂ := zornTracelessExp c₁₂ s₁₂ α v w
  let E₁₂' := zornTracelessExp c₁₂ (-s₁₂) α v w
  change (E₁ * ((E₂ * X) * E₂')) * E₁' = (E₁₂ * X) * E₁₂'
  have h1 : (E₂ * X) * E₂' = E₂ * (X * E₂') :=
    sub_eq_zero.mp
      (zornTracelessExp_artin_associativity_and_state_inversion 0 0 c₂ s₂ c₂ (-s₂) α v w X).2.2.1
  have h2 : E₁ * (E₂ * (X * E₂')) = (E₁ * E₂) * (X * E₂') :=
    (sub_eq_zero.mp
      (zornTracelessExp_artin_associativity_and_state_inversion 0 0 c₁ s₁ c₂ s₂ α v w (X * E₂')).1).symm
  have h_mul12 : E₁ * E₂ = E₁₂ :=
    (zornTracelessExp_coords_casimir_norm_and_group_law 0 0 c₁ s₁ c₂ s₂ α v w).2.2.1
  have h3 : (E₁₂ * (X * E₂')) * E₁' = E₁₂ * ((X * E₂') * E₁') :=
    sub_eq_zero.mp
      (zornTracelessExp_artin_associativity_and_state_inversion 0 0 c₁₂ s₁₂ c₁ (-s₁) α v w (X * E₂')).2.2.1
  have h4 : (X * E₂') * E₁' = X * (E₂' * E₁') :=
    sub_eq_zero.mp
      (zornTracelessExp_artin_associativity_and_state_inversion 0 0 c₂ (-s₂) c₁ (-s₁) α v w X).2.1
  have h_mul12' : E₂' * E₁' = E₁₂' := by
    have h0 :=
      (zornTracelessExp_coords_casimir_norm_and_group_law 0 0 c₂ (-s₂) c₁ (-s₁) α v w).2.2.1
    dsimp [E₂', E₁', E₁₂', c₁₂, s₁₂, κ] at h0 ⊢
    rw [h0]
    congr 1 <;> ring
  have h5 : E₁₂ * (X * E₁₂') = (E₁₂ * X) * E₁₂' :=
    (sub_eq_zero.mp
      (zornTracelessExp_artin_associativity_and_state_inversion 0 0 c₁₂ s₁₂ c₁₂ (-s₁₂) α v w X).2.2.1).symm
  rw [h1, h2, h_mul12, h3, h4, h_mul12', h5]

/-- **30. Two-Sided Adjoint Inversion, Vanishing Parenthesization Defect, & Unipotent Residual**:
    For ANY 8D state `X : ZornVectorMatrix R`:
    - `zornAdjointSpinorAction c (-s) α v w (zornAdjointSpinorAction c s α v w X) = (c² - s² κ)² • X`.
    - `zornAdjointSpinorAction c s α v w (zornAdjointSpinorAction c (-s) α v w X) = (c² - s² κ)² • X`.
    - `(E(c, s) * X) * E(c, -s) - E(c, s) * (X * E(c, -s)) = 0`.
    - `zornAdjointSpinorAction 1 (-s) α v w (zornAdjointSpinorAction 1 s α v w X) - X = (κ * s * s * (s * s * κ - 2)) • X`. -/
theorem zornAdjointSpinorAction_two_sided_inverse_and_defect
    (c s α : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    let κ := zornTracelessCasimir α v w
    let E := zornTracelessExp c s α v w
    let E_inv := zornTracelessExp c (-s) α v w
    zornAdjointSpinorAction c (-s) α v w (zornAdjointSpinorAction c s α v w X) =
      ((c * c - s * s * κ) * (c * c - s * s * κ)) • X ∧
    zornAdjointSpinorAction c s α v w (zornAdjointSpinorAction c (-s) α v w X) =
      ((c * c - s * s * κ) * (c * c - s * s * κ)) • X ∧
    (E * X) * E_inv - E * (X * E_inv) = 0 ∧
    zornAdjointSpinorAction 1 (-s) α v w (zornAdjointSpinorAction 1 s α v w X) - X =
      (κ * s * s * (s * s * κ - 2)) • X := by
  intro κ E E_inv
  have h_zero_exp : ∀ r : R, zornTracelessExp r 0 α v w = r • (one : ZornVectorMatrix R) := by
    intro r
    simp [zornTracelessExp]
  have h_zero_act : ∀ r : R, zornAdjointSpinorAction r 0 α v w X = (r * r) • X := by
    intro r
    dsimp [zornAdjointSpinorAction]
    rw [neg_zero, h_zero_exp r]
    change mul (mul (smul r one) X) (smul r one) = smul (r * r) X
    rw [ZornVectorMatrix.smul_mul, ZornVectorMatrix.one_mul,
        ZornVectorMatrix.mul_smul, ZornVectorMatrix.mul_one]
    change (r • (r • X)) = (r * r) • X
    rw [smul_smul]
  have h_inv : ∀ p q : R,
      zornAdjointSpinorAction p (-q) α v w (zornAdjointSpinorAction p q α v w X) =
        ((p * p - q * q * κ) * (p * p - q * q * κ)) • X := by
    intro p q
    rw [zornAdjointSpinorAction_comp]
    have hc : p * p + -q * q * zornTracelessCasimir α v w = p * p - q * q * κ := by
      dsimp [κ]; ring
    have hs : p * q + -q * p = 0 := by ring
    rw [hc, hs, h_zero_act]
  refine ⟨h_inv c s, ?_, ?_, ?_⟩
  · have h0 := h_inv c (-s)
    simpa [neg_neg, neg_mul, mul_neg] using h0
  · exact (zornTracelessExp_artin_associativity_and_state_inversion 0 0 c s c (-s) α v w X).2.2.1
  · rw [h_inv 1 s]
    nth_rw 2 [← _root_.one_smul R X]
    rw [← _root_.sub_smul]
    congr 1
    ring

/-- Isotropic scalar coordinate `α(u, w) := u ⋅ w` on the 6D null quadric cone. -/
def isotropicAlpha (u w : ZornVec3 R) : R :=
  ZornVec3.dot u w

/-- Isotropic upper 3-vector `v(u, p, w) := -(u ⋅ w) • u + p × w` satisfying `α² + v ⋅ w = 0`. -/
def isotropicVecV (u p w : ZornVec3 R) : ZornVec3 R :=
  fun i => -(ZornVec3.dot u w * u i) + ZornVec3.cross p w i

/-- Division-free 7D traceless isotropic generator `L(u, p, w)` on the null cone `Q(L) = 0`. -/
def isotropicGen (u p w : ZornVec3 R) : ZornVectorMatrix R :=
  zornTracelessFlowGen (isotropicAlpha u w) (isotropicVecV u p w) w

/-- Unipotent parabolic exponential `exp(s L(u, p, w)) = 1 + s • L(u, p, w)` (`norm = 1`). -/
noncomputable def isotropicExp (s : R) (u p w : ZornVec3 R) : ZornVectorMatrix R :=
  zornTracelessExp 1 s (isotropicAlpha u w) (isotropicVecV u p w) w

/-- Two-sided unipotent Eichler–Siegel transvection `(exp(s L) * X) * exp(-s L)`. -/
noncomputable def isotropicAdjointAction
    (s : R) (u p w : ZornVec3 R) (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  zornAdjointSpinorAction 1 s (isotropicAlpha u w) (isotropicVecV u p w) w X

/-- **31. Division-Free Isotropic Nilpotent Cone (`Q(L) = 0, L² = 0`), Rank-1 Jordan Operator, & Eichler–Siegel Transvections**:
    For ANY three 3-vectors `u, p, w : ZornVec3 R`, any 7D generator `M' = zornTracelessFlowGen α' v' w'`,
    and any 8D state `X : ZornVectorMatrix R`:
    - **Identical Null Casimir**: `zornTracelessCasimir (isotropicAlpha u w) (isotropicVecV u p w) w = 0`.
    - **Nilpotent Square & Wave Annihilation**: `L * L = 0`, `L * (L * X) = 0`, and `(X * L) * L = 0`.
    - **Rank-1 Jordan Triple Projection**:
      `(L * M') * L = zornTracelessPairing (isotropicAlpha u w) (isotropicVecV u p w) w α' v' w' • L`.
    - **Eichler–Siegel Parabolic Transvection**:
      `isotropicAdjointAction s u p w M' = M' - (s² ⟨L, M'⟩) • L + s • (L * M' - M' * L)`. -/
theorem isotropicGen_nilpotence_and_eichler_siegel_transvection
    (s : R) (u p w : ZornVec3 R) (α' : R) (v' w' : ZornVec3 R) (X : ZornVectorMatrix R) :
    let α₀ := isotropicAlpha u w
    let v₀ := isotropicVecV u p w
    let L := isotropicGen u p w
    let M' := zornTracelessFlowGen α' v' w'
    let pair := zornTracelessPairing α₀ v₀ w α' v' w'
    zornTracelessCasimir α₀ v₀ w = 0 ∧
    L * L = 0 ∧
    L * (L * X) = 0 ∧
    (X * L) * L = 0 ∧
    (L * M') * L = pair • L ∧
    isotropicAdjointAction s u p w M' =
      M' - (s * s * pair) • L + s • (L * M' - M' * L) := by
  intro α₀ v₀ L M' pair
  have h_cas : zornTracelessCasimir α₀ v₀ w = 0 := by
    simp [α₀, v₀, zornTracelessCasimir, isotropicAlpha, isotropicVecV,
          ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  have h18 := zornTracelessFlowGen_casimir_klein_gordon_and_clifford α₀ 0 v₀ w 0 0 X
  have h26 := zornAdjointSpinorAction_householder_rodrigues_and_closure 1 s α₀ v₀ w α' v' w'
  have hL : L = zornTracelessFlowGen α₀ v₀ w := rfl
  have hA : isotropicAdjointAction s u p w M' = zornAdjointSpinorAction 1 s α₀ v₀ w M' := rfl
  refine ⟨h_cas, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL, h18.1, h_cas, _root_.zero_smul]
  · rw [hL, h18.2.1, h_cas, _root_.zero_smul]
  · rw [hL, h18.2.2.1, h_cas, _root_.zero_smul]
  · rw [hL, h26.1, h_cas, _root_.zero_smul, _root_.sub_zero]
  · rw [hA, hL, h26.2.2.1, h_cas]
    simp [M', pair, _root_.one_mul]

/-- **32. Unipotent Group Law, Exact Division-Free Inversion, & Norm/Casimir Isometry on the Isotropic Cone**:
    For ANY `s, s₁, s₂, α' : R`, `u, p, w, v', w' : ZornVec3 R`, and 8D state `X : ZornVectorMatrix R`:
    - **Unipotent Norm**: `norm (isotropicExp s u p w) = 1`.
    - **Additive 1-Parameter Subgroup Law**:
      `isotropicExp s₁ u p w * isotropicExp s₂ u p w = isotropicExp (s₁ + s₂) u p w`.
    - **Additive Adjoint Group Law**:
      `isotropicAdjointAction s₁ u p w (isotropicAdjointAction s₂ u p w X) = isotropicAdjointAction (s₁ + s₂) u p w X`.
    - **Exact Division-Free Inversion (`s ↦ -s`)**:
      `isotropicAdjointAction (-s) u p w (isotropicAdjointAction s u p w X) = X`.
    - **Exact 8D Norm & 7D Casimir Isometry**:
      `norm (isotropicAdjointAction s u p w X) = norm X` and
      `zornTracelessCasimir α'' v'' w'' = zornTracelessCasimir α' v' w'`! -/
theorem isotropicAdjointAction_group_inversion_and_isometry
    (s s₁ s₂ α' : R) (u p w v' w' : ZornVec3 R) (X : ZornVectorMatrix R) :
    let α₀ := isotropicAlpha u w
    let v₀ := isotropicVecV u p w
    norm (isotropicExp s u p w) = 1 ∧
    isotropicExp s₁ u p w * isotropicExp s₂ u p w = isotropicExp (s₁ + s₂) u p w ∧
    isotropicAdjointAction s₁ u p w (isotropicAdjointAction s₂ u p w X) =
      isotropicAdjointAction (s₁ + s₂) u p w X ∧
    isotropicAdjointAction (-s) u p w (isotropicAdjointAction s u p w X) = X ∧
    norm (isotropicAdjointAction s u p w X) = norm X ∧
    zornTracelessCasimir
        (zornAdjointAlpha 1 s α₀ v₀ w α' v' w')
        (zornAdjointVecV 1 s α₀ v₀ w α' v' w')
        (zornAdjointVecW 1 s α₀ v₀ w α' v' w') =
      zornTracelessCasimir α' v' w' := by
  intro α₀ v₀
  have h_cas : zornTracelessCasimir α₀ v₀ w = 0 :=
    (isotropicGen_nilpotence_and_eichler_siegel_transvection 0 u p w 0 0 0 0).1
  have hE : ∀ q : R, isotropicExp q u p w = zornTracelessExp 1 q α₀ v₀ w := fun _ => rfl
  have hA : ∀ q : R, ∀ Y : ZornVectorMatrix R,
      isotropicAdjointAction q u p w Y = zornAdjointSpinorAction 1 q α₀ v₀ w Y := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hE s, (zornTracelessExp_coords_casimir_norm_and_group_law 1 s 0 0 0 0 α₀ v₀ w).2.1, h_cas]
    ring
  · rw [hE s₁, hE s₂, hE (s₁ + s₂),
        (zornTracelessExp_coords_casimir_norm_and_group_law 0 0 1 s₁ 1 s₂ α₀ v₀ w).2.2.1, h_cas]
    congr 1 <;> ring
  · rw [hA s₂ X, hA s₁ _, hA (s₁ + s₂) X, zornAdjointSpinorAction_comp, h_cas]
    congr 1 <;> ring
  · rw [hA s X, hA (-s) _,
        (zornAdjointSpinorAction_two_sided_inverse_and_defect 1 s α₀ v₀ w X).1, h_cas]
    simp [_root_.one_smul]
  · rw [hA s X, (zornAdjointSpinorAction_norm_scaling 1 s α₀ v₀ w 0 0 0 X).2, h_cas]
    ring
  · rw [(zornAdjointSpinorAction_casimir_and_square_scaling 1 s α₀ v₀ w α' v' w').1, h_cas]
    ring

/-- Universal polynomial family of tilted upper projective Peirce idempotents `Π_+(r₁, r₂, c, s, v, w)`. -/
def tiltedPeircePlus (r₁ r₂ c s : R) (v w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨c * c,
   fun i => -(r₁ * c * s * v i),
   fun i => (r₂ * c * s) * w i,
   -(r₁ * r₂ * (s * s) * ZornVec3.dot v w)⟩

/-- Universal polynomial family of tilted lower projective Peirce idempotents `Π_-(r₁, r₂, c, s, v, w)`. -/
def tiltedPeirceMinus (r₁ r₂ c s : R) (v w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨-(r₁ * r₂ * (s * s) * ZornVec3.dot v w),
   fun i => (r₁ * c * s) * v i,
   fun i => -(r₂ * c * s * w i),
   c * c⟩

/-- **33. Universal Polynomial Projective Peirce Idempotence, Chordal Square, & Left Peirce Syzygy**:
    For ANY scalars `r₁, r₂, c, s : R` and 3-vectors `v, w : ZornVec3 R`, let
    `P_+ = tiltedPeircePlus r₁ r₂ c s v w`, `P_- = tiltedPeirceMinus r₁ r₂ c s v w`, and
    `N_vw = c * c - r₁ * r₂ * (s * s) * (v ⋅ w)`:
    - **Mutual Orthogonality**: `P_+ * P_- = 0`.
    - **Projective Idempotence**: `P_+ * P_+ = N_vw • P_+`.
    - **Universal Grassmannian Chordal Distance Identity**:
      `(P_+ - N_vw • E11)² = (-(r₁ * r₂ * s² * (v ⋅ w)) * N_vw) • 1`.
    - **Left Peirce Module Annihilation Syzygy**:
      `(r₁ * r₂ * s * (v ⋅ w)) • (E11 * P_+) - c • ((E11 * zornTiltedVelocity r₁ r₂ v w) * P_+) = 0`! -/
theorem tiltedPeirce_orth_idem_chordal_and_syzygy
    (r₁ r₂ c s : R) (v w : ZornVec3 R) :
    let P_plus := tiltedPeircePlus r₁ r₂ c s v w
    let P_minus := tiltedPeirceMinus r₁ r₂ c s v w
    let N_vw := c * c - r₁ * r₂ * (s * s) * ZornVec3.dot v w
    let Q := zornTiltedVelocity r₁ r₂ v w
    P_plus * P_minus = 0 ∧
    P_plus * P_plus = N_vw • P_plus ∧
    (P_plus - N_vw • E11) * (P_plus - N_vw • E11) =
      (-(r₁ * r₂ * (s * s) * ZornVec3.dot v w) * N_vw) • (one : ZornVectorMatrix R) ∧
    (r₁ * r₂ * s * ZornVec3.dot v w) • (E11 * P_plus) -
      c • ((E11 * Q) * P_plus) = 0 := by
  intro P_plus P_minus N_vw Q
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext
    · simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            mul, zero, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
               mul, zero, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
               mul, zero, ZornVec3.cross]; try ring)
    · simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            mul, zero, ZornVec3.dot, Fin.sum_univ_three]; try ring
  · ext
    · simp [P_plus, N_vw, tiltedPeircePlus,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [P_plus, N_vw, tiltedPeircePlus,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [P_plus, N_vw, tiltedPeircePlus,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
               mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · simp [P_plus, N_vw, tiltedPeircePlus,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_smul_def,
            mul, smul, ZornVec3.dot, Fin.sum_univ_three]; try ring
  · simp only [_root_.sub_eq_add_neg]
    ext
    · simp [P_plus, N_vw, E11, one, tiltedPeircePlus,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
            ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [P_plus, N_vw, E11, one, tiltedPeircePlus,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
               ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [P_plus, N_vw, E11, one, tiltedPeircePlus,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
               ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · simp [P_plus, N_vw, E11, one, tiltedPeircePlus,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, add, neg, mul,
            ZornVec3.dot, Fin.sum_univ_three]; try ring
  · simp only [_root_.sub_eq_add_neg]
    ext
    · simp [P_plus, Q, E11, tiltedPeircePlus, zornTiltedVelocity,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [P_plus, Q, E11, tiltedPeircePlus, zornTiltedVelocity,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [P_plus, Q, E11, tiltedPeircePlus, zornTiltedVelocity,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
               add, neg, mul, zero, ZornVec3.cross]; try ring)
    · simp [P_plus, Q, E11, tiltedPeircePlus, zornTiltedVelocity,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
            add, neg, mul, zero, ZornVec3.dot]; try ring

/-!
### Master Unification Slice Embedding ($M_2(R) \hookrightarrow \mathrm{Zorn}(R)$) & Algebraic Rigidity Laws
-/

/-- Directional slice embedding $\Phi_{u, w} : M_2(R) \to \mathrm{Zorn}(R)$ sending
    $\begin{pmatrix} X_{00} & X_{01} \\ X_{10} & X_{11} \end{pmatrix} \mapsto
     \langle X_{00}, X_{01} \bullet u, X_{10} \bullet w, X_{11} \rangle$. -/
def sliceEmbed (u w : ZornVec3 R) (X : Matrix (Fin 2) (Fin 2) R) : ZornVectorMatrix R :=
  ⟨X 0 0, fun i => X 0 1 * u i, fun i => X 1 0 * w i, X 1 1⟩

/-- Deformed $2 \times 2$ matrix product $X \star_{u \cdot w} Y$ induced by the off-diagonal
    contraction $u \cdot w$ (which reduces to standard matrix multiplication when $u \cdot w = 1$). -/
def deformedMatMul (u w : ZornVec3 R) (X Y : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![X 0 0 * Y 0 0 + ZornVec3.dot u w * X 0 1 * Y 1 0, X 0 0 * Y 0 1 + X 0 1 * Y 1 1;
     Y 0 0 * X 1 0 + X 1 1 * Y 1 0, ZornVec3.dot u w * X 1 0 * Y 0 1 + X 1 1 * Y 1 1]

/-- **34. Master Slice Embedding Unification Theorem ($\Phi_{u, w} : M_2(R) \hookrightarrow \mathrm{Zorn}(R)$)**:
    For ANY $u, w : \mathrm{ZornVec3}\;R$ and ANY $2 \times 2$ matrices $X, Y, Z \in M_2(R)$:
    - **Exact Multiplicative Homomorphism**:
      `sliceEmbed u w X * sliceEmbed u w Y = sliceEmbed u w (deformedMatMul u w X Y)`
      (since $u \times u = 0$ and $w \times w = 0$ annihilate all non-associative cross terms).
    - **Identical Associativity of Every Directional Slice**:
      `zornAssociator (sliceEmbed u w X) (sliceEmbed u w Y) (sliceEmbed u w Z) = 0`.
    - **Norm–Determinant Bridge**:
      `norm (sliceEmbed u w X) = X 0 0 * X 1 1 - (u ⋅ w) * (X 0 1 * X 1 0)`.
    - **Traceless $\mathfrak{sl}_2(R) \hookrightarrow \mathrm{Im}(\mathrm{Zorn}(R))$ Casimir Bridge**:
      For $M_{\mathrm{mat}} = \begin{pmatrix} \alpha & \beta \\ \gamma & -\alpha \end{pmatrix}$,
      `sliceEmbed u w M_mat = zornTracelessFlowGen α (β • u) (γ • w)` and
      `sliceEmbed u w M_mat * sliceEmbed u w M_mat = (α * α + β * γ * (u ⋅ w)) • 1`! -/
theorem master_slice_embedding_unification
    (u w : ZornVec3 R) (X Y Z : Matrix (Fin 2) (Fin 2) R) (α β γ : R) :
    let M_mat : Matrix (Fin 2) (Fin 2) R := !![α, β; γ, -α]
    sliceEmbed u w X * sliceEmbed u w Y =
      sliceEmbed u w (deformedMatMul u w X Y) ∧
    zornAssociator (sliceEmbed u w X) (sliceEmbed u w Y) (sliceEmbed u w Z) = 0 ∧
    norm (sliceEmbed u w X) =
      X 0 0 * X 1 1 - ZornVec3.dot u w * (X 0 1 * X 1 0) ∧
    sliceEmbed u w M_mat =
      zornTracelessFlowGen α (fun i => β * u i) (fun i => γ * w i) ∧
    sliceEmbed u w M_mat * sliceEmbed u w M_mat =
      (α * α + β * γ * ZornVec3.dot u w) • (one : ZornVectorMatrix R) := by
  intro M_mat
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext
    · simp [sliceEmbed, deformedMatMul, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [sliceEmbed, deformedMatMul, mul, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (simp [sliceEmbed, deformedMatMul, mul, ZornVec3.cross]; ring)
    · simp [sliceEmbed, deformedMatMul, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [sliceEmbed, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [sliceEmbed, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring)
    · rename_i i; fin_cases i <;>
        (simp [sliceEmbed, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring)
    · simp [sliceEmbed, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
  · simp [norm, sliceEmbed, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · ext <;> simp [M_mat, sliceEmbed, zornTracelessFlowGen]
  · ext
    · simp [M_mat, sliceEmbed, one, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [M_mat, sliceEmbed, one, mul, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (simp [M_mat, sliceEmbed, one, mul, ZornVec3.cross]; ring)
    · simp [M_mat, sliceEmbed, one, mul, ZornVec3.dot, Fin.sum_univ_three]; ring

/-- **35. Cayley–Dickson Involution Duality, Universal Quadratic Equation, & Anti-Automorphism**:
    For ANY $X, Y \in \mathrm{Zorn}(R)$:
    - **Trace-Conjugate Additivity**: `X + conj X = trace X • 1`.
    - **Norm-Conjugate Multiplicativity**: `X * conj X = norm X • 1` and `conj X * X = norm X • 1`.
    - **Universal Cayley–Hamilton Identity**: `X * X - trace X • X + norm X • 1 = 0`.
    - **Involution Anti-Automorphism**: `conj (X * Y) = conj Y * conj X`. -/
theorem zorn_involution_cayley_hamilton_and_antiautomorphism (X Y : ZornVectorMatrix R) :
    X + conj X = trace X • (one : ZornVectorMatrix R) ∧
    X * conj X = norm X • (one : ZornVectorMatrix R) ∧
    conj X * X = norm X • (one : ZornVectorMatrix R) ∧
    X * X - trace X • X + norm X • (one : ZornVectorMatrix R) = 0 ∧
    conj (X * Y) = conj Y * conj X := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext
    · simp [conj, trace, one, InfoGeometry.Algebra.zvm_add_def, add]
    · rename_i i; fin_cases i <;>
        simp [conj, one, InfoGeometry.Algebra.zvm_add_def, add]
    · rename_i i; fin_cases i <;>
        simp [conj, one, InfoGeometry.Algebra.zvm_add_def, add]
    · simp [conj, trace, one, InfoGeometry.Algebra.zvm_add_def, add]; ring
  · ext
    · simp [conj, norm, one, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [conj, one, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [conj, one, mul, ZornVec3.cross]; try ring)
    · simp [conj, norm, one, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
  · ext
    · simp [conj, norm, one, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [conj, one, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [conj, one, mul, ZornVec3.cross]; try ring)
    · simp [conj, norm, one, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
  · simp only [_root_.sub_eq_add_neg]
    ext
    · simp [trace, norm, one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, zero, ZornVec3.dot]; ring
    · rename_i i; fin_cases i <;>
        (simp [trace, norm, one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, zero, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (simp [trace, norm, one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, zero, ZornVec3.cross]; ring)
    · simp [trace, norm, one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, zero, ZornVec3.dot, Fin.sum_univ_three]; ring
  · exact conj_mul X Y

/-- **36. Complete Skew-Symmetry (Alternativity) & Purely Traceless Structure of the Associator**:
    For ANY three elements $X, Y, Z \in \mathrm{Zorn}(R)$:
    - **Vanishing Trace**: `trace (zornAssociator X Y Z) = 0`.
    - **Anti-Invariance under Cayley Conjugation**: `conj (zornAssociator X Y Z) = -zornAssociator X Y Z`.
    - **Left, Right, and Middle Skew-Symmetry**:
      `zornAssociator X Y Z + zornAssociator Y X Z = 0`,
      `zornAssociator X Y Z + zornAssociator X Z Y = 0`, and
      `zornAssociator X Y Z + zornAssociator Z Y X = 0`. -/
theorem associator_traceless_and_totally_alternating (X Y Z : ZornVectorMatrix R) :
    trace (zornAssociator X Y Z) = 0 ∧
    conj (zornAssociator X Y Z) = -zornAssociator X Y Z ∧
    zornAssociator X Y Z + zornAssociator Y X Z = 0 ∧
    zornAssociator X Y Z + zornAssociator X Z Y = 0 ∧
    zornAssociator X Y Z + zornAssociator Z Y X = 0 := by
  have h12 : zornAssociator X Y Z + zornAssociator Y X Z = 0 := by
    change bundledAssociator X Y Z + bundledAssociator Y X Z = 0
    rw [bundledAssociator_swap12 X Y Z]
    abel
  have h23 : zornAssociator X Y Z + zornAssociator X Z Y = 0 := by
    change bundledAssociator X Y Z + bundledAssociator X Z Y = 0
    rw [bundledAssociator_swap23 X Y Z]
    abel
  have h13 : zornAssociator X Y Z + zornAssociator Z Y X = 0 := by
    change bundledAssociator X Y Z + bundledAssociator Z Y X = 0
    rw [bundledAssociator_swap12 Z Y X, ← bundledAssociator_cycle X Y Z]
    abel
  refine ⟨?_, ?_, h12, h23, h13⟩
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    simp [trace, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          add, neg, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, ZornVec3.dot, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, ZornVec3.dot, ZornVec3.cross]; try ring)
    · simp [conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring

/-- **37. The Three Universal Moufang Loop Identities on $\mathrm{Zorn}(R)$**:
    For ANY $X, Y, Z \in \mathrm{Zorn}(R)$:
    - **Left Moufang Identity**: `X * (Y * (X * Z)) = ((X * Y) * X) * Z`.
    - **Right Moufang Identity**: `((Z * X) * Y) * X = Z * (X * (Y * X))`.
    - **Middle (Bimodule) Moufang Identity**: `(X * Y) * (Z * X) = X * ((Y * Z) * X)`. -/
theorem zorn_universal_moufang_identities (X Y Z : ZornVectorMatrix R) :
    X * (Y * (X * Z)) = ((X * Y) * X) * Z ∧
    ((Z * X) * Y) * X = Z * (X * (Y * X)) ∧
    (X * Y) * (Z * X) = X * ((Y * Z) * X) :=
  ⟨left_moufang Y Z X, right_moufang X Z Y, middle_moufang X Y Z⟩

/-!
### Two-Sided Projective Peirce Decomposition, Rank-1 Diagonal Corner Reduction, & Frobenius–Schur Norm Factorization
-/

/-- Upper Peirce corner linear functional `τ_+(X)` satisfying `(Π_+ * X) * Π_+ = τ_+(X) • Π_+`. -/
def zornPeirceCornerTracePlus (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) : R :=
  c * c * X.a - r₁ * c * s * ZornVec3.dot v X.w + r₂ * c * s * ZornVec3.dot X.v w -
    r₁ * r₂ * (s * s) * ZornVec3.dot v w * X.b

/-- Lower Peirce corner linear functional `τ_-(X)` satisfying `(Π_- * X) * Π_- = τ_-(X) • Π_-`. -/
def zornPeirceCornerTraceMinus (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) : R :=
  -(r₁ * r₂ * (s * s) * ZornVec3.dot v w) * X.a + r₁ * c * s * ZornVec3.dot v X.w -
    r₂ * c * s * ZornVec3.dot X.v w + c * c * X.b

/-- **38. Isotropic Norm, Central Resolution of Identity, & Artin Peirce Module Associativity**:
    For ANY $r_1, r_2, c, s \in R$, $v, w \in R^3$, and arbitrary $X \in \mathrm{Zorn}(R)$, let
    $\Pi_\pm = \mathrm{tiltedPeirce\pm}\;r_1\;r_2\;c\;s\;v\;w$ and $N_{vw} = c^2 - r_1 r_2 s^2 (v \cdot w)$:
    - **Singular Isotropic Norm**: `norm Π_+ = 0` and `norm Π_- = 0`.
    - **Central Resolution of Identity**: `Π_+ + Π_- = N_vw • 1`.
    - **Vanishing Peirce Module Associators**:
      `zornAssociator Π_+ Π_- X = 0`, `zornAssociator Π_+ X Π_- = 0`, and `zornAssociator Π_+ Π_+ X = 0`. -/
theorem tiltedPeirce_norm_central_sum_and_associators
    (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    let P_plus := tiltedPeircePlus r₁ r₂ c s v w
    let P_minus := tiltedPeirceMinus r₁ r₂ c s v w
    let N_vw := c * c - r₁ * r₂ * (s * s) * ZornVec3.dot v w
    norm P_plus = 0 ∧
    norm P_minus = 0 ∧
    P_plus + P_minus = N_vw • (one : ZornVectorMatrix R) ∧
    zornAssociator P_plus P_minus X = 0 ∧
    zornAssociator P_plus X P_minus = 0 ∧
    zornAssociator P_plus P_plus X = 0 := by
  intro P_plus P_minus N_vw
  have h_sum : P_plus + P_minus = N_vw • (one : ZornVectorMatrix R) := by
    ext
    · simp [P_plus, P_minus, N_vw, one, tiltedPeircePlus, tiltedPeirceMinus,
            InfoGeometry.Algebra.zvm_add_def, add]; ring
    · rename_i i; fin_cases i <;>
        simp [P_plus, P_minus, one, tiltedPeircePlus, tiltedPeirceMinus,
              InfoGeometry.Algebra.zvm_add_def, add]
    · rename_i i; fin_cases i <;>
        simp [P_plus, P_minus, one, tiltedPeircePlus, tiltedPeirceMinus,
              InfoGeometry.Algebra.zvm_add_def, add]
    · simp [P_plus, P_minus, N_vw, one, tiltedPeircePlus, tiltedPeirceMinus,
            InfoGeometry.Algebra.zvm_add_def, add]; ring
  have h_minus : P_minus = N_vw • (one : ZornVectorMatrix R) + (-1 : R) • P_plus := by
    rw [← h_sum]
    ext
    · simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
    · rename_i i; fin_cases i <;>
        simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
    · rename_i i; fin_cases i <;>
        simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
    · simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
  refine ⟨?_, ?_, h_sum, ?_, ?_, ?_⟩
  · simp [P_plus, tiltedPeircePlus, norm, ZornVec3.dot, Fin.sum_univ_three]; ring
  · simp [P_minus, tiltedPeirceMinus, norm, ZornVec3.dot, Fin.sum_univ_three]; ring
  · change bundledAssociator P_plus P_minus X = 0
    rw [h_minus, bundledAssociator_add_mid, bundledAssociator_smul_mid,
        bundledAssociator_smul_mid, bundledAssociator_one_mid,
        bundledAssociator_left_alt, _root_.smul_zero, _root_.smul_zero, _root_.add_zero]
  · change bundledAssociator P_plus X P_minus = 0
    rw [h_minus, bundledAssociator_add_right, bundledAssociator_smul_right,
        bundledAssociator_smul_right, bundledAssociator_one_right,
        bundledAssociator_flexible, _root_.smul_zero, _root_.smul_zero, _root_.add_zero]
  · exact bundledAssociator_left_alt P_plus X

/-- **39. Left/Right Peirce Eigen-Action, Rank-1 Diagonal Corner Reduction, & Universal 4-Block Decomposition**:
    For ANY $r_1, r_2, c, s \in R$, $v, w \in R^3$, and arbitrary $X \in \mathrm{Zorn}(R)$:
    - **Left & Right Peirce Module Orthogonality & Idempotence**:
      `Π_+ * (Π_- * X) = 0`, `Π_+ * (Π_+ * X) = N_vw • (Π_+ * X)`,
      `(X * Π_+) * Π_- = 0`, and `(X * Π_+) * Π_+ = N_vw • (X * Π_+)`.
    - **Rank-1 Diagonal Peirce Corner Reduction & Trace Conservation**:
      `(Π_+ * X) * Π_+ = τ_+(X) • Π_+`, `(Π_- * X) * Π_- = τ_-(X) • Π_-`,
      and `τ_+(X) + τ_-(X) = N_vw * trace X`.
    - **Universal 4-Block Projective Peirce Decomposition**:
      `(Π_+ * X) * Π_+ + (Π_+ * X) * Π_- + (Π_- * X) * Π_+ + (Π_- * X) * Π_- = (N_vw * N_vw) • X`! -/
theorem tiltedPeirce_module_action_corner_reduction_and_four_block_decomposition
    (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    let P_plus := tiltedPeircePlus r₁ r₂ c s v w
    let P_minus := tiltedPeirceMinus r₁ r₂ c s v w
    let N_vw := c * c - r₁ * r₂ * (s * s) * ZornVec3.dot v w
    let τ_plus := zornPeirceCornerTracePlus r₁ r₂ c s v w X
    let τ_minus := zornPeirceCornerTraceMinus r₁ r₂ c s v w X
    P_plus * (P_minus * X) = 0 ∧
    P_plus * (P_plus * X) = N_vw • (P_plus * X) ∧
    (X * P_plus) * P_minus = 0 ∧
    (X * P_plus) * P_plus = N_vw • (X * P_plus) ∧
    (P_plus * X) * P_plus = τ_plus • P_plus ∧
    (P_minus * X) * P_minus = τ_minus • P_minus ∧
    τ_plus + τ_minus = N_vw * trace X ∧
    (P_plus * X) * P_plus + (P_plus * X) * P_minus +
      (P_minus * X) * P_plus + (P_minus * X) * P_minus =
      (N_vw * N_vw) • X := by
  intro P_plus P_minus N_vw τ_plus τ_minus
  have h33 := tiltedPeirce_orth_idem_chordal_and_syzygy r₁ r₂ c s v w
  have h38 := tiltedPeirce_norm_central_sum_and_associators r₁ r₂ c s v w X
  have h_orth : P_plus * P_minus = 0 := h33.1
  have h_idem : P_plus * P_plus = N_vw • P_plus := h33.2.1
  have h_sum : P_plus + P_minus = N_vw • (one : ZornVectorMatrix R) := h38.2.2.1
  have h_assoc_pm_x : (P_plus * P_minus) * X = P_plus * (P_minus * X) :=
    sub_eq_zero.mp h38.2.2.2.1
  have h_assoc_pp_x : (P_plus * P_plus) * X = P_plus * (P_plus * X) :=
    sub_eq_zero.mp h38.2.2.2.2.2
  have h_assoc_x_pp : (X * P_plus) * P_plus = X * (P_plus * P_plus) :=
    sub_eq_zero.mp (bundledAssociator_right_alt X P_plus)
  have h_minus : P_minus = N_vw • (one : ZornVectorMatrix R) + (-1 : R) • P_plus := by
    rw [← h_sum]
    ext
    · simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
    · rename_i i; fin_cases i <;>
        simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
    · rename_i i; fin_cases i <;>
        simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
    · simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
  have h_assoc_x_pm : (X * P_plus) * P_minus = X * (P_plus * P_minus) := by
    apply sub_eq_zero.mp
    change bundledAssociator X P_plus P_minus = 0
    rw [h_minus, bundledAssociator_add_right, bundledAssociator_smul_right,
        bundledAssociator_smul_right, bundledAssociator_one_right,
        bundledAssociator_right_alt, _root_.smul_zero, _root_.smul_zero, _root_.add_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h_assoc_pm_x, h_orth]
    exact zero_mul X
  · rw [← h_assoc_pp_x, h_idem]
    exact smul_mul N_vw P_plus X
  · rw [h_assoc_x_pm, h_orth]
    exact mul_zero X
  · rw [h_assoc_x_pp, h_idem]
    exact mul_smul N_vw X P_plus
  · ext
    · simp [P_plus, τ_plus, tiltedPeircePlus, zornPeirceCornerTracePlus,
            mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [P_plus, τ_plus, tiltedPeircePlus, zornPeirceCornerTracePlus,
               mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring)
    · rename_i i; fin_cases i <;>
        (simp [P_plus, τ_plus, tiltedPeircePlus, zornPeirceCornerTracePlus,
               mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring)
    · simp [P_plus, τ_plus, tiltedPeircePlus, zornPeirceCornerTracePlus,
            mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
  · ext
    · simp [P_minus, τ_minus, tiltedPeirceMinus, zornPeirceCornerTraceMinus,
            mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [P_minus, τ_minus, tiltedPeirceMinus, zornPeirceCornerTraceMinus,
               mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring)
    · rename_i i; fin_cases i <;>
        (simp [P_minus, τ_minus, tiltedPeirceMinus, zornPeirceCornerTraceMinus,
               mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring)
    · simp [P_minus, τ_minus, tiltedPeirceMinus, zornPeirceCornerTraceMinus,
            mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
  · simp [τ_plus, τ_minus, N_vw, zornPeirceCornerTracePlus, zornPeirceCornerTraceMinus, trace]
    ring
  · calc (P_plus * X) * P_plus + (P_plus * X) * P_minus +
           (P_minus * X) * P_plus + (P_minus * X) * P_minus
      _ = (P_plus * X) * (P_plus + P_minus) + (P_minus * X) * (P_plus + P_minus) := by
          rw [← _root_.mul_add, _root_.add_assoc, ← _root_.mul_add]
      _ = ((P_plus + P_minus) * X) * (P_plus + P_minus) := by
          rw [← _root_.add_mul, ← _root_.add_mul]
      _ = ((N_vw • (one : ZornVectorMatrix R)) * X) * (N_vw • (one : ZornVectorMatrix R)) := by
          rw [h_sum]
      _ = (N_vw * N_vw) • X := by
          change mul (mul (smul N_vw one) X) (smul N_vw one) = smul (N_vw * N_vw) X
          rw [ZornVectorMatrix.smul_mul, ZornVectorMatrix.one_mul,
              ZornVectorMatrix.mul_smul, ZornVectorMatrix.mul_one]
          change N_vw • (N_vw • X) = (N_vw * N_vw) • X
          rw [smul_smul]

/-- **40. Non-Associative Gauss–Bruhat Schur Complement Reconstruction & Frobenius–Schur Norm Factorization**:
    For ALL $w, v \in R^3$, $\lambda, \mu, b \in R$, and any unit $u \in R^\times$:
    - **Vanishing Bruhat Associator**: `zornAssociator (zornParabolicMinus w) (zornHyperbolicKernel lam mu) (zornParabolicPlus v) = 0`.
    - **Explicit Bruhat Coordinates**: `zornTrifactorFlow w lam mu v = ⟨lam, lam • v, lam • w, mu + lam * (w ⋅ v)⟩`.
    - **Unipotent Norm Invariance**: `norm (zornTrifactorFlow w lam mu v) = lam * mu`.
    - **Universal Schur Complement Reconstruction**:
      `zornTrifactorFlow (u⁻¹ • w) u (b - u⁻¹ * (w ⋅ v)) (u⁻¹ • v) = ⟨u, v, w, b⟩`.
    - **Frobenius–Schur Determinant/Norm Factorization**:
      `norm ⟨u, v, w, b⟩ = u * (b - u⁻¹ * (w ⋅ v))`! -/
theorem zornTrifactorFlow_frobenius_schur_norm_factorization
    (w v : ZornVec3 R) (lam mu b : R) (u : Rˣ) :
    zornAssociator (zornParabolicMinus w) (zornHyperbolicKernel lam mu) (zornParabolicPlus v) = 0 ∧
    zornTrifactorFlow w lam mu v =
      ⟨lam, fun i => lam * v i, fun i => lam * w i, mu + lam * ZornVec3.dot w v⟩ ∧
    norm (zornTrifactorFlow w lam mu v) = lam * mu ∧
    zornTrifactorFlow (fun i => (↑u⁻¹ : R) * w i) (u : R)
      (b - (↑u⁻¹ : R) * ZornVec3.dot w v) (fun i => (↑u⁻¹ : R) * v i) =
      ⟨(u : R), v, w, b⟩ ∧
    norm ⟨(u : R), v, w, b⟩ = (u : R) * (b - (↑u⁻¹ : R) * ZornVec3.dot w v) := by
  have h5 := zornTrifactorFlow_assoc_casimir_and_reconstruction w v lam mu b u
  refine ⟨h5.1, h5.2.1, h5.2.2.1, h5.2.2.2, ?_⟩
  have h_norm :=
    (zornTrifactorFlow_assoc_casimir_and_reconstruction
      (fun i => (↑u⁻¹ : R) * w i) (fun i => (↑u⁻¹ : R) * v i)
      (u : R) (b - (↑u⁻¹ : R) * ZornVec3.dot w v) b u).2.2.1
  rw [← h5.2.2.2, h_norm]

/-!
### Projective Peirce Quaternity Multiplication Table & Off-Diagonal Determinant-Norm Reconstruction
-/

/-- Upper-left projective Peirce block `X_{++} = (Π_+ * X) * Π_+`. -/
noncomputable def peirceBlockPP (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  (tiltedPeircePlus r₁ r₂ c s v w * X) * tiltedPeircePlus r₁ r₂ c s v w

/-- Upper-right off-diagonal projective Peirce root block `X_{+-} = (Π_+ * X) * Π_-`. -/
noncomputable def peirceBlockPM (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  (tiltedPeircePlus r₁ r₂ c s v w * X) * tiltedPeirceMinus r₁ r₂ c s v w

/-- Lower-left off-diagonal projective Peirce root block `X_{-+} = (Π_- * X) * Π_+`. -/
noncomputable def peirceBlockMP (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  (tiltedPeirceMinus r₁ r₂ c s v w * X) * tiltedPeircePlus r₁ r₂ c s v w

/-- Lower-right projective Peirce block `X_{--} = (Π_- * X) * Π_-`. -/
noncomputable def peirceBlockMM (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  (tiltedPeirceMinus r₁ r₂ c s v w * X) * tiltedPeirceMinus r₁ r₂ c s v w

private lemma zvm_smul_mul (r : R) (A B : ZornVectorMatrix R) :
    (r • A) * B = r • (A * B) := ZornVectorMatrix.smul_mul r A B

private lemma zvm_mul_smul (r : R) (A B : ZornVectorMatrix R) :
    A * (r • B) = r • (A * B) := ZornVectorMatrix.mul_smul r A B

private lemma zvm_one_mul (A : ZornVectorMatrix R) :
    (one : ZornVectorMatrix R) * A = A := ZornVectorMatrix.one_mul A

private lemma zvm_mul_one (A : ZornVectorMatrix R) :
    A * (one : ZornVectorMatrix R) = A := ZornVectorMatrix.mul_one A

private lemma peirce_offDiag_product_of_idem
    (P : ZornVectorMatrix R) (N_vw τ_P τ_Q : R) (X : ZornVectorMatrix R)
    (h_idem : P * P = N_vw • P)
    (h_corner : (P * X) * P = τ_P • P)
    (h_tr : τ_P + τ_Q = N_vw * trace X) :
    (N_vw • (P * X) - τ_P • P) * (N_vw • (X * P) - τ_P • P) =
      (N_vw * τ_P * τ_Q - (N_vw ^ 3) * norm X) • P := by
  have h_flex : P * (X * P) = (P * X) * P :=
    (sub_eq_zero.mp (bundledAssociator_flexible P X)).symm
  have h_corner' : P * (X * P) = τ_P • P := h_flex.trans h_corner
  have h_ch : X * X = trace X • X - norm X • (one : ZornVectorMatrix R) := by
    rw [← sub_eq_zero, ← sub_add]
    exact (zorn_involution_cayley_hamilton_and_antiautomorphism X 0).2.2.2.1
  have h_quad : (P * X) * (X * P) = (trace X * τ_P - norm X * N_vw) • P := by
    calc (P * X) * (X * P)
      _ = P * ((X * X) * P) := middle_moufang P X X
      _ = (P * (X * X)) * P := (sub_eq_zero.mp (bundledAssociator_flexible P (X * X))).symm
      _ = (P * (trace X • X - norm X • (one : ZornVectorMatrix R))) * P := by rw [h_ch]
      _ = (P * (trace X • X)) * P - (P * (norm X • (one : ZornVectorMatrix R))) * P := by
          rw [_root_.mul_sub, _root_.sub_mul]
      _ = (trace X * τ_P - norm X * N_vw) • P := by
          simp only [zvm_mul_smul, zvm_smul_mul, zvm_mul_one, h_corner, h_idem, smul_smul, ← sub_smul]
  simp only [_root_.sub_mul, _root_.mul_sub, zvm_smul_mul, zvm_mul_smul,
             h_quad, h_corner, h_corner', h_idem, smul_smul, ← sub_smul]
  congr 1
  linear_combination (N_vw * τ_P) * h_tr.symm

/-- **41. Isotropic Nilpotence & Bimodule Eigen-Absorption of Off-Diagonal Peirce Roots**:
    For ANY $r_1, r_2, c, s \in R$, $v, w \in R^3$, and arbitrary $X \in \mathrm{Zorn}(R)$, let
    $X_{+-} = (\Pi_+ * X) * \Pi_-$ and $X_{-+} = (\Pi_- * X) * \Pi_+$ with $N_{vw} = c^2 - r_1 r_2 s^2 (v \cdot w)$:
    - **Vanishing Trace & Composition Norm**:
      `trace X_{+-} = 0`, `trace X_{-+} = 0`, `norm X_{+-} = 0`, and `norm X_{-+} = 0`.
    - **Square-Zero Isotropic Nilpotence**:
      `X_{+-} * X_{+-} = 0` and `X_{-+} * X_{-+} = 0`.
    - **Left/Right Bimodule Eigen-Absorption & Cross-Annihilation**:
      `Π_+ * X_{+-} = N_vw • X_{+-}`, `X_{+-} * Π_- = N_vw • X_{+-}`,
      `Π_- * X_{+-} = 0`, and `X_{+-} * Π_+ = 0`. -/
theorem peirceBlock_offDiag_nilpotence_and_absorption
    (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    let P_plus := tiltedPeircePlus r₁ r₂ c s v w
    let P_minus := tiltedPeirceMinus r₁ r₂ c s v w
    let X_pm := peirceBlockPM r₁ r₂ c s v w X
    let X_mp := peirceBlockMP r₁ r₂ c s v w X
    let N_vw := c * c - r₁ * r₂ * (s * s) * ZornVec3.dot v w
    trace X_pm = 0 ∧
    trace X_mp = 0 ∧
    norm X_pm = 0 ∧
    norm X_mp = 0 ∧
    X_pm * X_pm = 0 ∧
    X_mp * X_mp = 0 ∧
    P_plus * X_pm = N_vw • X_pm ∧
    X_pm * P_minus = N_vw • X_pm ∧
    P_minus * X_pm = 0 ∧
    X_pm * P_plus = 0 := by
  intro P_plus P_minus X_pm X_mp N_vw
  let τ_plus := zornPeirceCornerTracePlus r₁ r₂ c s v w X
  have h33 := tiltedPeirce_orth_idem_chordal_and_syzygy r₁ r₂ c s v w
  have h38 := tiltedPeirce_norm_central_sum_and_associators r₁ r₂ c s v w X
  have h39 := tiltedPeirce_module_action_corner_reduction_and_four_block_decomposition r₁ r₂ c s v w X
  have h_idem : P_plus * P_plus = N_vw • P_plus := h33.2.1
  have h_sum : P_plus + P_minus = N_vw • (one : ZornVectorMatrix R) := h38.2.2.1
  have h_corner_plus : (P_plus * X) * P_plus = τ_plus • P_plus := h39.2.2.2.2.1
  have h_pm_plus : X_pm = N_vw • (P_plus * X) - τ_plus • P_plus := by
    apply eq_sub_of_add_eq'
    calc τ_plus • P_plus + X_pm
      _ = (P_plus * X) * P_plus + (P_plus * X) * P_minus := by rw [← h_corner_plus]; rfl
      _ = (P_plus * X) * (P_plus + P_minus) := by rw [← _root_.mul_add]
      _ = N_vw • (P_plus * X) := by rw [h_sum, zvm_mul_smul, zvm_mul_one]
  have h_tr_pm : trace X_pm = 0 := by
    simp [X_pm, peirceBlockPM, tiltedPeircePlus, tiltedPeirceMinus,
          trace, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  have h_tr_mp : trace X_mp = 0 := by
    simp [X_mp, peirceBlockMP, tiltedPeircePlus, tiltedPeirceMinus,
          trace, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  have h_norm_pm : norm X_pm = 0 := by
    change norm (mul (P_plus * X) P_minus) = 0
    rw [norm_mul, h38.2.1, MulZeroClass.mul_zero]
  have h_norm_mp : norm X_mp = 0 := by
    change norm (mul (P_minus * X) P_plus) = 0
    rw [norm_mul, h38.1, MulZeroClass.mul_zero]
  have h_sq_pm : X_pm * X_pm = 0 := by
    have hch := (zorn_involution_cayley_hamilton_and_antiautomorphism X_pm 0).2.2.2.1
    rw [h_tr_pm, h_norm_pm, _root_.zero_smul, _root_.zero_smul, _root_.sub_zero, _root_.add_zero] at hch
    exact hch
  have h_sq_mp : X_mp * X_mp = 0 := by
    have hch := (zorn_involution_cayley_hamilton_and_antiautomorphism X_mp 0).2.2.2.1
    rw [h_tr_mp, h_norm_mp, _root_.zero_smul, _root_.zero_smul, _root_.sub_zero, _root_.add_zero] at hch
    exact hch
  have h_abs_left : P_plus * X_pm = N_vw • X_pm := by
    rw [h_pm_plus, _root_.mul_sub, zvm_mul_smul, zvm_mul_smul,
        h39.2.1, h_idem, smul_sub, smul_comm τ_plus N_vw P_plus]
  have h_ann_right : X_pm * P_plus = 0 := by
    rw [h_pm_plus, _root_.sub_mul, zvm_smul_mul, zvm_smul_mul,
        h_corner_plus, h_idem, smul_smul, smul_smul, mul_comm τ_plus N_vw, _root_.sub_self]
  have h_abs_right : X_pm * P_minus = N_vw • X_pm := by
    calc X_pm * P_minus
      _ = 0 + X_pm * P_minus := (_root_.zero_add _).symm
      _ = X_pm * P_plus + X_pm * P_minus := by rw [h_ann_right]
      _ = X_pm * (P_plus + P_minus) := by rw [← _root_.mul_add]
      _ = N_vw • X_pm := by rw [h_sum, zvm_mul_smul, zvm_mul_one]
  have h_ann_left : P_minus * X_pm = 0 := by
    have h1 : P_plus * X_pm + P_minus * X_pm = N_vw • X_pm := by
      calc P_plus * X_pm + P_minus * X_pm
        _ = (P_plus + P_minus) * X_pm := by rw [← _root_.add_mul]
        _ = N_vw • X_pm := by rw [h_sum, zvm_smul_mul, zvm_one_mul]
    rw [h_abs_left] at h1
    calc P_minus * X_pm
      _ = (N_vw • X_pm + P_minus * X_pm) - N_vw • X_pm := (add_sub_cancel_left _ _).symm
      _ = N_vw • X_pm - N_vw • X_pm := by rw [h1]
      _ = 0 := _root_.sub_self _
  exact ⟨h_tr_pm, h_tr_mp, h_norm_pm, h_norm_mp, h_sq_pm, h_sq_mp,
         h_abs_left, h_abs_right, h_ann_left, h_ann_right⟩

/-- **42. Off-Diagonal Peirce Root Coupling & Universal Peirce Determinant-Norm Reconstruction**:
    For ANY $r_1, r_2, c, s \in R$, $v, w \in R^3$, and arbitrary $X \in \mathrm{Zorn}(R)$:
    - **Upper Off-Diagonal Root Product**:
      `X_{+-} * X_{-+} = (N_vw * τ_+(X) * τ_-(X) - N_vw^3 * norm X) • Π_+`.
    - **Lower Off-Diagonal Root Product**:
      `X_{-+} * X_{+-} = (N_vw * τ_+(X) * τ_-(X) - N_vw^3 * norm X) • Π_-`.
    - **Symmetrized Off-Diagonal Jordan Product (Peirce Determinant Law)**:
      `X_{+-} * X_{-+} + X_{-+} * X_{+-} = (N_vw * N_vw * (τ_+(X) * τ_-(X) - N_vw * N_vw * norm X)) • 1`! -/
theorem peirceBlock_offDiag_coupling_and_determinant_law
    (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    let P_plus := tiltedPeircePlus r₁ r₂ c s v w
    let P_minus := tiltedPeirceMinus r₁ r₂ c s v w
    let X_pm := peirceBlockPM r₁ r₂ c s v w X
    let X_mp := peirceBlockMP r₁ r₂ c s v w X
    let τ_plus := zornPeirceCornerTracePlus r₁ r₂ c s v w X
    let τ_minus := zornPeirceCornerTraceMinus r₁ r₂ c s v w X
    let N_vw := c * c - r₁ * r₂ * (s * s) * ZornVec3.dot v w
    X_pm * X_mp = (N_vw * τ_plus * τ_minus - (N_vw ^ 3) * norm X) • P_plus ∧
    X_mp * X_pm = (N_vw * τ_plus * τ_minus - (N_vw ^ 3) * norm X) • P_minus ∧
    X_pm * X_mp + X_mp * X_pm =
      (N_vw * N_vw * (τ_plus * τ_minus - N_vw * N_vw * norm X)) • (one : ZornVectorMatrix R) := by
  intro P_plus P_minus X_pm X_mp τ_plus τ_minus N_vw
  have h33 := tiltedPeirce_orth_idem_chordal_and_syzygy r₁ r₂ c s v w
  have h38 := tiltedPeirce_norm_central_sum_and_associators r₁ r₂ c s v w X
  have h39 := tiltedPeirce_module_action_corner_reduction_and_four_block_decomposition r₁ r₂ c s v w X
  have h_idem_plus : P_plus * P_plus = N_vw • P_plus := h33.2.1
  have h_sum : P_plus + P_minus = N_vw • (one : ZornVectorMatrix R) := h38.2.2.1
  have h_corner_plus : (P_plus * X) * P_plus = τ_plus • P_plus := h39.2.2.2.2.1
  have h_corner_minus : (P_minus * X) * P_minus = τ_minus • P_minus := h39.2.2.2.2.2.1
  have h_tr : τ_plus + τ_minus = N_vw * trace X := h39.2.2.2.2.2.2.1
  have h_tr_symm : τ_minus + τ_plus = N_vw * trace X := (_root_.add_comm τ_minus τ_plus).trans h_tr
  have h_orth_mp : P_minus * P_plus = 0 := by
    have h1 : P_plus * P_plus + P_minus * P_plus = N_vw • P_plus := by
      calc P_plus * P_plus + P_minus * P_plus
        _ = (P_plus + P_minus) * P_plus := by rw [← _root_.add_mul]
        _ = N_vw • P_plus := by rw [h_sum, zvm_smul_mul, zvm_one_mul]
    rw [h_idem_plus] at h1
    calc P_minus * P_plus
      _ = (N_vw • P_plus + P_minus * P_plus) - N_vw • P_plus := (add_sub_cancel_left _ _).symm
      _ = N_vw • P_plus - N_vw • P_plus := by rw [h1]
      _ = 0 := _root_.sub_self _
  have h_idem_minus : P_minus * P_minus = N_vw • P_minus := by
    calc P_minus * P_minus
      _ = 0 + P_minus * P_minus := (_root_.zero_add _).symm
      _ = P_minus * P_plus + P_minus * P_minus := by rw [h_orth_mp]
      _ = P_minus * (P_plus + P_minus) := by rw [← _root_.mul_add]
      _ = N_vw • P_minus := by rw [h_sum, zvm_mul_smul, zvm_mul_one]
  have h_pm_plus : X_pm = N_vw • (P_plus * X) - τ_plus • P_plus := by
    apply eq_sub_of_add_eq'
    calc τ_plus • P_plus + X_pm
      _ = (P_plus * X) * P_plus + (P_plus * X) * P_minus := by rw [← h_corner_plus]; rfl
      _ = (P_plus * X) * (P_plus + P_minus) := by rw [← _root_.mul_add]
      _ = N_vw • (P_plus * X) := by rw [h_sum, zvm_mul_smul, zvm_mul_one]
  have h_mp_plus : X_mp = N_vw • (X * P_plus) - τ_plus • P_plus := by
    apply eq_sub_of_add_eq'
    calc τ_plus • P_plus + X_mp
      _ = (P_plus * X) * P_plus + (P_minus * X) * P_plus := by rw [← h_corner_plus]; rfl
      _ = ((P_plus + P_minus) * X) * P_plus := by rw [← _root_.add_mul, ← _root_.add_mul]
      _ = N_vw • (X * P_plus) := by rw [h_sum, zvm_smul_mul, zvm_one_mul, zvm_smul_mul]
  have h_mp_minus : X_mp = N_vw • (P_minus * X) - τ_minus • P_minus := by
    apply eq_sub_of_add_eq
    calc X_mp + τ_minus • P_minus
      _ = (P_minus * X) * P_plus + (P_minus * X) * P_minus := by rw [← h_corner_minus]; rfl
      _ = (P_minus * X) * (P_plus + P_minus) := by rw [← _root_.mul_add]
      _ = N_vw • (P_minus * X) := by rw [h_sum, zvm_mul_smul, zvm_mul_one]
  have h_pm_minus : X_pm = N_vw • (X * P_minus) - τ_minus • P_minus := by
    apply eq_sub_of_add_eq
    calc X_pm + τ_minus • P_minus
      _ = (P_plus * X) * P_minus + (P_minus * X) * P_minus := by rw [← h_corner_minus]; rfl
      _ = ((P_plus + P_minus) * X) * P_minus := by rw [← _root_.add_mul, ← _root_.add_mul]
      _ = N_vw • (X * P_minus) := by rw [h_sum, zvm_smul_mul, zvm_one_mul, zvm_smul_mul]
  have h_pm : X_pm * X_mp = (N_vw * τ_plus * τ_minus - (N_vw ^ 3) * norm X) • P_plus := by
    rw [h_pm_plus, h_mp_plus]
    exact peirce_offDiag_product_of_idem P_plus N_vw τ_plus τ_minus X h_idem_plus h_corner_plus h_tr
  have h_mp : X_mp * X_pm = (N_vw * τ_plus * τ_minus - (N_vw ^ 3) * norm X) • P_minus := by
    rw [h_mp_minus, h_pm_minus]
    have h_raw := peirce_offDiag_product_of_idem P_minus N_vw τ_minus τ_plus X
      h_idem_minus h_corner_minus h_tr_symm
    rw [show N_vw * τ_minus * τ_plus = N_vw * τ_plus * τ_minus by ring] at h_raw
    exact h_raw
  refine ⟨h_pm, h_mp, ?_⟩
  rw [h_pm, h_mp, ← _root_.smul_add, h_sum, smul_smul]
  congr 1
  ring

/-!
### Multi-Archetype Bargmann Transition Fidelity & Diagonal Peirce Spectral Annihilation
-/

/-- **Symmetric Bargmann Transition Fidelity Scalar `σ(Π₁, Π₂) = trace (Π₁ * Π₂)`**
    measuring the oblique overlap between two arbitrary projective Peirce idempotents `Π₁` and `Π₂`. -/
def bargmannFidelity (r₁ r₂ c₁ s₁ : R) (v₁ w₁ : ZornVec3 R)
    (r'₁ r'₂ c₂ s₂ : R) (v₂ w₂ : ZornVec3 R) : R :=
  (c₁ * c₁) * (c₂ * c₂) -
    (r₁ * c₁ * s₁) * (r'₂ * c₂ * s₂) * ZornVec3.dot v₁ w₂ -
    (r₂ * c₁ * s₁) * (r'₁ * c₂ * s₂) * ZornVec3.dot v₂ w₁ +
    (r₁ * r₂ * (s₁ * s₁) * ZornVec3.dot v₁ w₁) * (r'₁ * r'₂ * (s₂ * s₂) * ZornVec3.dot v₂ w₂)

/-- **43. Universal Two-Idempotent Bargmann Sandwich Law & Transition Fidelity**:
    For ANY two projective Peirce idempotents $\Pi_1 = \Pi_+(r_1, r_2, c_1, s_1, v_1, w_1)$ and
    $\Pi_2 = \Pi_+(r'_1, r'_2, c_2, s_2, v_2, w_2)$ in $\mathrm{Zorn}(R)$:
    - **Trace Symmetry of the Bargmann Fidelity**:
      `trace (Π₁ * Π₂) = σ(Π₁, Π₂)` and `trace (Π₂ * Π₁) = σ(Π₁, Π₂)`.
    - **Flexible Sandwich Associativity**:
      `(Π₁ * Π₂) * Π₁ = Π₁ * (Π₂ * Π₁)`.
    - **Exact Rank-1 Bargmann Sandwich Reduction**:
      `(Π₁ * Π₂) * Π₁ = σ(Π₁, Π₂) • Π₁` and `(Π₂ * Π₁) * Π₂ = σ(Π₁, Π₂) • Π₂`.
    - **Singular Isotropic Norm of the Transition Product**:
      `norm (Π₁ * Π₂) = 0`. -/
theorem twoArchetype_bargmann_sandwich_and_fidelity
    (r₁ r₂ c₁ s₁ r'₁ r'₂ c₂ s₂ : R) (v₁ w₁ v₂ w₂ : ZornVec3 R) :
    let P₁ := tiltedPeircePlus r₁ r₂ c₁ s₁ v₁ w₁
    let P₂ := tiltedPeircePlus r'₁ r'₂ c₂ s₂ v₂ w₂
    let σ := bargmannFidelity r₁ r₂ c₁ s₁ v₁ w₁ r'₁ r'₂ c₂ s₂ v₂ w₂
    trace (P₁ * P₂) = σ ∧
    trace (P₂ * P₁) = σ ∧
    (P₁ * P₂) * P₁ = P₁ * (P₂ * P₁) ∧
    (P₁ * P₂) * P₁ = σ • P₁ ∧
    (P₂ * P₁) * P₂ = σ • P₂ ∧
    norm (P₁ * P₂) = 0 := by
  intro P₁ P₂ σ
  have h_corner12 : (P₁ * P₂) * P₁ = zornPeirceCornerTracePlus r₁ r₂ c₁ s₁ v₁ w₁ P₂ • P₁ :=
    (tiltedPeirce_module_action_corner_reduction_and_four_block_decomposition
      r₁ r₂ c₁ s₁ v₁ w₁ P₂).2.2.2.2.1
  have h_corner21 : (P₂ * P₁) * P₂ = zornPeirceCornerTracePlus r'₁ r'₂ c₂ s₂ v₂ w₂ P₁ • P₂ :=
    (tiltedPeirce_module_action_corner_reduction_and_four_block_decomposition
      r'₁ r'₂ c₂ s₂ v₂ w₂ P₁).2.2.2.2.1
  have h_σ12 : zornPeirceCornerTracePlus r₁ r₂ c₁ s₁ v₁ w₁ P₂ = σ := by
    simp [P₂, σ, tiltedPeircePlus, zornPeirceCornerTracePlus, bargmannFidelity,
          ZornVec3.dot, Fin.sum_univ_three]
    ring
  have h_σ21 : zornPeirceCornerTracePlus r'₁ r'₂ c₂ s₂ v₂ w₂ P₁ = σ := by
    simp [P₁, σ, tiltedPeircePlus, zornPeirceCornerTracePlus, bargmannFidelity,
          ZornVec3.dot, Fin.sum_univ_three]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [P₁, P₂, σ, tiltedPeircePlus, bargmannFidelity, trace,
          mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · simp [P₁, P₂, σ, tiltedPeircePlus, bargmannFidelity, trace,
          mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · exact sub_eq_zero.mp (bundledAssociator_flexible P₁ P₂)
  · rw [h_corner12, h_σ12]
  · rw [h_corner21, h_σ21]
  · change norm (mul P₁ P₂) = 0
    rw [norm_mul, (tiltedPeirce_norm_central_sum_and_associators r₁ r₂ c₁ s₁ v₁ w₁ 0).1,
        MulZeroClass.zero_mul]

/-- **44. Spectral Minimal Polynomial Annihilation of the Diagonal Peirce Operator**:
    For ANY $r_1, r_2, c, s \in R$, $v, w \in R^3$, and arbitrary $X \in \mathrm{Zorn}(R)$, let
    $D_\Pi(X) = \tau_+(X) \bullet \Pi_+ + \tau_-(X) \bullet \Pi_-$ be the extracted diagonal Peirce operator of $X$:
    - **Eigen-Projection on $\Pi_\pm$**:
      `D_Π(X) * Π_+ = (τ_+(X) * N_vw) • Π_+` and `D_Π(X) * Π_- = (τ_-(X) * N_vw) • Π_-`.
    - **Exact Factorized Cayley–Hamilton Spectral Annihilation**:
      `(D_Π(X) - (τ_+(X) * N_vw) • 1) * (D_Π(X) - (τ_-(X) * N_vw) • 1) = 0`.
    - **Composition Norm of the Diagonal Peirce Operator**:
      `norm (D_Π(X)) = (N_vw * N_vw) * τ_+(X) * τ_-(X)`! -/
theorem peirceDiagonalOperator_eigen_and_spectral_annihilation
    (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    let P_plus := tiltedPeircePlus r₁ r₂ c s v w
    let P_minus := tiltedPeirceMinus r₁ r₂ c s v w
    let N_vw := c * c - r₁ * r₂ * (s * s) * ZornVec3.dot v w
    let τ_plus := zornPeirceCornerTracePlus r₁ r₂ c s v w X
    let τ_minus := zornPeirceCornerTraceMinus r₁ r₂ c s v w X
    let D_X := τ_plus • P_plus + τ_minus • P_minus
    D_X * P_plus = (τ_plus * N_vw) • P_plus ∧
    D_X * P_minus = (τ_minus * N_vw) • P_minus ∧
    (D_X - (τ_plus * N_vw) • (one : ZornVectorMatrix R)) *
      (D_X - (τ_minus * N_vw) • (one : ZornVectorMatrix R)) = 0 ∧
    norm D_X = (N_vw * N_vw) * τ_plus * τ_minus := by
  intro P_plus P_minus N_vw τ_plus τ_minus D_X
  have h33 := tiltedPeirce_orth_idem_chordal_and_syzygy r₁ r₂ c s v w
  have h38 := tiltedPeirce_norm_central_sum_and_associators r₁ r₂ c s v w X
  have h_orth_pm : P_plus * P_minus = 0 := h33.1
  have h_idem_plus : P_plus * P_plus = N_vw • P_plus := h33.2.1
  have h_sum : P_plus + P_minus = N_vw • (one : ZornVectorMatrix R) := h38.2.2.1
  have h_orth_mp : P_minus * P_plus = 0 := by
    have h1 : P_plus * P_plus + P_minus * P_plus = N_vw • P_plus := by
      calc P_plus * P_plus + P_minus * P_plus
        _ = (P_plus + P_minus) * P_plus := by rw [← _root_.add_mul]
        _ = N_vw • P_plus := by rw [h_sum, zvm_smul_mul, zvm_one_mul]
    rw [h_idem_plus] at h1
    calc P_minus * P_plus
      _ = (N_vw • P_plus + P_minus * P_plus) - N_vw • P_plus := (add_sub_cancel_left _ _).symm
      _ = N_vw • P_plus - N_vw • P_plus := by rw [h1]
      _ = 0 := _root_.sub_self _
  have h_idem_minus : P_minus * P_minus = N_vw • P_minus := by
    calc P_minus * P_minus
      _ = 0 + P_minus * P_minus := (_root_.zero_add _).symm
      _ = P_minus * P_plus + P_minus * P_minus := by rw [h_orth_mp]
      _ = P_minus * (P_plus + P_minus) := by rw [← _root_.mul_add]
      _ = N_vw • P_minus := by rw [h_sum, zvm_mul_smul, zvm_mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (τ_plus • P_plus + τ_minus • P_minus) * P_plus = (τ_plus * N_vw) • P_plus
    rw [_root_.add_mul, zvm_smul_mul, zvm_smul_mul, h_idem_plus, h_orth_mp,
        smul_smul, _root_.smul_zero, _root_.add_zero]
  · change (τ_plus • P_plus + τ_minus • P_minus) * P_minus = (τ_minus * N_vw) • P_minus
    rw [_root_.add_mul, zvm_smul_mul, zvm_smul_mul, h_orth_pm, h_idem_minus,
        smul_smul, _root_.smul_zero, _root_.zero_add]
  · have h_shift_plus :
        D_X - (τ_plus * N_vw) • (one : ZornVectorMatrix R) = (τ_minus - τ_plus) • P_minus := by
      change (τ_plus • P_plus + τ_minus • P_minus) - (τ_plus * N_vw) • (one : ZornVectorMatrix R) =
        (τ_minus - τ_plus) • P_minus
      rw [← smul_smul, ← h_sum, _root_.smul_add, sub_smul]
      abel
    have h_shift_minus :
        D_X - (τ_minus * N_vw) • (one : ZornVectorMatrix R) = (τ_plus - τ_minus) • P_plus := by
      change (τ_plus • P_plus + τ_minus • P_minus) - (τ_minus * N_vw) • (one : ZornVectorMatrix R) =
        (τ_plus - τ_minus) • P_plus
      rw [← smul_smul, ← h_sum, _root_.smul_add, sub_smul]
      abel
    rw [h_shift_plus, h_shift_minus, zvm_smul_mul, zvm_mul_smul, h_orth_mp,
        _root_.smul_zero, _root_.smul_zero]
  · simp [D_X, P_plus, P_minus, N_vw, tiltedPeircePlus, tiltedPeirceMinus,
          norm, InfoGeometry.Algebra.zvm_add_def, add, ZornVec3.dot, Fin.sum_univ_three]
    ring

/-- **45. Unconditional 8D Transition Projective Idempotence & Multi-Archetype Commutator Clifford Law**:
    Because every element of $\mathrm{Zorn}(R)$ is quadratic over $R$ and the composition norm is
    multiplicative (`norm (Π₁ * Π₂) = 0`), the product $P_{12} = \Pi_1 * \Pi_2$ of ANY two tilted
    projective Peirce idempotents $\Pi_1, \Pi_2 \in \mathrm{Zorn}(R)$ is itself a projective idempotent
    across the **entire 8D non-associative algebra** (requiring no coplanarity hypothesis!):
    - **Unconditional 8D Transition Idempotence**:
      `(Π₁ * Π₂) * (Π₁ * Π₂) = σ(Π₁, Π₂) • (Π₁ * Π₂)` and
      `(Π₂ * Π₁) * (Π₂ * Π₁) = σ(Π₁, Π₂) • (Π₂ * Π₁)`.
    - **Traceless 7D Malcev Commutator**:
      `trace (Π₁ * Π₂ - Π₂ * Π₁) = 0` and `(Π₁ * Π₂ - Π₂ * Π₁) + conj (Π₁ * Π₂ - Π₂ * Π₁) = 0`.
    - **Multi-Archetype Commutator Clifford Square**:
      `(Π₁ * Π₂ - Π₂ * Π₁) * (Π₁ * Π₂ - Π₂ * Π₁) = (-norm (Π₁ * Π₂ - Π₂ * Π₁)) • 1`! -/
theorem twoArchetype_transition_idempotence_and_commutator_clifford
    (r₁ r₂ c₁ s₁ r'₁ r'₂ c₂ s₂ : R) (v₁ w₁ v₂ w₂ : ZornVec3 R) :
    let P₁ := tiltedPeircePlus r₁ r₂ c₁ s₁ v₁ w₁
    let P₂ := tiltedPeircePlus r'₁ r'₂ c₂ s₂ v₂ w₂
    let σ := bargmannFidelity r₁ r₂ c₁ s₁ v₁ w₁ r'₁ r'₂ c₂ s₂ v₂ w₂
    let C₁₂ := P₁ * P₂ - P₂ * P₁
    (P₁ * P₂) * (P₁ * P₂) = σ • (P₁ * P₂) ∧
    (P₂ * P₁) * (P₂ * P₁) = σ • (P₂ * P₁) ∧
    trace C₁₂ = 0 ∧
    C₁₂ + conj C₁₂ = 0 ∧
    C₁₂ * C₁₂ = (-norm C₁₂) • (one : ZornVectorMatrix R) := by
  intro P₁ P₂ σ C₁₂
  have h43 := twoArchetype_bargmann_sandwich_and_fidelity r₁ r₂ c₁ s₁ r'₁ r'₂ c₂ s₂ v₁ w₁ v₂ w₂
  have h_tr12 : trace (P₁ * P₂) = σ := h43.1
  have h_tr21 : trace (P₂ * P₁) = σ := h43.2.1
  have h_norm12 : norm (P₁ * P₂) = 0 := h43.2.2.2.2.2
  have h_norm21 : norm (P₂ * P₁) = 0 := by
    change norm (mul P₂ P₁) = 0
    rw [norm_mul, (tiltedPeirce_norm_central_sum_and_associators r'₁ r'₂ c₂ s₂ v₂ w₂ 0).1,
        MulZeroClass.zero_mul]
  have h_tr_comm : trace C₁₂ = 0 := by
    have h_sub : trace C₁₂ = trace (P₁ * P₂) - trace (P₂ * P₁) := by
      simp [C₁₂, _root_.sub_eq_add_neg, trace, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, add, neg]
      ring
    rw [h_sub, h_tr12, h_tr21, _root_.sub_self]
  refine ⟨?_, ?_, h_tr_comm, ?_, ?_⟩
  · apply sub_eq_zero.mp
    have hch := (zorn_involution_cayley_hamilton_and_antiautomorphism (P₁ * P₂) 0).2.2.2.1
    rw [h_tr12, h_norm12, _root_.zero_smul, _root_.add_zero] at hch
    exact hch
  · apply sub_eq_zero.mp
    have hch := (zorn_involution_cayley_hamilton_and_antiautomorphism (P₂ * P₁) 0).2.2.2.1
    rw [h_tr21, h_norm21, _root_.zero_smul, _root_.add_zero] at hch
    exact hch
  · have h_inv := (zorn_involution_cayley_hamilton_and_antiautomorphism C₁₂ 0).1
    rw [h_tr_comm, _root_.zero_smul] at h_inv
    exact h_inv
  · have hch := (zorn_involution_cayley_hamilton_and_antiautomorphism C₁₂ 0).2.2.2.1
    rw [h_tr_comm, _root_.zero_smul, _root_.sub_zero] at hch
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hch

/-!
### Non-Associative Core-Nilpotent Drazin Splitting, Moore–Penrose Generalized Inverse, & Rank-1 Trifactor Law
-/

/-- Upper Peirce core-nilpotent operator `T(X) = X_{++} + X_{+-} = (Π_+ * X) * Π_+ + (Π_+ * X) * Π_-`. -/
noncomputable def peirceCoreNilpotentOp (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  peirceBlockPP r₁ r₂ c s v w X + peirceBlockPM r₁ r₂ c s v w X

/-- **46. Non-Associative Core-Nilpotent Jordan Splitting & Polynomial Drazin Generalized Inverse**:
    For ANY $r_1, r_2, c, s \in R$, $v, w \in R^3$, and arbitrary $X \in \mathrm{Zorn}(R)$, let
    $C = X_{++} = \tau_+(X) \bullet \Pi_+$ be the core part, $N = X_{+-} = (\Pi_+ * X) * \Pi_-$ be
    the nilpotent part, and $T = C + N$ be the upper Peirce operator, with spectral multiplier
    $\lambda = \tau_+(X) * N_{vw}$:
    - **Core-Nilpotent Semidirect Relations**:
      `N * N = 0`, `C * N = lam • N`, and `N * C = 0`.
    - **Singular Norm of `T`**: `norm T = 0`.
    - **Projective Core Idempotence**: `T * T = lam • T`.
    - **Polynomial Drazin Generalized Inverse Equations (with $T^D = T$)**:
      `(T * T) * T = (lam * lam) • T` and `T * (T * T) = (lam * lam) • T`! -/
theorem peirceCoreNilpotent_drazin_splitting
    (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    let N_vw := c * c - r₁ * r₂ * (s * s) * ZornVec3.dot v w
    let τ_plus := zornPeirceCornerTracePlus r₁ r₂ c s v w X
    let lam := τ_plus * N_vw
    let C := peirceBlockPP r₁ r₂ c s v w X
    let N := peirceBlockPM r₁ r₂ c s v w X
    let T := peirceCoreNilpotentOp r₁ r₂ c s v w X
    N * N = 0 ∧
    C * N = lam • N ∧
    N * C = 0 ∧
    norm T = 0 ∧
    T * T = lam • T ∧
    (T * T) * T = (lam * lam) • T ∧
    T * (T * T) = (lam * lam) • T := by
  intro N_vw τ_plus lam C N T
  let P_plus := tiltedPeircePlus r₁ r₂ c s v w
  let P_minus := tiltedPeirceMinus r₁ r₂ c s v w
  have h33 := tiltedPeirce_orth_idem_chordal_and_syzygy r₁ r₂ c s v w
  have h38 := tiltedPeirce_norm_central_sum_and_associators r₁ r₂ c s v w X
  have h39 := tiltedPeirce_module_action_corner_reduction_and_four_block_decomposition r₁ r₂ c s v w X
  have h41 := peirceBlock_offDiag_nilpotence_and_absorption r₁ r₂ c s v w X
  have h_idem : P_plus * P_plus = N_vw • P_plus := h33.2.1
  have h_sum : P_plus + P_minus = N_vw • (one : ZornVectorMatrix R) := h38.2.2.1
  have h_C : C = τ_plus • P_plus := h39.2.2.2.2.1
  have h_N_sq : N * N = 0 := h41.2.2.2.2.1
  have h_P_N : P_plus * N = N_vw • N := h41.2.2.2.2.2.2.1
  have h_N_P : N * P_plus = 0 := h41.2.2.2.2.2.2.2.2.2
  have h_C_N : C * N = lam • N := by
    rw [h_C, zvm_smul_mul, h_P_N, smul_smul]
  have h_N_C : N * C = 0 := by
    rw [h_C, zvm_mul_smul, h_N_P, _root_.smul_zero]
  have h_C_sq : C * C = lam • C := by
    rw [h_C, zvm_smul_mul, zvm_mul_smul, h_idem, smul_smul, smul_smul, smul_smul]
    exact congrArg (· • P_plus) (by dsimp [lam]; ring)
  have h_T_eq : T = N_vw • (P_plus * X) := by
    calc T
      _ = (P_plus * X) * P_plus + (P_plus * X) * P_minus := rfl
      _ = (P_plus * X) * (P_plus + P_minus) := by rw [← _root_.mul_add]
      _ = N_vw • (P_plus * X) := by rw [h_sum, zvm_mul_smul, zvm_mul_one]
  have h_norm_T : norm T = 0 := by
    rw [h_T_eq]
    change norm (smul N_vw (mul P_plus X)) = 0
    rw [norm_smul, norm_mul, h38.1, MulZeroClass.zero_mul, MulZeroClass.mul_zero]
  have h_T_sq : T * T = lam • T := by
    change (C + N) * (C + N) = lam • (C + N)
    rw [_root_.add_mul, _root_.mul_add, _root_.mul_add,
        h_C_sq, h_C_N, h_N_C, h_N_sq, _root_.add_zero, _root_.add_zero, ← _root_.smul_add]
  have h_T_cube_left : (T * T) * T = (lam * lam) • T := by
    rw [h_T_sq, zvm_smul_mul, h_T_sq, smul_smul]
  have h_T_cube_right : T * (T * T) = (lam * lam) • T := by
    rw [h_T_sq, zvm_mul_smul, h_T_sq, smul_smul]
  exact ⟨h_N_sq, h_C_N, h_N_C, h_norm_T, h_T_sq, h_T_cube_left, h_T_cube_right⟩

/-- Dual-vector transpose involution `X^* = ⟨X.a, X.w, X.v, X.b⟩` on `ZornVectorMatrix R`. -/
def zornTranspose (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨X.a, X.w, X.v, X.b⟩

/-- Frobenius–Gram scalar `μ_MP(Π_+) = trace (Π_+ * Π_+^*)` governing the Moore–Penrose
    generalized inverse of `tiltedPeircePlus r₁ r₂ c s v w`. -/
def moorePenroseGramScalar (r₁ r₂ c s : R) (v w : ZornVec3 R) : R :=
  (c * c) * (c * c) +
    (r₁ * c * s) * (r₁ * c * s) * ZornVec3.dot v v +
    (r₂ * c * s) * (r₂ * c * s) * ZornVec3.dot w w +
    (r₁ * r₂ * (s * s) * ZornVec3.dot v w) * (r₁ * r₂ * (s * s) * ZornVec3.dot v w)

/-- Rank-1 Gauss–Bruhat trifactor representation `(U_-(u) * Π_+) * U_+(p)` of a tilted Peirce operator. -/
noncomputable def rankOneTrifactor
    (u : ZornVec3 R) (r₁ r₂ c s : R) (v w p : ZornVec3 R) : ZornVectorMatrix R :=
  (zornParabolicMinus u * tiltedPeircePlus r₁ r₂ c s v w) * zornParabolicPlus p

/-- **47. All Four Non-Associative Moore–Penrose Generalized Inverse Equations for $\Pi_+$**:
    For ANY $r_1, r_2, c, s \in R$ and $v, w \in R^3$, let $P = \Pi_+(r_1, r_2, c, s, v, w)$,
    $P^* = \mathrm{zornTranspose}\;P$, and $\mu_{\mathrm{MP}} = \mathrm{moorePenroseGramScalar}\;r_1\;r_2\;c\;s\;v\;w$:
    1. **First Moore–Penrose Equation (Left & Right Associative)**:
       `(P * P^*) * P = μ_MP • P` and `P * (P^* * P) = μ_MP • P`.
    2. **Second Moore–Penrose Equation (Left & Right Associative)**:
       `(P^* * P) * P^* = μ_MP • P^*` and `P^* * (P * P^*) = μ_MP • P^*`.
    3. **Third Moore–Penrose Equation (Hermitian Symmetry of `P * P^*`)**:
       `zornTranspose (P * P^*) = P * P^*`.
    4. **Fourth Moore–Penrose Equation (Hermitian Symmetry of `P^* * P`)**:
       `zornTranspose (P^* * P) = P^* * P`. -/
theorem tiltedPeirce_moore_penrose_equations
    (r₁ r₂ c s : R) (v w : ZornVec3 R) :
    let P := tiltedPeircePlus r₁ r₂ c s v w
    let P_star := zornTranspose P
    let μ_MP := moorePenroseGramScalar r₁ r₂ c s v w
    (P * P_star) * P = μ_MP • P ∧
    P * (P_star * P) = μ_MP • P ∧
    (P_star * P) * P_star = μ_MP • P_star ∧
    P_star * (P * P_star) = μ_MP • P_star ∧
    zornTranspose (P * P_star) = P * P_star ∧
    zornTranspose (P_star * P) = P_star * P := by
  intro P P_star μ_MP
  have h_star : P_star = tiltedPeircePlus (-r₂) (-r₁) c s w v := by
    ext
    · rfl
    · rename_i i; fin_cases i <;> simp [P_star, P, zornTranspose, tiltedPeircePlus]
    · rename_i i; fin_cases i <;> simp [P_star, P, zornTranspose, tiltedPeircePlus]
    · simp [P_star, P, zornTranspose, tiltedPeircePlus, ZornVec3.dot, Fin.sum_univ_three]; ring
  have h_fid : bargmannFidelity r₁ r₂ c s v w (-r₂) (-r₁) c s w v = μ_MP := by
    simp [μ_MP, bargmannFidelity, moorePenroseGramScalar, ZornVec3.dot, Fin.sum_univ_three]
    ring
  have h43 := twoArchetype_bargmann_sandwich_and_fidelity r₁ r₂ c s (-r₂) (-r₁) c s v w w v
  have h_mp1_left : (P * P_star) * P = μ_MP • P := by
    have h := h43.2.2.2.1
    rw [← h_star, h_fid] at h
    exact h
  have h_mp1_right : P * (P_star * P) = μ_MP • P :=
    (sub_eq_zero.mp (bundledAssociator_flexible P P_star)).symm.trans h_mp1_left
  have h_mp2_left : (P_star * P) * P_star = μ_MP • P_star := by
    have h := h43.2.2.2.2.1
    rw [← h_star, h_fid] at h
    exact h
  have h_mp2_right : P_star * (P * P_star) = μ_MP • P_star :=
    (sub_eq_zero.mp (bundledAssociator_flexible P_star P)).symm.trans h_mp2_left
  refine ⟨h_mp1_left, h_mp1_right, h_mp2_left, h_mp2_right, ?_, ?_⟩
  · ext
    · rfl
    · rename_i i; fin_cases i <;>
        (simp [P, P_star, zornTranspose, tiltedPeircePlus, mul, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (simp [P, P_star, zornTranspose, tiltedPeircePlus, mul, ZornVec3.cross]; ring)
    · rfl
  · ext
    · rfl
    · rename_i i; fin_cases i <;>
        (simp [P, P_star, zornTranspose, tiltedPeircePlus, mul, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (simp [P, P_star, zornTranspose, tiltedPeircePlus, mul, ZornVec3.cross]; ring)
    · rfl

/-- **48. Gauss–Bruhat Rank-1 Trifactor Associator Formula, Aligned Associativity, & Singular Norm**:
    For ANY $u, p, v, w \in R^3$, $r_1, r_2, c, s \in R$, and arbitrary $X \in \mathrm{Zorn}(R)$:
    - **Universal Parabolic Trifactor Associator Formula**:
       `zornAssociator (U_-(u)) X (U_+(p)) = ⟨0, u × (X.v × p), -(u × X.w) × p, 0⟩`.
    - **Vanishing Aligned Gauss–Bruhat Trifactor Associator ($u = w, p = v$)**:
       `zornAssociator (U_-(w)) (Π_+(r₁, r₂, c, s, v, w)) (U_+(v)) = 0`.
    - **Universal Singular Norm Conservation**:
       `norm (rankOneTrifactor u r₁ r₂ c s v w p) = 0`! -/
theorem rankOneTrifactor_assoc_and_singular_norm
    (u p v w : ZornVec3 R) (r₁ r₂ c s : R) (X : ZornVectorMatrix R) :
    let P := tiltedPeircePlus r₁ r₂ c s v w
    zornAssociator (zornParabolicMinus u) X (zornParabolicPlus p) =
      ⟨0, ZornVec3.cross u (ZornVec3.cross X.v p),
       fun i => -ZornVec3.cross (ZornVec3.cross u X.w) p i, 0⟩ ∧
    zornAssociator (zornParabolicMinus w) P (zornParabolicPlus v) = 0 ∧
    norm (rankOneTrifactor u r₁ r₂ c s v w p) = 0 := by
  intro P
  have h_assoc : ∀ (u' p' : ZornVec3 R) (Y : ZornVectorMatrix R),
      zornAssociator (zornParabolicMinus u') Y (zornParabolicPlus p') =
        ⟨0, ZornVec3.cross u' (ZornVec3.cross Y.v p'),
         fun i => -ZornVec3.cross (ZornVec3.cross u' Y.w) p' i, 0⟩ := by
    intro u' p' Y
    unfold zornAssociator
    simp only [_root_.sub_eq_add_neg]
    ext
    · simp [zornParabolicMinus, zornParabolicPlus, zornExpLowerNil, zornExpUpperNil,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def,
            add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        (simp [zornParabolicMinus, zornParabolicPlus, zornExpLowerNil, zornExpUpperNil,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def,
               add, neg, mul, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (simp [zornParabolicMinus, zornParabolicPlus, zornExpLowerNil, zornExpUpperNil,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_mul_def,
               add, neg, mul, ZornVec3.cross]; ring)
    · simp [zornParabolicMinus, zornParabolicPlus, zornExpLowerNil, zornExpUpperNil,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_mul_def,
            add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  refine ⟨h_assoc u p X, ?_, ?_⟩
  · rw [h_assoc w v P]
    ext
    · rfl
    · rename_i i; fin_cases i <;>
        (simp [P, tiltedPeircePlus, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (simp [P, tiltedPeircePlus, ZornVec3.cross]; ring)
    · rfl
  · change norm (mul (mul (zornParabolicMinus u) P) (zornParabolicPlus p)) = 0
    rw [norm_mul, norm_mul,
        (tiltedPeirce_norm_central_sum_and_associators r₁ r₂ c s v w 0).1,
        MulZeroClass.mul_zero, MulZeroClass.zero_mul]

/-- Tilted Peirce grading polarization operator `Γ_Π = Π_+ - Π_-`. -/
noncomputable def tiltedPeirceGamma (r₁ r₂ c s : R) (v w : ZornVec3 R) : ZornVectorMatrix R :=
  tiltedPeircePlus r₁ r₂ c s v w - tiltedPeirceMinus r₁ r₂ c s v w

/-- Diagonal Peirce spectral operator `D_Π(X) = τ_+(X) • Π_+ + τ_-(X) • Π_-`. -/
noncomputable def peirceDiagonalOperator (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  zornPeirceCornerTracePlus r₁ r₂ c s v w X • tiltedPeircePlus r₁ r₂ c s v w +
    zornPeirceCornerTraceMinus r₁ r₂ c s v w X • tiltedPeirceMinus r₁ r₂ c s v w

/-- Off-diagonal Peirce transition operator `O_Π(X) = X_{+-} + X_{-+} = (Π_+ * X) * Π_- + (Π_- * X) * Π_+`. -/
noncomputable def peirceOffDiagOperator (r₁ r₂ c s : R) (v w : ZornVec3 R) (X : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  peirceBlockPM r₁ r₂ c s v w X + peirceBlockMP r₁ r₂ c s v w X

/-- **49. Conjugate Peirce Duality, Four-Factor Transition Associativity, & Chiral Off-Diagonal Square**:
    For ANY $r_1, r_2, c, s, r_1', r_2', c_2, s_2 \in R$, $v, w, v_2, w_2 \in R^3$, and arbitrary
    $X \in \mathrm{Zorn}(R)$, let $\Pi_+ = \Pi_+(r_1, r_2, c, s, v, w)$, $\Pi_- = \Pi_-(r_1, r_2, c, s, v, w)$,
    $\Pi_2 = \Pi_+(r_1', r_2', c_2, s_2, v_2, w_2)$, $\Gamma_\Pi = \Pi_+ - \Pi_-$,
    $D_\Pi(X) = \mathrm{peirceDiagonalOperator}\;r_1\;r_2\;c\;s\;v\;w\;X$, and
    $O_\Pi(X) = \mathrm{peirceOffDiagOperator}\;r_1\;r_2\;c\;s\;v\;w\;X$:
    1. **Cayley–Dickson Conjugate Duality of the Tilted Peirce Projectors**:
       `conj Π_+ = Π_-` and `conj Π_- = Π_+`.
    2. **Universal Four-Factor Transition Associativity**:
       `((Π_+ * Π_2) * Π_+) * Π_2 = (Π_+ * Π_2) * (Π_+ * Π_2)`.
    3. **Diagonal + Off-Diagonal Resolution of the State**:
       `D_Π(X) + O_Π(X) = (N_vw * N_vw) • X`.
    4. **Tracelessness of the Off-Diagonal Peirce Operator**:
       `trace (O_Π(X)) = 0`.
    5. **Exact Chiral Anticommutation with `Γ_Π` & Commutation of `D_Π(X)` with `Γ_Π`**:
       `Γ_Π * O_Π(X) + O_Π(X) * Γ_Π = 0` and `Γ_Π * D_Π(X) = D_Π(X) * Γ_Π`.
    6. **Universal Scalar Square of the Off-Diagonal Peirce Operator**:
       `O_Π(X) * O_Π(X) = (-norm (O_Π(X))) • 1` and
       `O_Π(X) * O_Π(X) = (N_vw * N_vw * (τ_+(X) * τ_-(X) - N_vw * N_vw * norm X)) • 1`! -/
theorem peirceOffDiagOperator_chiral_anticomm_and_scalar_square
    (r₁ r₂ c s r₁' r₂' c₂ s₂ : R) (v w v₂ w₂ : ZornVec3 R) (X : ZornVectorMatrix R) :
    let P_plus := tiltedPeircePlus r₁ r₂ c s v w
    let P_minus := tiltedPeirceMinus r₁ r₂ c s v w
    let P₂ := tiltedPeircePlus r₁' r₂' c₂ s₂ v₂ w₂
    let N_vw := c * c - r₁ * r₂ * (s * s) * ZornVec3.dot v w
    let τ_plus := zornPeirceCornerTracePlus r₁ r₂ c s v w X
    let τ_minus := zornPeirceCornerTraceMinus r₁ r₂ c s v w X
    let Γ_Pi := tiltedPeirceGamma r₁ r₂ c s v w
    let D_X := peirceDiagonalOperator r₁ r₂ c s v w X
    let O_X := peirceOffDiagOperator r₁ r₂ c s v w X
    conj P_plus = P_minus ∧
    conj P_minus = P_plus ∧
    ((P_plus * P₂) * P_plus) * P₂ = (P_plus * P₂) * (P_plus * P₂) ∧
    D_X + O_X = (N_vw * N_vw) • X ∧
    trace O_X = 0 ∧
    Γ_Pi * O_X + O_X * Γ_Pi = 0 ∧
    Γ_Pi * D_X = D_X * Γ_Pi ∧
    O_X * O_X = (-norm O_X) • (one : ZornVectorMatrix R) ∧
    O_X * O_X = (N_vw * N_vw * (τ_plus * τ_minus - N_vw * N_vw * norm X)) • (one : ZornVectorMatrix R) := by
  intro P_plus P_minus P₂ N_vw τ_plus τ_minus Γ_Pi D_X O_X
  let X_pp := peirceBlockPP r₁ r₂ c s v w X
  let X_pm := peirceBlockPM r₁ r₂ c s v w X
  let X_mp := peirceBlockMP r₁ r₂ c s v w X
  let X_mm := peirceBlockMM r₁ r₂ c s v w X
  have h33 := tiltedPeirce_orth_idem_chordal_and_syzygy r₁ r₂ c s v w
  have h38 := tiltedPeirce_norm_central_sum_and_associators r₁ r₂ c s v w X
  have h39 := tiltedPeirce_module_action_corner_reduction_and_four_block_decomposition r₁ r₂ c s v w X
  have h41 := peirceBlock_offDiag_nilpotence_and_absorption r₁ r₂ c s v w X
  have h42 := peirceBlock_offDiag_coupling_and_determinant_law r₁ r₂ c s v w X
  have h43 := twoArchetype_bargmann_sandwich_and_fidelity r₁ r₂ c s r₁' r₂' c₂ s₂ v w v₂ w₂
  have h45 := twoArchetype_transition_idempotence_and_commutator_clifford r₁ r₂ c s r₁' r₂' c₂ s₂ v w v₂ w₂
  have h_conj_p : conj P_plus = P_minus := by
    ext
    · simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus, conj, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus, conj]
    · rename_i i; fin_cases i <;> simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus, conj]
    · simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus, conj, ZornVec3.dot, Fin.sum_univ_three]
  have h_conj_m : conj P_minus = P_plus := by
    ext
    · simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus, conj, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus, conj]
    · rename_i i; fin_cases i <;> simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus, conj]
    · simp [P_plus, P_minus, tiltedPeircePlus, tiltedPeirceMinus, conj, ZornVec3.dot, Fin.sum_univ_three]
  have h_four_assoc : ((P_plus * P₂) * P_plus) * P₂ = (P_plus * P₂) * (P_plus * P₂) := by
    rw [h43.2.2.2.1, zvm_smul_mul, ← h45.1]
  have h_res : D_X + O_X = (N_vw * N_vw) • X := by
    have h_pp : X_pp = τ_plus • P_plus := h39.2.2.2.2.1
    have h_mm : X_mm = τ_minus • P_minus := h39.2.2.2.2.2.1
    have h_4b : X_pp + X_pm + X_mp + X_mm = (N_vw * N_vw) • X := h39.2.2.2.2.2.2.2
    calc D_X + O_X
      _ = (τ_plus • P_plus + τ_minus • P_minus) + (X_pm + X_mp) := rfl
      _ = (X_pp + X_mm) + (X_pm + X_mp) := by rw [← h_pp, ← h_mm]
      _ = X_pp + X_pm + X_mp + X_mm := by abel
      _ = (N_vw * N_vw) • X := h_4b
  have h_tr_O : trace O_X = 0 := by
    change trace (add X_pm X_mp) = 0
    rw [trace_add, h41.1, h41.2.1, _root_.add_zero]
  have h_sum : P_plus + P_minus = N_vw • (one : ZornVectorMatrix R) := h38.2.2.1
  have h_idem_p : P_plus * P_plus = N_vw • P_plus := h33.2.1
  have h_orth_pm : P_plus * P_minus = 0 := h33.1
  have h_orth_mp : P_minus * P_plus = 0 := by
    have h1 : P_plus * P_plus + P_minus * P_plus = N_vw • P_plus := by
      calc P_plus * P_plus + P_minus * P_plus
        _ = (P_plus + P_minus) * P_plus := by rw [← _root_.add_mul]
        _ = N_vw • P_plus := by rw [h_sum, zvm_smul_mul, zvm_one_mul]
    rw [h_idem_p] at h1
    calc P_minus * P_plus
      _ = (N_vw • P_plus + P_minus * P_plus) - N_vw • P_plus := (add_sub_cancel_left _ _).symm
      _ = N_vw • P_plus - N_vw • P_plus := by rw [h1]
      _ = 0 := _root_.sub_self _
  have h_mp_expr : X_mp = N_vw • (X * P_plus) - τ_plus • P_plus := by
    apply eq_sub_of_add_eq'
    have h_cp : (P_plus * X) * P_plus = τ_plus • P_plus := h39.2.2.2.2.1
    calc τ_plus • P_plus + X_mp
      _ = (P_plus * X) * P_plus + (P_minus * X) * P_plus := by rw [← h_cp]; rfl
      _ = ((P_plus + P_minus) * X) * P_plus := by rw [← _root_.add_mul, ← _root_.add_mul]
      _ = N_vw • (X * P_plus) := by rw [h_sum, zvm_smul_mul, zvm_one_mul, zvm_smul_mul]
  have h_mp_right_p : X_mp * P_plus = N_vw • X_mp := by
    rw [h_mp_expr, _root_.sub_mul, zvm_smul_mul, zvm_smul_mul,
        h39.2.2.2.1, h_idem_p, smul_sub, smul_comm τ_plus N_vw P_plus]
  have h_mp_left_p : P_plus * X_mp = 0 := by
    have h_flex : P_plus * (X * P_plus) = (P_plus * X) * P_plus :=
      (sub_eq_zero.mp (bundledAssociator_flexible P_plus X)).symm
    rw [h_mp_expr, _root_.mul_sub, zvm_mul_smul, zvm_mul_smul,
        h_flex, h39.2.2.2.2.1, h_idem_p, smul_smul, smul_smul, mul_comm τ_plus N_vw, _root_.sub_self]
  have h_mp_right_m : X_mp * P_minus = 0 := by
    have h1 : X_mp * P_plus + X_mp * P_minus = N_vw • X_mp := by
      calc X_mp * P_plus + X_mp * P_minus
        _ = X_mp * (P_plus + P_minus) := by rw [← _root_.mul_add]
        _ = N_vw • X_mp := by rw [h_sum, zvm_mul_smul, zvm_mul_one]
    rw [h_mp_right_p] at h1
    calc X_mp * P_minus
      _ = (N_vw • X_mp + X_mp * P_minus) - N_vw • X_mp := (add_sub_cancel_left _ _).symm
      _ = N_vw • X_mp - N_vw • X_mp := by rw [h1]
      _ = 0 := _root_.sub_self _
  have h_mp_left_m : P_minus * X_mp = N_vw • X_mp := by
    calc P_minus * X_mp
      _ = 0 + P_minus * X_mp := (_root_.zero_add _).symm
      _ = P_plus * X_mp + P_minus * X_mp := by rw [h_mp_left_p]
      _ = (P_plus + P_minus) * X_mp := by rw [← _root_.add_mul]
      _ = N_vw • X_mp := by rw [h_sum, zvm_smul_mul, zvm_one_mul]
  have h_anticomm : Γ_Pi * O_X + O_X * Γ_Pi = 0 := by
    change (P_plus - P_minus) * (X_pm + X_mp) + (X_pm + X_mp) * (P_plus - P_minus) = 0
    rw [_root_.mul_add, _root_.sub_mul, _root_.sub_mul,
        _root_.add_mul, _root_.mul_sub, _root_.mul_sub,
        h41.2.2.2.2.2.2.1, h41.2.2.2.2.2.2.2.1, h41.2.2.2.2.2.2.2.2.1, h41.2.2.2.2.2.2.2.2.2,
        h_mp_left_p, h_mp_left_m, h_mp_right_p, h_mp_right_m]
    abel
  have h_comm_D : Γ_Pi * D_X = D_X * Γ_Pi := by
    change (P_plus - P_minus) * (τ_plus • P_plus + τ_minus • P_minus) =
           (τ_plus • P_plus + τ_minus • P_minus) * (P_plus - P_minus)
    rw [_root_.mul_add, _root_.sub_mul, _root_.sub_mul,
        _root_.add_mul, _root_.mul_sub, _root_.mul_sub,
        zvm_mul_smul, zvm_mul_smul, zvm_mul_smul, zvm_mul_smul,
        zvm_smul_mul, zvm_smul_mul, zvm_smul_mul, zvm_smul_mul,
        h_orth_pm, h_orth_mp, _root_.smul_zero, _root_.smul_zero]
  have h_O_sq_ch : O_X * O_X = (-norm O_X) • (one : ZornVectorMatrix R) := by
    have hch := (zorn_involution_cayley_hamilton_and_antiautomorphism O_X 0).2.2.2.1
    rw [h_tr_O, _root_.zero_smul, _root_.sub_zero] at hch
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hch
  have h_O_sq_det :
      O_X * O_X = (N_vw * N_vw * (τ_plus * τ_minus - N_vw * N_vw * norm X)) • (one : ZornVectorMatrix R) := by
    change (X_pm + X_mp) * (X_pm + X_mp) =
      (N_vw * N_vw * (τ_plus * τ_minus - N_vw * N_vw * norm X)) • (one : ZornVectorMatrix R)
    rw [_root_.add_mul, _root_.mul_add, _root_.mul_add,
        h41.2.2.2.2.1, h41.2.2.2.2.2.1, _root_.zero_add, _root_.add_zero]
    exact h42.2.2
  exact ⟨h_conj_p, h_conj_m, h_four_assoc, h_res, h_tr_O, h_anticomm, h_comm_D, h_O_sq_ch, h_O_sq_det⟩

/-!
### Multi-Step Projector Chain Idempotence, Drazin–Moore–Penrose Spectral Splittings, Jordan–Lie–Malcev Decomposition, & Directed Colimit Retractions
-/

/-- **50. Universal Multi-Step Projector Chain Idempotence (`multiStep_projector_chain_idempotence`)**:
    Because $N(A * B) = N(A) * N(B)$ and $N(\Pi_1) = 0$, for ANY operator $Z \in \mathrm{Zorn}(R)$
    (including arbitrary $k$-step multi-projector products $Z = \Pi_2 * (\Pi_3 * \dots * \Pi_k)$),
    both the left-projected operator $W_L = \Pi_1 * Z$ and the right-projected operator
    $W_R = Z * \Pi_1$ are isotropic ($N(W_L) = N(W_R) = 0$) and satisfy exact scaled
    idempotence across all 8 dimensions of $\mathrm{Zorn}(R)$:
    `W_L * W_L = trace W_L • W_L` and `W_R * W_R = trace W_R • W_R`! -/
theorem multiStep_projector_chain_idempotence
    (r₁ r₂ c₁ s₁ : R) (v₁ w₁ : ZornVec3 R) (Z : ZornVectorMatrix R) :
    let P₁ := tiltedPeircePlus r₁ r₂ c₁ s₁ v₁ w₁
    let W_L := P₁ * Z
    let W_R := Z * P₁
    norm W_L = 0 ∧
    norm W_R = 0 ∧
    W_L * W_L = trace W_L • W_L ∧
    W_R * W_R = trace W_R • W_R := by
  intro P₁ W_L W_R
  have hP : norm P₁ = 0 :=
    (tiltedPeirce_norm_central_sum_and_associators r₁ r₂ c₁ s₁ v₁ w₁ 0).1
  have h_nL : norm W_L = 0 := by
    change norm (mul P₁ Z) = 0
    rw [norm_mul, hP, MulZeroClass.zero_mul]
  have h_nR : norm W_R = 0 := by
    change norm (mul Z P₁) = 0
    rw [norm_mul, hP, MulZeroClass.mul_zero]
  refine ⟨h_nL, h_nR, ?_, ?_⟩
  · apply sub_eq_zero.mp
    have hch := (zorn_involution_cayley_hamilton_and_antiautomorphism W_L 0).2.2.2.1
    rw [h_nL, _root_.zero_smul, _root_.add_zero] at hch
    exact hch
  · apply sub_eq_zero.mp
    have hch := (zorn_involution_cayley_hamilton_and_antiautomorphism W_R 0).2.2.2.1
    rw [h_nR, _root_.zero_smul, _root_.add_zero] at hch
    exact hch

/-- Upper-triangular singular rank-1 operator `upperPeirceCore lam v = ⟨lam, v, 0, 0⟩`. -/
def upperPeirceCore (lam : R) (v : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨lam, v, 0, 0⟩

/-- Pure upper off-diagonal Peirce root `peirceRootPlus v = ⟨0, v, 0, 0⟩`. -/
def peirceRootPlus (v : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨0, v, 0, 0⟩

/-- Pure lower off-diagonal Peirce root `peirceRootMinus w = ⟨0, 0, w, 0⟩`. -/
def peirceRootMinus (w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨0, 0, w, 0⟩

/-- **51. Moore–Penrose Partial Isometry Triple Equations & Group/Drazin Inverse of `upperPeirceCore`**:
    For all $r_1, r_2, c, s \in R$, $v, w \in R^3$, and unit $u \in R^\times$:
    1. **Zero Moore–Penrose Associator**: `zornAssociator (peirceRootPlus v) (peirceRootMinus w) (peirceRootPlus v) = 0`.
    2. **Moore–Penrose Triple Equations**:
       `(peirceRootPlus v * peirceRootMinus w) * peirceRootPlus v = (v ⋅ w) • peirceRootPlus v` and
       `(peirceRootMinus w * peirceRootPlus v) * peirceRootMinus w = (v ⋅ w) • peirceRootMinus w`.
    3. **Projective Group/Drazin Reflexivity of $\Pi_+$**:
       `(Π_+ * Π_+) * Π_+ = N_vw² • Π_+` and `Π_+ * conj Π_+ = 0`.
    4. **Exact Group/Drazin Inverse of $C(u, v) = \begin{pmatrix} u & v \\ 0 & 0 \end{pmatrix}$ ($u \in R^\times$)**:
       With $C^\#(u, v) = C(u^{-1}, (u^{-1})^2 \bullet v)$,
       `C * C_drazin = C_drazin * C`, `(C * C_drazin) * C = C`, and `(C_drazin * C) * C_drazin = C_drazin`! -/
theorem zorn_drazin_moore_penrose_spectral_splitting
    (r₁ r₂ c s : R) (v w : ZornVec3 R) (u : Rˣ) :
    let E₁₂ := peirceRootPlus v
    let E₂₁ := peirceRootMinus w
    let P_plus := tiltedPeircePlus r₁ r₂ c s v w
    let N_vw := c * c - r₁ * r₂ * (s * s) * ZornVec3.dot v w
    let C := upperPeirceCore (u : R) v
    let C_drazin := upperPeirceCore (↑u⁻¹ : R) (((↑u⁻¹ : R) * (↑u⁻¹ : R)) • v)
    zornAssociator E₁₂ E₂₁ E₁₂ = 0 ∧
    (E₁₂ * E₂₁) * E₁₂ = (ZornVec3.dot v w) • E₁₂ ∧
    (E₂₁ * E₁₂) * E₂₁ = (ZornVec3.dot v w) • E₂₁ ∧
    (P_plus * P_plus) * P_plus = (N_vw * N_vw) • P_plus ∧
    P_plus * conj P_plus = 0 ∧
    C * C_drazin = C_drazin * C ∧
    (C * C_drazin) * C = C ∧
    (C_drazin * C) * C_drazin = C_drazin := by
  intro E₁₂ E₂₁ P_plus N_vw C C_drazin
  have h33 := tiltedPeirce_orth_idem_chordal_and_syzygy r₁ r₂ c s v w
  have h49 := peirceOffDiagOperator_chiral_anticomm_and_scalar_square r₁ r₂ c s 0 0 0 0 v w 0 0 0
  have hu_r : (u : R) * (↑u⁻¹ : R) = 1 := Units.mul_inv u
  have h_core_mul : ∀ (a₁ a₂ s₁ s₂ : R),
      upperPeirceCore a₁ (s₁ • v) * upperPeirceCore a₂ (s₂ • v) =
        upperPeirceCore (a₁ * a₂) ((a₁ * s₂) • v) := by
    intro a₁ a₂ s₁ s₂
    ext
    · simp [upperPeirceCore, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [upperPeirceCore, mul, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (simp [upperPeirceCore, mul, ZornVec3.cross]; ring)
    · simp [upperPeirceCore, mul, ZornVec3.dot]
  have hC_eq : C = upperPeirceCore (u : R) ((1 : R) • v) := by
    dsimp [C]; rw [_root_.one_smul]
  have h_cd : C * C_drazin = upperPeirceCore 1 ((↑u⁻¹ : R) • v) := by
    change C * upperPeirceCore (↑u⁻¹ : R) (((↑u⁻¹ : R) * (↑u⁻¹ : R)) • v) = _
    rw [hC_eq, h_core_mul, hu_r, ← _root_.mul_assoc, hu_r, _root_.one_mul]
  have h_dc : C_drazin * C = upperPeirceCore 1 ((↑u⁻¹ : R) • v) := by
    change upperPeirceCore (↑u⁻¹ : R) (((↑u⁻¹ : R) * (↑u⁻¹ : R)) • v) * C = _
    rw [hC_eq, h_core_mul, Units.inv_mul, _root_.mul_one]
  refine ⟨bundledAssociator_flexible E₁₂ E₂₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext
    · simp [E₁₂, E₂₁, peirceRootPlus, peirceRootMinus, mul, smul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        simp [E₁₂, E₂₁, peirceRootPlus, peirceRootMinus, mul, smul,
              ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        simp [E₁₂, E₂₁, peirceRootPlus, peirceRootMinus, mul, smul, ZornVec3.cross]
    · simp [E₁₂, E₂₁, peirceRootPlus, peirceRootMinus, mul, smul,
            ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  · ext
    · simp [E₁₂, E₂₁, peirceRootPlus, peirceRootMinus, mul, smul,
            ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        simp [E₁₂, E₂₁, peirceRootPlus, peirceRootMinus, mul, smul, ZornVec3.cross]
    · rename_i i; fin_cases i <;>
        (simp [E₁₂, E₂₁, peirceRootPlus, peirceRootMinus, mul, smul,
               ZornVec3.dot, Fin.sum_univ_three]; ring)
    · simp [E₁₂, E₂₁, peirceRootPlus, peirceRootMinus, mul, smul, ZornVec3.dot]
  · rw [h33.2.1, zvm_smul_mul, h33.2.1, smul_smul]
  · rw [h49.1, h33.1]
  · rw [h_cd, h_dc]
  · rw [h_cd, hC_eq, h_core_mul, _root_.one_mul, _root_.one_mul]
  · change (C_drazin * C) * upperPeirceCore (↑u⁻¹ : R) (((↑u⁻¹ : R) * (↑u⁻¹ : R)) • v) =
      upperPeirceCore (↑u⁻¹ : R) (((↑u⁻¹ : R) * (↑u⁻¹ : R)) • v)
    rw [h_dc, h_core_mul, _root_.one_mul, _root_.one_mul]

/-- Symmetric Jordan product (anticommutator) `zornJordanMul X Y = X * Y + Y * X`. -/
noncomputable def zornJordanMul (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  X * Y + Y * X

/-- **52. Universal Jordan–Lie–Malcev Splitting & Jacobiator–Associator Bridge**:
    For ANY $X, Y, Z \in \mathrm{Zorn}(R)$:
    1. **Exact Jordan–Lie Reconstruction**: `(2 : R) • (X * Y) = zornJordanMul X Y + zornComm X Y`.
    2. **Cayley Involution Selection Rule**:
       `conj (zornJordanMul X Y) = zornJordanMul (conj X) (conj Y)` and
       `conj (zornComm X Y) = -zornComm (conj X) (conj Y)`.
    3. **Tracelessness of Commutator**: `trace (zornComm X Y) = 0`.
    4. **Universal Malcev Jacobiator Law**:
       `zornJacobiator X Y Z = (-6 : R) • zornAssociator X Y Z`! -/
theorem zorn_jordan_lie_malcev_operator_splitting (X Y Z : ZornVectorMatrix R) :
    (2 : R) • (X * Y) = zornJordanMul X Y + zornComm X Y ∧
    conj (zornJordanMul X Y) = zornJordanMul (conj X) (conj Y) ∧
    conj (zornComm X Y) = -zornComm (conj X) (conj Y) ∧
    trace (zornComm X Y) = 0 ∧
    zornJacobiator X Y Z = (-6 : R) • zornAssociator X Y Z := by
  refine ⟨?_, ?_, ?_, ?_, zornJacobiator_eq_neg_six_smul_zornAssociator X Y Z⟩
  · unfold zornJordanMul zornComm
    rw [two_smul]
    abel
  · ext
    · simp [zornJordanMul, conj, InfoGeometry.Algebra.zvm_add_def, add, mul,
            ZornVec3.dot, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [zornJordanMul, conj, InfoGeometry.Algebra.zvm_add_def, add, mul,
               ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (simp [zornJordanMul, conj, InfoGeometry.Algebra.zvm_add_def, add, mul,
               ZornVec3.cross]; ring)
    · simp [zornJordanMul, conj, InfoGeometry.Algebra.zvm_add_def, add, mul,
            ZornVec3.dot, Fin.sum_univ_three]; ring
  · ext
    · simp [zornComm, _root_.sub_eq_add_neg, conj,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [zornComm, _root_.sub_eq_add_neg, conj,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, ZornVec3.cross]; ring)
    · rename_i i; fin_cases i <;>
        (simp [zornComm, _root_.sub_eq_add_neg, conj,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, ZornVec3.cross]; ring)
    · simp [zornComm, _root_.sub_eq_add_neg, conj,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
  · simp [zornComm, _root_.sub_eq_add_neg, trace,
          InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
          add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]
    ring

/-- Stage 0 of the Peirce doubling tower: the 2D split Cartan torus algebra $R \times R$. -/
@[ext]
structure CartanTorus (R : Type*) where
  lam : R
  mu : R
  deriving DecidableEq

instance : Zero (CartanTorus R) := ⟨⟨0, 0⟩⟩
instance : One (CartanTorus R) := ⟨⟨1, 1⟩⟩
instance : Inhabited (CartanTorus R) := ⟨0⟩
instance : Mul (CartanTorus R) := ⟨fun d₁ d₂ => ⟨d₁.lam * d₂.lam, d₁.mu * d₂.mu⟩⟩

@[simp]
lemma cartan_mul_lam (d₁ d₂ : CartanTorus R) : (d₁ * d₂).lam = d₁.lam * d₂.lam := rfl

@[simp]
lemma cartan_mul_mu (d₁ d₂ : CartanTorus R) : (d₁ * d₂).mu = d₁.mu * d₂.mu := rfl

/-- Quadratic norm `d.lam * d.mu` on `CartanTorus R`. -/
def cartanNorm (d : CartanTorus R) : R := d.lam * d.mu

/-- Stage $0 \to 1$ embedding $\Psi_1 : \mathrm{Cartan}(R) \hookrightarrow M_2(R)$. -/
def embedCartanToMat (d : CartanTorus R) : Matrix (Fin 2) (Fin 2) R :=
  !![d.lam, 0; 0, d.mu]

/-- Stage $1 \to 0$ retraction $\rho_1 : M_2(R) \twoheadrightarrow \mathrm{Cartan}(R)$. -/
def retractMatToCartan (X : Matrix (Fin 2) (Fin 2) R) : CartanTorus R :=
  ⟨X 0 0, X 1 1⟩

/-- Stage $1 \to 2$ embedding $\Psi_2 : M_2(R) \hookrightarrow \mathrm{Zorn}(R)$ along `basis 0`. -/
def embedMatToZorn (X : Matrix (Fin 2) (Fin 2) R) : ZornVectorMatrix R :=
  ⟨X 0 0, (X 0 1) • ZornVec3.basis 0, (X 1 0) • ZornVec3.basis 0, X 1 1⟩

/-- Stage $2 \to 1$ retraction $\rho_2 : \mathrm{Zorn}(R) \twoheadrightarrow M_2(R)$ along `basis 0`. -/
def retractZornToMat (Z : ZornVectorMatrix R) : Matrix (Fin 2) (Fin 2) R :=
  !![Z.a, Z.v 0; Z.w 0, Z.b]

/-- **53. Directed Inductive System Functoriality & Split Retractions**:
    Across the 3-stage Peirce doubling tower $\mathrm{Cartan}(R) \xrightarrow{\Psi_1} M_2(R) \xrightarrow{\Psi_2} \mathrm{Zorn}(R)$:
    1. Stage $0 \to 1$ Multiplicativity & Retraction:
       `embedCartanToMat (d₁ * d₂) = embedCartanToMat d₁ * embedCartanToMat d₂` and
       `retractMatToCartan (embedCartanToMat d₁) = d₁`.
    2. Stage $1 \to 2$ Multiplicativity & Retraction:
       `embedMatToZorn (X * Y) = embedMatToZorn X * embedMatToZorn Y` and
       `retractZornToMat (embedMatToZorn X) = X`.
    3. Composite $0 \to 2$ Directed Retraction & Norm Coherence:
       `retractMatToCartan (retractZornToMat (embedMatToZorn (embedCartanToMat d₁))) = d₁` and
       `norm (embedMatToZorn (embedCartanToMat d₁)) = cartanNorm d₁`! -/
theorem directed_colimit_tower_retractions_and_functoriality
    (d₁ d₂ : CartanTorus R) (X Y : Matrix (Fin 2) (Fin 2) R) :
    embedCartanToMat (d₁ * d₂) = embedCartanToMat d₁ * embedCartanToMat d₂ ∧
    retractMatToCartan (embedCartanToMat d₁) = d₁ ∧
    embedMatToZorn (X * Y) = embedMatToZorn X * embedMatToZorn Y ∧
    retractZornToMat (embedMatToZorn X) = X ∧
    retractMatToCartan (retractZornToMat (embedMatToZorn (embedCartanToMat d₁))) = d₁ ∧
    norm (embedMatToZorn (embedCartanToMat d₁)) = cartanNorm d₁ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [embedCartanToMat, Matrix.mul_apply, Fin.sum_univ_two]
  · ext <;> rfl
  · ext
    · simp [embedMatToZorn, mul, ZornVec3.basis, ZornVec3.dot,
            Matrix.mul_apply, Fin.sum_univ_two]
    · rename_i i; fin_cases i <;>
        (simp [embedMatToZorn, mul, ZornVec3.basis, ZornVec3.cross,
               Matrix.mul_apply, Fin.sum_univ_two]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [embedMatToZorn, mul, ZornVec3.basis, ZornVec3.cross,
               Matrix.mul_apply, Fin.sum_univ_two]; try ring)
    · simp [embedMatToZorn, mul, ZornVec3.basis, ZornVec3.dot,
            Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [retractZornToMat, embedMatToZorn, ZornVec3.basis]
  · ext <;> simp [retractMatToCartan, retractZornToMat, embedMatToZorn, embedCartanToMat]
  · simp [norm, embedMatToZorn, embedCartanToMat, cartanNorm, ZornVec3.dot]

/-!
## 54. 5-Graded Kantor-Koecher-Tits Contact Structure, Associative Heisenberg Nilradicals, & Erlangen Homogeneous Flag States
-/

/-- **Grade $-2$ ($\mathcal{G}_{-2}$)**: Longitudinal dual contact ray $E_{-2}(\eta) = \langle 0, [\eta, 0, 0], 0, 0 \rangle$. -/
def zornGradeMinus2 (η : R) : ZornVectorMatrix R := ⟨0, ![η, 0, 0], 0, 0⟩

/-- **Grade $-1$ ($\mathcal{G}_{-1}$)**: Transverse backward plane $E_{-1}(y, z) = \langle 0, 0, [0, y, z], 0 \rangle$. -/
def zornGradeMinus1 (y z : R) : ZornVectorMatrix R := ⟨0, 0, ![0, y, z], 0⟩

/-- **Grade $0$ ($\mathcal{G}_0$)**: Cartan/modular diagonal $D(\rho_+, \rho_-) = \langle \rho_+, 0, 0, \rho_- \rangle$. -/
def zornGradeZero (ρ_plus ρ_minus : R) : ZornVectorMatrix R := ⟨ρ_plus, 0, 0, ρ_minus⟩

/-- **Grade $+1$ ($\mathcal{G}_{+1}$)**: Transverse forward plane $E_{+1}(y, z) = \langle 0, [0, y, z], 0, 0 \rangle$. -/
def zornGradePlus1 (y z : R) : ZornVectorMatrix R := ⟨0, ![0, y, z], 0, 0⟩

/-- **Grade $+2$ ($\mathcal{G}_{+2}$)**: Longitudinal primal contact ray $E_{+2}(\xi) = \langle 0, 0, [\xi, 0, 0], 0 \rangle$. -/
def zornGradePlus2 (ξ : R) : ZornVectorMatrix R := ⟨0, 0, ![ξ, 0, 0], 0⟩

/-- Positive Heisenberg nilradical element $N_+(y, z, \xi) = E_{+1}(y, z) + E_{+2}(\xi) \in \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$. -/
def zornHeisenbergNilPlus (y z ξ : R) : ZornVectorMatrix R := ⟨0, ![0, y, z], ![ξ, 0, 0], 0⟩

/-- Positive Heisenberg group element $H_+(y, z, \xi) = 1 + N_+(y, z, \xi) \in \exp(\mathcal{G}_{+1} \oplus \mathcal{G}_{+2})$. -/
def zornHeisenbergGroupPlus (y z ξ : R) : ZornVectorMatrix R := ⟨1, ![0, y, z], ![ξ, 0, 0], 1⟩

/-- Erlangen homogeneous flag state projector $\Pi_{\mathrm{hom}}(v) = \langle 1, -v, 0, 0 \rangle$. -/
def zornHomogeneousFlagState (v : ZornVec3 R) : ZornVectorMatrix R := ⟨1, -v, 0, 0⟩

/-- Helper lemma: product of two elements in the 5-graded positive Heisenberg nilradical $\mathcal{N}_+ = \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$. -/
theorem zornHeisenbergNilPlus_mul (y₁ z₁ ξ₁ y₂ z₂ ξ₂ : R) :
    zornHeisenbergNilPlus y₁ z₁ ξ₁ * zornHeisenbergNilPlus y₂ z₂ ξ₂ =
      zornGradePlus2 (y₁ * z₂ - z₁ * y₂) := by
  ext
  · simp [zornHeisenbergNilPlus, zornGradePlus2, mul, ZornVec3.dot, Fin.sum_univ_three]
  · rename_i i; fin_cases i <;>
      simp [zornHeisenbergNilPlus, zornGradePlus2, mul, ZornVec3.cross]
  · rename_i i; fin_cases i <;>
      (simp [zornHeisenbergNilPlus, zornGradePlus2, mul, ZornVec3.cross]; try ring)
  · simp [zornHeisenbergNilPlus, zornGradePlus2, mul, ZornVec3.dot, Fin.sum_univ_three]

/-- Helper lemma: product of two elements in the 5-graded positive Heisenberg group $\exp(\mathcal{N}_+)$. -/
theorem zornHeisenbergGroupPlus_mul (y₁ z₁ ξ₁ y₂ z₂ ξ₂ : R) :
    zornHeisenbergGroupPlus y₁ z₁ ξ₁ * zornHeisenbergGroupPlus y₂ z₂ ξ₂ =
      zornHeisenbergGroupPlus (y₁ + y₂) (z₁ + z₂) (ξ₁ + ξ₂ + (y₁ * z₂ - z₁ * y₂)) := by
  ext
  · simp [zornHeisenbergGroupPlus, mul, ZornVec3.dot, Fin.sum_univ_three]
  · rename_i i; fin_cases i <;>
      (simp [zornHeisenbergGroupPlus, mul, ZornVec3.cross]; try ring)
  · rename_i i; fin_cases i <;>
      (simp [zornHeisenbergGroupPlus, mul, ZornVec3.cross]; try ring)
  · simp [zornHeisenbergGroupPlus, mul, ZornVec3.dot, Fin.sum_univ_three]

/-- **54. 5-Graded Kantor-Koecher-Tits Contact Structure, Associative Heisenberg Group, & Erlangen Flag States in $\mathrm{Zorn}(R)$**:
    Over any commutative ring $R$:
    1. Step-2 Heisenberg-Contact Grading ($\mathcal{G}_{+1} * \mathcal{G}_{+1} \subseteq \mathcal{G}_{+2}$, $\mathcal{G}_{-1} * \mathcal{G}_{-1} \subseteq \mathcal{G}_{-2}$) & Termination ($\mathcal{G}_{+1} * \mathcal{G}_{+2} = 0$):
       $E_{+1}(y_1, z_1) * E_{+1}(y_2, z_2) = E_{+2}(y_1 z_2 - z_1 y_2)$,
       $E_{-1}(y_1, z_1) * E_{-1}(y_2, z_2) = E_{-2}(-(y_1 z_2 - z_1 y_2))$, and
       $E_{+1}(y, z) * E_{+2}(\xi) = 0$.
    2. Associative Heisenberg Group Law & Inversion on $\exp(\mathcal{G}_{+1} \oplus \mathcal{G}_{+2})$:
       $H_+(y_1, z_1, \xi_1) * H_+(y_2, z_2, \xi_2) = H_+(y_1 + y_2, z_1 + z_2, \xi_1 + \xi_2 + (y_1 z_2 - z_1 y_2))$,
       $\mathrm{bundledAssociator}\;H_1\;H_2\;H_3 = 0$, and $H_1 * H_+(-y_1, -z_1, -\xi_1) = 1$.
    3. Opposite-Grade Contact Lowering ($\mathcal{G}_{+1} \times \mathcal{G}_{-2} \to \mathcal{G}_{-1}$):
       $E_{+1}(y, z) * E_{-2}(\eta) = E_{-1}(z \eta, -y \eta)$.
    4. Erlangen Homogeneous Flag State Orbit & Idempotence:
       $(\langle 1, v, 0, 1 \rangle * \langle 1, 0, 0, 0 \rangle) * \langle 1, -v, 0, 1 \rangle = \Pi_{\mathrm{hom}}(v)$ and
       $\Pi_{\mathrm{hom}}(v) * \Pi_{\mathrm{hom}}(v) = \Pi_{\mathrm{hom}}(v)$. -/
theorem zorn_five_graded_kantor_koecher_and_erlangen_flag_states
    (y z y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ ξ η : R) (v : ZornVec3 R) :
    let H₁ := zornHeisenbergGroupPlus y₁ z₁ ξ₁
    let H₂ := zornHeisenbergGroupPlus y₂ z₂ ξ₂
    let H₃ := zornHeisenbergGroupPlus y₃ z₃ ξ₃
    zornGradePlus1 y₁ z₁ * zornGradePlus1 y₂ z₂ = zornGradePlus2 (y₁ * z₂ - z₁ * y₂) ∧
    zornGradeMinus1 y₁ z₁ * zornGradeMinus1 y₂ z₂ = zornGradeMinus2 (-(y₁ * z₂ - z₁ * y₂)) ∧
    zornGradePlus1 y z * zornGradePlus2 ξ = 0 ∧
    H₁ * H₂ = zornHeisenbergGroupPlus (y₁ + y₂) (z₁ + z₂) (ξ₁ + ξ₂ + (y₁ * z₂ - z₁ * y₂)) ∧
    bundledAssociator H₁ H₂ H₃ = 0 ∧
    H₁ * zornHeisenbergGroupPlus (-y₁) (-z₁) (-ξ₁) = zornGradeZero 1 1 ∧
    zornGradePlus1 y z * zornGradeMinus2 η = zornGradeMinus1 (z * η) (-y * η) ∧
    ((⟨1, v, 0, 1⟩ : ZornVectorMatrix R) * ⟨1, 0, 0, 0⟩) * ⟨1, -v, 0, 1⟩ =
      zornHomogeneousFlagState v ∧
    zornHomogeneousFlagState v * zornHomogeneousFlagState v = zornHomogeneousFlagState v := by
  intro H₁ H₂ H₃
  have hAssocH : (H₁ * H₂) * H₃ = H₁ * (H₂ * H₃) := by
    change (zornHeisenbergGroupPlus y₁ z₁ ξ₁ * zornHeisenbergGroupPlus y₂ z₂ ξ₂) * zornHeisenbergGroupPlus y₃ z₃ ξ₃ =
      zornHeisenbergGroupPlus y₁ z₁ ξ₁ * (zornHeisenbergGroupPlus y₂ z₂ ξ₂ * zornHeisenbergGroupPlus y₃ z₃ ξ₃)
    rw [zornHeisenbergGroupPlus_mul, zornHeisenbergGroupPlus_mul,
        zornHeisenbergGroupPlus_mul, zornHeisenbergGroupPlus_mul]
    ext
    · rfl
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus]; try ring)
    · rfl
  refine ⟨?_, ?_, ?_, zornHeisenbergGroupPlus_mul y₁ z₁ ξ₁ y₂ z₂ ξ₂,
          sub_eq_zero.mpr hAssocH, ?_, ?_, ?_, ?_⟩
  · ext
    · simp [zornGradePlus1, zornGradePlus2, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [zornGradePlus1, zornGradePlus2, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> (simp [zornGradePlus1, zornGradePlus2, mul, ZornVec3.cross]; try ring)
    · simp [zornGradePlus1, zornGradePlus2, mul, ZornVec3.dot]
  · ext
    · simp [zornGradeMinus1, zornGradeMinus2, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> (simp [zornGradeMinus1, zornGradeMinus2, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;> simp [zornGradeMinus1, zornGradeMinus2, mul, ZornVec3.cross]
    · simp [zornGradeMinus1, zornGradeMinus2, mul, ZornVec3.dot]
  · ext
    · simp [zornGradePlus1, zornGradePlus2, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [zornGradePlus1, zornGradePlus2, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [zornGradePlus1, zornGradePlus2, mul, ZornVec3.cross]
    · simp [zornGradePlus1, zornGradePlus2, mul, ZornVec3.dot]
  · change zornHeisenbergGroupPlus y₁ z₁ ξ₁ * zornHeisenbergGroupPlus (-y₁) (-z₁) (-ξ₁) = zornGradeZero 1 1
    rw [zornHeisenbergGroupPlus_mul]
    ext
    · rfl
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus, zornGradeZero]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus, zornGradeZero]; try ring)
    · rfl
  · ext
    · simp [zornGradePlus1, zornGradeMinus2, zornGradeMinus1, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [zornGradePlus1, zornGradeMinus2, zornGradeMinus1, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> (simp [zornGradePlus1, zornGradeMinus2, zornGradeMinus1, mul, ZornVec3.cross]; try ring)
    · simp [zornGradePlus1, zornGradeMinus2, zornGradeMinus1, mul, ZornVec3.dot]
  · ext
    · simp [zornHomogeneousFlagState, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> (simp [zornHomogeneousFlagState, mul, ZornVec3.dot, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHomogeneousFlagState, mul, ZornVec3.dot, ZornVec3.cross]; try ring)
    · simp [zornHomogeneousFlagState, mul, ZornVec3.dot, ZornVec3.cross]
  · ext
    · simp [zornHomogeneousFlagState, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> (simp [zornHomogeneousFlagState, mul, ZornVec3.dot, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHomogeneousFlagState, mul, ZornVec3.dot, ZornVec3.cross]; try ring)
    · simp [zornHomogeneousFlagState, mul, ZornVec3.dot]

/-- Negative Heisenberg nilradical element $N_-(y, z, \eta) = E_{-1}(y, z) + E_{-2}(\eta) \in \mathcal{G}_{-1} \oplus \mathcal{G}_{-2}$. -/
def zornHeisenbergNilMinus (y z η : R) : ZornVectorMatrix R := ⟨0, ![η, 0, 0], ![0, y, z], 0⟩

/-- Negative Heisenberg group element $H_-(y, z, \eta) = 1 + N_-(y, z, \eta) \in \exp(\mathcal{G}_{-1} \oplus \mathcal{G}_{-2})$. -/
def zornHeisenbergGroupMinus (y z η : R) : ZornVectorMatrix R := ⟨1, ![η, 0, 0], ![0, y, z], 1⟩

/-- Helper lemma: product of two elements in the 5-graded negative Heisenberg nilradical $\mathcal{N}_- = \mathcal{G}_{-1} \oplus \mathcal{G}_{-2}$. -/
theorem zornHeisenbergNilMinus_mul (y₁ z₁ η₁ y₂ z₂ η₂ : R) :
    zornHeisenbergNilMinus y₁ z₁ η₁ * zornHeisenbergNilMinus y₂ z₂ η₂ =
      zornGradeMinus2 (-(y₁ * z₂ - z₁ * y₂)) := by
  ext
  · simp [zornHeisenbergNilMinus, zornGradeMinus2, mul, ZornVec3.dot, Fin.sum_univ_three]
  · rename_i i; fin_cases i <;>
      (simp [zornHeisenbergNilMinus, zornGradeMinus2, mul, ZornVec3.cross]; try ring)
  · rename_i i; fin_cases i <;>
      simp [zornHeisenbergNilMinus, zornGradeMinus2, mul, ZornVec3.cross]
  · simp [zornHeisenbergNilMinus, zornGradeMinus2, mul, ZornVec3.dot, Fin.sum_univ_three]

/-- Helper lemma: product of two elements in the 5-graded negative Heisenberg group $\exp(\mathcal{N}_-)$. -/
theorem zornHeisenbergGroupMinus_mul (y₁ z₁ η₁ y₂ z₂ η₂ : R) :
    zornHeisenbergGroupMinus y₁ z₁ η₁ * zornHeisenbergGroupMinus y₂ z₂ η₂ =
      zornHeisenbergGroupMinus (y₁ + y₂) (z₁ + z₂) (η₁ + η₂ - (y₁ * z₂ - z₁ * y₂)) := by
  ext
  · simp [zornHeisenbergGroupMinus, mul, ZornVec3.dot, Fin.sum_univ_three]
  · rename_i i; fin_cases i <;>
      (simp [zornHeisenbergGroupMinus, mul, ZornVec3.cross]; try ring)
  · rename_i i; fin_cases i <;>
      (simp [zornHeisenbergGroupMinus, mul, ZornVec3.cross]; try ring)
  · simp [zornHeisenbergGroupMinus, mul, ZornVec3.dot, Fin.sum_univ_three]

/-- **55. Negative Heisenberg Nilradical $\mathcal{N}_-$, Dual Group Law, & Opposite-Nilradical Nucleus Coupling in $\mathrm{Zorn}(R)$**:
    Over any commutative ring $R$:
    1. Step-2 Negative Nilradical Closure & Associativity:
       $N_-(y_1, z_1, \eta_1) * N_-(y_2, z_2, \eta_2) = E_{-2}(-(y_1 z_2 - z_1 y_2))$ and
       $\mathrm{bundledAssociator}\;H_{-,1}\;H_{-,2}\;H_{-,3} = 0$.
    2. Dual Heisenberg Group Law & Exact Inversion:
       $H_-(y_1, z_1, \eta_1) * H_-(y_2, z_2, \eta_2) = H_-(y_1 + y_2, z_1 + z_2, \eta_1 + \eta_2 - (y_1 z_2 - z_1 y_2))$ and
       $H_{-,1} * H_-(-y_1, -z_1, -\eta_1) = \mathrm{zornGradeZero}\;1\;1$.
    3. Exact $\mathcal{G}_0$ Central Nucleus Closure of the Jordan Anticommutator $\{N_+, N_-\}$:
       $N_+(y_1, z_1, \xi) * N_-(y_2, z_2, \eta) + N_-(y_2, z_2, \eta) * N_+(y_1, z_1, \xi) =
         \mathrm{zornGradeZero}\;(y_1 y_2 + z_1 z_2 + \xi \eta)\;(y_1 y_2 + z_1 z_2 + \xi \eta)$. -/
theorem zorn_negative_nilradical_and_nucleus_coupling
    (y₁ z₁ η₁ y₂ z₂ η₂ y₃ z₃ η₃ ξ η : R) :
    let H₁ := zornHeisenbergGroupMinus y₁ z₁ η₁
    let H₂ := zornHeisenbergGroupMinus y₂ z₂ η₂
    let H₃ := zornHeisenbergGroupMinus y₃ z₃ η₃
    let N_p := zornHeisenbergNilPlus y₁ z₁ ξ
    let N_m := zornHeisenbergNilMinus y₂ z₂ η
    zornHeisenbergNilMinus y₁ z₁ η₁ * zornHeisenbergNilMinus y₂ z₂ η₂ =
      zornGradeMinus2 (-(y₁ * z₂ - z₁ * y₂)) ∧
    H₁ * H₂ = zornHeisenbergGroupMinus (y₁ + y₂) (z₁ + z₂) (η₁ + η₂ - (y₁ * z₂ - z₁ * y₂)) ∧
    bundledAssociator H₁ H₂ H₃ = 0 ∧
    H₁ * zornHeisenbergGroupMinus (-y₁) (-z₁) (-η₁) = zornGradeZero 1 1 ∧
    N_p * N_m + N_m * N_p =
      zornGradeZero (y₁ * y₂ + z₁ * z₂ + ξ * η) (y₁ * y₂ + z₁ * z₂ + ξ * η) := by
  intro H₁ H₂ H₃ N_p N_m
  have hAssocH : (H₁ * H₂) * H₃ = H₁ * (H₂ * H₃) := by
    change (zornHeisenbergGroupMinus y₁ z₁ η₁ * zornHeisenbergGroupMinus y₂ z₂ η₂) * zornHeisenbergGroupMinus y₃ z₃ η₃ =
      zornHeisenbergGroupMinus y₁ z₁ η₁ * (zornHeisenbergGroupMinus y₂ z₂ η₂ * zornHeisenbergGroupMinus y₃ z₃ η₃)
    rw [zornHeisenbergGroupMinus_mul, zornHeisenbergGroupMinus_mul,
        zornHeisenbergGroupMinus_mul, zornHeisenbergGroupMinus_mul]
    ext
    · rfl
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupMinus]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupMinus]; try ring)
    · rfl
  refine ⟨zornHeisenbergNilMinus_mul y₁ z₁ η₁ y₂ z₂ η₂,
          zornHeisenbergGroupMinus_mul y₁ z₁ η₁ y₂ z₂ η₂,
          sub_eq_zero.mpr hAssocH, ?_, ?_⟩
  · change zornHeisenbergGroupMinus y₁ z₁ η₁ * zornHeisenbergGroupMinus (-y₁) (-z₁) (-η₁) = zornGradeZero 1 1
    rw [zornHeisenbergGroupMinus_mul]
    ext
    · rfl
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupMinus, zornGradeZero]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupMinus, zornGradeZero]; try ring)
    · rfl
  · ext
    · simp [N_p, N_m, zornHeisenbergNilPlus, zornHeisenbergNilMinus, zornGradeZero,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]
      try ring
    · rename_i i; fin_cases i <;>
        (simp [N_p, N_m, zornHeisenbergNilPlus, zornHeisenbergNilMinus, zornGradeZero,
               InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [N_p, N_m, zornHeisenbergNilPlus, zornHeisenbergNilMinus, zornGradeZero,
               InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.cross]; try ring)
    · simp [N_p, N_m, zornHeisenbergNilPlus, zornHeisenbergNilMinus, zornGradeZero,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]
      try ring

/-- Positive central contact subgroup $C_+(\xi) := H_+(0, 0, \xi) = \langle 1, 0, \langle \xi, 0, 0 \rangle, 1 \rangle \in \mathrm{Zorn}(R)$. -/
def zornContactSubgroupPlus (ξ : R) : ZornVectorMatrix R :=
  zornHeisenbergGroupPlus 0 0 ξ

/-- Negative central contact subgroup $C_-(\eta) := H_-(0, 0, \eta) = \langle 1, \langle \eta, 0, 0 \rangle, 0, 1 \rangle \in \mathrm{Zorn}(R)$. -/
def zornContactSubgroupMinus (η : R) : ZornVectorMatrix R :=
  zornHeisenbergGroupMinus 0 0 η

/-- **56. 5-Grade Nucleus Derivation Invariance, Central Contact Subgroup Readout, & Contact-Gauss Associativity in $\mathrm{Zorn}(R)$**:
    Over any commutative ring $R$, for all $\rho_+, \rho_-, y, z, \xi, \xi', \eta, \eta' \in R$:
    1. 5-Grade Eigenvalue Invariance Under $D = \mathrm{zornGradeZero}\;\rho_+\;\rho_-$:
       $$D * E_{+1}(y, z) - E_{+1}(y, z) * D = (\rho_+ - \rho_-) \cdot E_{+1}(y, z), \qquad
         D * E_{+2}(\xi) - E_{+2}(\xi) * D = (\rho_- - \rho_+) \cdot E_{+2}(\xi).$$
    2. Exact Centrality of Contact Subgroups $C_+(\xi')$ and $C_-(\eta')$:
       $$H_+(y, z, \xi) * C_+(\xi') = C_+(\xi') * H_+(y, z, \xi) = H_+(y, z, \xi + \xi'),$$
       $$H_-(y, z, \eta) * C_-(\eta') = C_-(\eta') * H_-(y, z, \eta) = H_-(y, z, \eta + \eta').$$
    3. Selective Contact Readout & Contact-Gauss Associativity:
       $$E_{-2}(\eta) * (E_{-1}(y, z) + E_{+2}(\xi)) = \mathrm{zornGradeZero}\;(\eta \xi)\;0,$$
       $$\mathrm{bundledAssociator}\;(C_+(\xi))\;(\mathrm{zornGradeZero}\;\rho_+\;\rho_-)\;(C_-(\eta)) = 0.$$ -/
theorem zorn_five_graded_nucleus_invariance_and_contact_centrality
    (ρ_plus ρ_minus y z ξ ξ' η η' : R) :
    let D := zornGradeZero ρ_plus ρ_minus
    D * zornGradePlus1 y z - zornGradePlus1 y z * D =
      zornGradePlus1 ((ρ_plus - ρ_minus) * y) ((ρ_plus - ρ_minus) * z) ∧
    D * zornGradePlus2 ξ - zornGradePlus2 ξ * D =
      zornGradePlus2 ((ρ_minus - ρ_plus) * ξ) ∧
    zornHeisenbergGroupPlus y z ξ * zornContactSubgroupPlus ξ' =
      zornHeisenbergGroupPlus y z (ξ + ξ') ∧
    zornContactSubgroupPlus ξ' * zornHeisenbergGroupPlus y z ξ =
      zornHeisenbergGroupPlus y z (ξ + ξ') ∧
    zornHeisenbergGroupMinus y z η * zornContactSubgroupMinus η' =
      zornHeisenbergGroupMinus y z (η + η') ∧
    zornContactSubgroupMinus η' * zornHeisenbergGroupMinus y z η =
      zornHeisenbergGroupMinus y z (η + η') ∧
    zornGradeMinus2 η * (zornGradeMinus1 y z + zornGradePlus2 ξ) =
      zornGradeZero (η * ξ) 0 ∧
    bundledAssociator (zornContactSubgroupPlus ξ) D (zornContactSubgroupMinus η) = 0 := by
  intro D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply sub_eq_iff_eq_add.mpr
    ext
    · simp [D, zornGradeZero, zornGradePlus1,
            InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [D, zornGradeZero, zornGradePlus1,
               InfoGeometry.Algebra.zvm_add_def,
               add, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        simp [D, zornGradeZero, zornGradePlus1,
              InfoGeometry.Algebra.zvm_add_def,
              add, mul, ZornVec3.cross]
    · simp [D, zornGradeZero, zornGradePlus1,
            InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot]
  · apply sub_eq_iff_eq_add.mpr
    ext
    · simp [D, zornGradeZero, zornGradePlus2,
            InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        simp [D, zornGradeZero, zornGradePlus2,
              InfoGeometry.Algebra.zvm_add_def,
              add, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;>
        (simp [D, zornGradeZero, zornGradePlus2,
               InfoGeometry.Algebra.zvm_add_def,
               add, mul, ZornVec3.cross]; try ring)
    · simp [D, zornGradeZero, zornGradePlus2,
            InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot]
  · change zornHeisenbergGroupPlus y z ξ * zornHeisenbergGroupPlus 0 0 ξ' =
      zornHeisenbergGroupPlus y z (ξ + ξ')
    rw [zornHeisenbergGroupPlus_mul]
    ext
    · rfl
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus]; try ring)
    · rfl
  · change zornHeisenbergGroupPlus 0 0 ξ' * zornHeisenbergGroupPlus y z ξ =
      zornHeisenbergGroupPlus y z (ξ + ξ')
    rw [zornHeisenbergGroupPlus_mul]
    ext
    · rfl
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus]; try ring)
    · rfl
  · change zornHeisenbergGroupMinus y z η * zornHeisenbergGroupMinus 0 0 η' =
      zornHeisenbergGroupMinus y z (η + η')
    rw [zornHeisenbergGroupMinus_mul]
    ext
    · rfl
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupMinus]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupMinus]; try ring)
    · rfl
  · change zornHeisenbergGroupMinus 0 0 η' * zornHeisenbergGroupMinus y z η =
      zornHeisenbergGroupMinus y z (η + η')
    rw [zornHeisenbergGroupMinus_mul]
    ext
    · rfl
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupMinus]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupMinus]; try ring)
    · rfl
  · ext
    · simp [zornGradeMinus2, zornGradeMinus1, zornGradePlus2, zornGradeZero,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        simp [zornGradeMinus2, zornGradeMinus1, zornGradePlus2, zornGradeZero,
              InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;>
        simp [zornGradeMinus2, zornGradeMinus1, zornGradePlus2, zornGradeZero,
              InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.cross]
    · simp [zornGradeMinus2, zornGradeMinus1, zornGradePlus2, zornGradeZero,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]
  · apply sub_eq_zero.mpr
    ext
    · simp [D, zornContactSubgroupPlus, zornContactSubgroupMinus,
            zornHeisenbergGroupPlus, zornHeisenbergGroupMinus, zornGradeZero,
            mul, ZornVec3.dot, Fin.sum_univ_three]
      try ring
    · rename_i i; fin_cases i <;>
        (simp [D, zornContactSubgroupPlus, zornContactSubgroupMinus,
               zornHeisenbergGroupPlus, zornHeisenbergGroupMinus, zornGradeZero,
               mul, ZornVec3.dot, Fin.sum_univ_three, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [D, zornContactSubgroupPlus, zornContactSubgroupMinus,
               zornHeisenbergGroupPlus, zornHeisenbergGroupMinus, zornGradeZero,
               mul, ZornVec3.dot, Fin.sum_univ_three, ZornVec3.cross]; try ring)
    · simp [D, zornContactSubgroupPlus, zornContactSubgroupMinus,
            zornHeisenbergGroupPlus, zornHeisenbergGroupMinus, zornGradeZero,
            mul, ZornVec3.dot, Fin.sum_univ_three]
      try ring

/-- Transverse Erlangen flag state $\Pi_\perp(y, z) := \langle 1, ![0, -y, -z], 0, 0 \rangle \in \mathrm{Zorn}(R)$. -/
def zornTransverseFlagState (y z : R) : ZornVectorMatrix R :=
  ⟨1, ![0, -y, -z], 0, 0⟩

/-- Transverse BCFW shift operator $S_+(y_s, z_s) := \mathrm{zornHeisenbergGroupPlus}\;y_s\;z_s\;0 = \langle 1, ![0, y_s, z_s], 0, 1 \rangle \in \mathrm{Zorn}(R)$. -/
def zornBCFWShift (y_s z_s : R) : ZornVectorMatrix R :=
  zornHeisenbergGroupPlus y_s z_s 0

/-- **57. 5-Graded BCFW Transverse Shift, Symplectic Contact Residue, & Dual Probe Readout in $\mathrm{Zorn}(R)$ (Archetype XLIX)**:
    Over any commutative ring $R$, for all $y_0, z_0, y_s, z_s, \eta \in R$:
    1. Vanishing BCFW Shift Associator:
       $$\mathrm{bundledAssociator}\;(\mathrm{zornBCFWShift}\;y_s\;z_s)\;(\mathrm{zornTransverseFlagState}\;y_0\;z_0)\;(\mathrm{zornBCFWShift}\;(-y_s)\;(-z_s)) = 0.$$
    2. Exact Right BCFW Shift & Symplectic Contact Residue Factorization:
       $$\Pi_\perp(y_0, z_0) * S_+(-y_s, -z_s) = \Pi_\perp(y_s + y_0, z_s + z_0) + E_{+2}(-(y_s z_0 - z_s y_0)).$$
    3. Exact Two-Sided BCFW Conjugation Shift:
       $$(S_+(y_s, z_s) * \Pi_\perp(y_0, z_0)) * S_+(-y_s, -z_s) = \Pi_\perp(y_s + y_0, z_s + z_0) + E_{+2}(-2 (y_s z_0 - z_s y_0)).$$
    4. Direct Dual Contact Probe Readout of the BCFW Symplectic Residue:
       $$E_{-2}(\eta) * E_{+2}(-(y_s z_0 - z_s y_0)) = \mathrm{zornGradeZero}\;(-\eta (y_s z_0 - z_s y_0))\;0.$$ -/
theorem zorn_five_graded_bcfw_shift_and_contact_residue
    (y₀ z₀ y_s z_s η : R) :
    let P₀ := zornTransverseFlagState y₀ z₀
    let P_shifted := zornTransverseFlagState (y_s + y₀) (z_s + z₀)
    let S_plus := zornBCFWShift y_s z_s
    let S_minus := zornBCFWShift (-y_s) (-z_s)
    let ω_res := y_s * z₀ - z_s * y₀
    bundledAssociator S_plus P₀ S_minus = 0 ∧
    P₀ * S_minus = P_shifted + zornGradePlus2 (-ω_res) ∧
    (S_plus * P₀) * S_minus = P_shifted + zornGradePlus2 (-(2 * ω_res)) ∧
    zornGradeMinus2 η * zornGradePlus2 (-ω_res) =
      zornGradeZero (-η * ω_res) 0 := by
  intro P₀ P_shifted S_plus S_minus ω_res
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply sub_eq_zero.mpr
    ext
    · simp [P₀, S_plus, S_minus, zornTransverseFlagState, zornBCFWShift,
            zornHeisenbergGroupPlus, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        (simp [P₀, S_plus, S_minus, zornTransverseFlagState, zornBCFWShift,
               zornHeisenbergGroupPlus, mul, ZornVec3.dot, Fin.sum_univ_three, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [P₀, S_plus, S_minus, zornTransverseFlagState, zornBCFWShift,
               zornHeisenbergGroupPlus, mul, ZornVec3.dot, Fin.sum_univ_three, ZornVec3.cross]; try ring)
    · simp [P₀, S_plus, S_minus, zornTransverseFlagState, zornBCFWShift,
            zornHeisenbergGroupPlus, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [P₀, P_shifted, S_minus, zornTransverseFlagState, zornBCFWShift,
            zornHeisenbergGroupPlus, zornGradePlus2,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        (simp [P₀, P_shifted, S_minus, zornTransverseFlagState, zornBCFWShift,
               zornHeisenbergGroupPlus, zornGradePlus2,
               InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [P₀, P_shifted, S_minus, zornTransverseFlagState, zornBCFWShift,
               zornHeisenbergGroupPlus, zornGradePlus2, ω_res,
               InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.cross]; try ring)
    · simp [P₀, P_shifted, S_minus, zornTransverseFlagState, zornBCFWShift,
            zornHeisenbergGroupPlus, zornGradePlus2,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [P₀, P_shifted, S_plus, S_minus, zornTransverseFlagState, zornBCFWShift,
            zornHeisenbergGroupPlus, zornGradePlus2,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        (simp [P₀, P_shifted, S_plus, S_minus, zornTransverseFlagState, zornBCFWShift,
               zornHeisenbergGroupPlus, zornGradePlus2,
               InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [P₀, P_shifted, S_plus, S_minus, zornTransverseFlagState, zornBCFWShift,
               zornHeisenbergGroupPlus, zornGradePlus2, ω_res,
               InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three, ZornVec3.cross]; try ring)
    · simp [P₀, P_shifted, S_plus, S_minus, zornTransverseFlagState, zornBCFWShift,
            zornHeisenbergGroupPlus, zornGradePlus2,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [zornGradeMinus2, zornGradePlus2, zornGradeZero, mul, ZornVec3.dot, Fin.sum_univ_three]
      try ring
    · rename_i i; fin_cases i <;>
        simp [zornGradeMinus2, zornGradePlus2, zornGradeZero, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;>
        simp [zornGradeMinus2, zornGradePlus2, zornGradeZero, mul, ZornVec3.cross]
    · simp [zornGradeMinus2, zornGradePlus2, zornGradeZero, mul, ZornVec3.dot, Fin.sum_univ_three]

/-- **58. Unified Three-Arnold Synthesis in $\mathrm{Zorn}(R)$: 3-Layer KAN Superposition, 4-Gate Braid Monodromy Loop, & Beltrami Lamb Vanishing**:
    Over any commutative ring $R$, for all $y_i, z_i, \xi_i, \eta, \xi \in R$ and $u \in \mathrm{ZornVec3}\;R$:
    1. 3-Layer KAN + Symplectic Braid Composition:
       $$(H_+(y_1, z_1, \xi_1) * H_+(y_2, z_2, \xi_2)) * H_+(y_3, z_3, \xi_3) =
         H_+\!\bigl(y_1 + y_2 + y_3,\; z_1 + z_2 + z_3,\;
                    \xi_1 + \xi_2 + \xi_3 + (y_1 z_2 - z_1 y_2) + ((y_1 + y_2) z_3 - (z_1 + z_2) y_3)\bigr).$$
    2. 4-Gate Braid Group Commutator Loop (Pure Contact Phase Monodromy):
       $$(H_+(y_1, z_1, \xi_1) * H_+(y_2, z_2, \xi_2)) *
         (H_+(-y_1, -z_1, -\xi_1) * H_+(-y_2, -z_2, -\xi_2)) =
         \mathrm{zornContactSubgroupPlus}\;(2 (y_1 z_2 - z_1 y_2)).$$
    3. Beltrami Lamb Vector Vanishing & Helicity Casimir Identity:
       $$\langle 0, u, 0, 0 \rangle * \langle 0, u, 0, 0 \rangle = 0 \qquad \text{and} \qquad
         \langle 0, u, 0, 0 \rangle * \langle 0, 0, u, 0 \rangle +
         \langle 0, 0, u, 0 \rangle * \langle 0, u, 0, 0 \rangle =
         \mathrm{zornGradeZero}\;(u \cdot u)\;(u \cdot u).$$ -/
theorem zorn_unified_three_arnold_kan_braid_and_beltrami
    (y₁ z₁ ξ₁ y₂ z₂ ξ₂ y₃ z₃ ξ₃ : R) (u : ZornVec3 R) :
    let G₁ := zornHeisenbergGroupPlus y₁ z₁ ξ₁
    let G₂ := zornHeisenbergGroupPlus y₂ z₂ ξ₂
    let G₃ := zornHeisenbergGroupPlus y₃ z₃ ξ₃
    let G₁_inv := zornHeisenbergGroupPlus (-y₁) (-z₁) (-ξ₁)
    let G₂_inv := zornHeisenbergGroupPlus (-y₂) (-z₂) (-ξ₂)
    let ω₁₂ := y₁ * z₂ - z₁ * y₂
    let ω₁₂_₃ := (y₁ + y₂) * z₃ - (z₁ + z₂) * y₃
    let Lu_p : ZornVectorMatrix R := ⟨0, u, 0, 0⟩
    let Lu_m : ZornVectorMatrix R := ⟨0, 0, u, 0⟩
    (G₁ * G₂) * G₃ =
      zornHeisenbergGroupPlus (y₁ + y₂ + y₃) (z₁ + z₂ + z₃) (ξ₁ + ξ₂ + ξ₃ + ω₁₂ + ω₁₂_₃) ∧
    (G₁ * G₂) * (G₁_inv * G₂_inv) = zornContactSubgroupPlus (2 * ω₁₂) ∧
    Lu_p * Lu_p = 0 ∧
    Lu_p * Lu_m + Lu_m * Lu_p = zornGradeZero (ZornVec3.dot u u) (ZornVec3.dot u u) := by
  intro G₁ G₂ G₃ G₁_inv G₂_inv ω₁₂ ω₁₂_₃ Lu_p Lu_m
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (zornHeisenbergGroupPlus y₁ z₁ ξ₁ * zornHeisenbergGroupPlus y₂ z₂ ξ₂) *
        zornHeisenbergGroupPlus y₃ z₃ ξ₃ =
      zornHeisenbergGroupPlus (y₁ + y₂ + y₃) (z₁ + z₂ + z₃) (ξ₁ + ξ₂ + ξ₃ + ω₁₂ + ω₁₂_₃)
    rw [zornHeisenbergGroupPlus_mul, zornHeisenbergGroupPlus_mul]
    ext
    · rfl
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus, ω₁₂, ω₁₂_₃]; try ring)
    · rfl
  · change (zornHeisenbergGroupPlus y₁ z₁ ξ₁ * zornHeisenbergGroupPlus y₂ z₂ ξ₂) *
        (zornHeisenbergGroupPlus (-y₁) (-z₁) (-ξ₁) * zornHeisenbergGroupPlus (-y₂) (-z₂) (-ξ₂)) =
      zornContactSubgroupPlus (2 * ω₁₂)
    rw [zornHeisenbergGroupPlus_mul, zornHeisenbergGroupPlus_mul, zornHeisenbergGroupPlus_mul]
    ext
    · rfl
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus, zornContactSubgroupPlus]; try ring)
    · rename_i i; fin_cases i <;> (simp [zornHeisenbergGroupPlus, zornContactSubgroupPlus, ω₁₂]; try ring)
    · rfl
  · ext
    · simp [Lu_p, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [Lu_p, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> (simp [Lu_p, mul, ZornVec3.cross]; try ring)
    · simp [Lu_p, mul, ZornVec3.dot]
  · ext
    · simp [Lu_p, Lu_m, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        simp [Lu_p, Lu_m, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
              add, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;>
        simp [Lu_p, Lu_m, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
              add, mul, ZornVec3.cross]
    · simp [Lu_p, Lu_m, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot, Fin.sum_univ_three]

/-! ## Section 59: Universal 3D Zorn Lamb-Velocity & Lamb-Vorticity Nilpotence (Archetype LIV.4) -/

/-- **Universal 3D Zorn Lamb-Velocity & Lamb-Vorticity Nilpotence (Archetype LIV.4)**:
    Over any commutative ring $R$ (`[CommRing R]`), for *arbitrary* full 3D velocity and vorticity
    vectors $u, \omega \in \mathrm{ZornVec3}\;R$, let $U = \langle 0, u, 0, 0 \rangle$ and
    $\Omega = \langle 0, \omega, 0, 0 \rangle$ so that $\Omega * U = \langle 0, 0, 2(\omega \times u), 0 \rangle$:
    1. Exact 3D Lamb-Velocity Work Vanishing ($u \cdot (\omega \times u) = 0$):
       $$U * (\Omega * U) = 0 \qquad \text{and} \qquad (\Omega * U) * U = 0.$$
    2. Exact 3D Lamb-Vorticity Self-Advection Vanishing ($\omega \cdot (\omega \times u) = 0$):
       $$\Omega * (\Omega * U) = 0 \qquad \text{and} \qquad (\Omega * U) * \Omega = 0.$$ -/
theorem zorn_threeDim_lamb_velocity_and_vorticity_annihilation
    (u ω : ZornVec3 R) :
    let U : ZornVectorMatrix R := ⟨0, u, 0, 0⟩
    let Ω : ZornVectorMatrix R := ⟨0, ω, 0, 0⟩
    U * (Ω * U) = 0 ∧
    (Ω * U) * U = 0 ∧
    Ω * (Ω * U) = 0 ∧
    (Ω * U) * Ω = 0 := by
  intro U Ω
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext
    · simp [U, Ω, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;> simp [U, Ω, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [U, Ω, mul, ZornVec3.cross]
    · simp [U, Ω, mul, ZornVec3.dot]
  · ext
    · simp [U, Ω, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [U, Ω, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [U, Ω, mul, ZornVec3.cross]
    · simp [U, Ω, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
  · ext
    · simp [U, Ω, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;> simp [U, Ω, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [U, Ω, mul, ZornVec3.cross]
    · simp [U, Ω, mul, ZornVec3.dot]
  · ext
    · simp [U, Ω, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [U, Ω, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [U, Ω, mul, ZornVec3.cross]
    · simp [U, Ω, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; ring

/-! ## Section 60: Madelung QGT Split, Metriplectic Chiral Factorization, & Beltrami Helicity Dissipation (Archetypes LV–LVII) -/

/-- **Madelung QGT Metric-Berry Split, Metriplectic Chiral Factorization, & Navier–Stokes Beltrami Helicity Dissipation (Archetypes LV–LVII)**:
    Over any commutative ring $R$ (`[CommRing R]`):
    1. Quantum Geometric Tensor Metric-Berry Split ($Q(v, w) = 2(L_+(v) * L_-(w))$):
       $$L_+(v) * L_-(w) + L_+(v) * L_-(w) = (L_+(v) * L_-(w) + L_-(w) * L_+(v)) + (L_+(v) * L_-(w) + -(L_-(w) * L_+(v))).$$
    2. Metriplectic Chiral Left-Right Factorization ($H = \mathrm{zornGradeZero}\;h_+\;h_-$, $S = \mathrm{zornGradeZero}\;\nu_+\;\nu_-$):
       $$(H * X + -(X * H)) + (S * X + X * S) = (H + S) * X + X * (S + -H).$$
    3. Beltrami Collinear Lamb Vanishing, Helicity Casimir, & Viscous Helicity Dissipation Rate ($\omega = \lambda \bullet u$):
       $$\langle 0, \lambda \bullet u, 0, 0 \rangle * \langle 0, u, 0, 0 \rangle = 0,$$
       $$\{L_+(u), L_-(\lambda \bullet u)\} = \mathrm{zornGradeZero}\;(\lambda (u \cdot u))\;(\lambda (u \cdot u)),$$
       $$\{(S_{\mathrm{visc}} * L_+(u)), L_-(\lambda \bullet u)\} + \{L_+(u), (S_{\mathrm{visc}} * L_-(\lambda \bullet u))\} =
         \mathrm{zornGradeZero}\;(-(2 \nu \lambda^2))\;(-(2 \nu \lambda^2)) * \{L_+(u), L_-(\lambda \bullet u)\}.$$ -/
theorem zorn_qgt_metriplectic_and_beltrami_helicity_dissipation
    (h_plus h_minus ν_plus ν_minus ν lam : R) (v w u : ZornVec3 R) (X : ZornVectorMatrix R) :
    let Lp : ZornVectorMatrix R := ⟨0, v, 0, 0⟩
    let Lm : ZornVectorMatrix R := ⟨0, 0, w, 0⟩
    let H := zornGradeZero h_plus h_minus
    let S := zornGradeZero ν_plus ν_minus
    let U_p : ZornVectorMatrix R := ⟨0, u, 0, 0⟩
    let Ω_p : ZornVectorMatrix R := ⟨0, lam • u, 0, 0⟩
    let Ω_m : ZornVectorMatrix R := ⟨0, 0, lam • u, 0⟩
    let S_visc := zornGradeZero (-(ν * (lam * lam))) (-(ν * (lam * lam)))
    let H_hel := U_p * Ω_m + Ω_m * U_p
    Lp * Lm + Lp * Lm = (Lp * Lm + Lm * Lp) + (Lp * Lm + -(Lm * Lp)) ∧
    (H * X + -(X * H)) + (S * X + X * S) = (H + S) * X + X * (S + -H) ∧
    Ω_p * U_p = 0 ∧
    H_hel = zornGradeZero (lam * ZornVec3.dot u u) (lam * ZornVec3.dot u u) ∧
    ((S_visc * U_p) * Ω_m + Ω_m * (S_visc * U_p)) +
      (U_p * (S_visc * Ω_m) + (S_visc * Ω_m) * U_p) =
      zornGradeZero (-(2 * ν * (lam * lam))) (-(2 * ν * (lam * lam))) * H_hel := by
  intro Lp Lm H S U_p Ω_p Ω_m S_visc H_hel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · abel
  · ext
    · simp [H, S, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.dot]; ring
    · rename_i i; fin_cases i <;>
        (simp [H, S, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [H, S, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
               InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.cross]; try ring)
    · simp [H, S, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.dot]; ring
  · ext
    · simp [U_p, Ω_p, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [U_p, Ω_p, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> (simp [U_p, Ω_p, mul, ZornVec3.cross]; try ring)
    · simp [U_p, Ω_p, mul, ZornVec3.dot]
  · ext
    · simp [H_hel, U_p, Ω_m, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        simp [H_hel, U_p, Ω_m, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
              add, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;>
        simp [H_hel, U_p, Ω_m, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
              add, mul, ZornVec3.cross]
    · simp [H_hel, U_p, Ω_m, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
  · ext
    · simp [H_hel, S_visc, U_p, Ω_m, zornGradeZero,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [H_hel, S_visc, U_p, Ω_m, zornGradeZero,
               InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, ZornVec3.cross,
               Fin.sum_univ_three]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [H_hel, S_visc, U_p, Ω_m, zornGradeZero,
               InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, ZornVec3.cross,
               Fin.sum_univ_three]; try ring)
    · simp [H_hel, S_visc, U_p, Ω_m, zornGradeZero,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]; ring

/-! ## Section 61: Quark–Diquark–Meson–Baryon Color Confinement into the $\mathcal{G}_0$ Associative Nucleus (Archetype LIX) -/

/-- **Quark–Diquark Anti-Triplet Pairing & Meson/Baryon Color Confinement into $\mathcal{G}_0$ (Archetype LIX)**:
    Over any commutative ring $R$ (`[CommRing R]`), for all 3-color quark vectors $v, v_1, v_2, v_3 \in \mathrm{ZornVec3}\;R$
    and antiquark vector $w \in \mathrm{ZornVec3}\;R$:
    1. Quark $\times$ Quark $\to$ Diquark Anti-Triplet:
       $$\langle 0, v_1, 0, 0 \rangle * \langle 0, v_2, 0, 0 \rangle = \langle 0, 0, v_1 \times v_2, 0 \rangle.$$
    2. Meson Singlet Lands in the Grade-0 Associative Nucleus $\mathcal{G}_0$:
       $$\langle 0, v, 0, 0 \rangle * \langle 0, 0, w, 0 \rangle + \langle 0, 0, w, 0 \rangle * \langle 0, v, 0, 0 \rangle =
         \mathrm{zornGradeZero}\;(v \cdot w)\;(w \cdot v).$$
    3. 3-Quark Baryon Associator Lands in the Grade-0 Associative Nucleus $\mathcal{G}_0$:
       $$(\langle 0, v_1, 0, 0 \rangle * \langle 0, v_2, 0, 0 \rangle) * \langle 0, v_3, 0, 0 \rangle +
         -(\langle 0, v_1, 0, 0 \rangle * (\langle 0, v_2, 0, 0 \rangle * \langle 0, v_3, 0, 0 \rangle)) =
         \mathrm{zornGradeZero}\;(-(v_1 \cdot (v_2 \times v_3)))\;((v_1 \times v_2) \cdot v_3).$$ -/
theorem zorn_baryon_meson_singlet_nucleus_confinement
    (v w v₁ v₂ v₃ : ZornVec3 R) :
    let Qv : ZornVectorMatrix R := ⟨0, v, 0, 0⟩
    let Qw : ZornVectorMatrix R := ⟨0, 0, w, 0⟩
    let Q₁ : ZornVectorMatrix R := ⟨0, v₁, 0, 0⟩
    let Q₂ : ZornVectorMatrix R := ⟨0, v₂, 0, 0⟩
    let Q₃ : ZornVectorMatrix R := ⟨0, v₃, 0, 0⟩
    Q₁ * Q₂ = ⟨0, 0, ZornVec3.cross v₁ v₂, 0⟩ ∧
    Qv * Qw + Qw * Qv = zornGradeZero (ZornVec3.dot v w) (ZornVec3.dot w v) ∧
    (Q₁ * Q₂) * Q₃ + -(Q₁ * (Q₂ * Q₃)) =
      zornGradeZero (-ZornVec3.dot v₁ (ZornVec3.cross v₂ v₃))
                    (ZornVec3.dot (ZornVec3.cross v₁ v₂) v₃) ∧
    (Q₁ * Q₂) * Q₃ + -(Q₁ * (Q₂ * Q₃)) =
      -((Q₂ * Q₁) * Q₃ + -(Q₂ * (Q₁ * Q₃))) ∧
    (Q₁ * Q₁) * Q₃ + -(Q₁ * (Q₁ * Q₃)) = 0 := by
  intro Qv Qw Q₁ Q₂ Q₃
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext
    · simp [Q₁, Q₂, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [Q₁, Q₂, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> (simp [Q₁, Q₂, mul, ZornVec3.cross]; try ring)
    · simp [Q₁, Q₂, mul, ZornVec3.dot]
  · ext
    · simp [Qv, Qw, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        simp [Qv, Qw, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
              add, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;>
        simp [Qv, Qw, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
              add, mul, ZornVec3.cross]
    · simp [Qv, Qw, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [Q₁, Q₂, Q₃, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, add, neg, mul,
            ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        simp [Q₁, Q₂, Q₃, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
              InfoGeometry.Algebra.zvm_neg_def, add, neg, mul,
              ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        simp [Q₁, Q₂, Q₃, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
              InfoGeometry.Algebra.zvm_neg_def, add, neg, mul,
              ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · simp [Q₁, Q₂, Q₃, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            InfoGeometry.Algebra.zvm_neg_def, add, neg, mul,
            ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  · change bundledAssociator Q₁ Q₂ Q₃ = -bundledAssociator Q₂ Q₁ Q₃
    exact bundledAssociator_swap12 Q₁ Q₂ Q₃
  · change bundledAssociator Q₁ Q₁ Q₃ = 0
    exact bundledAssociator_left_alt Q₁ Q₃

/-! ## Section 62: Master Trifactor Wavefunction Factorization & 4-Factor Associative Square (Archetype LX) -/

/-- **Chiral Wavefunction Factors $\Psi_L(w) = \langle 1, 0, w, 0 \rangle$, $\Psi_R(v) = \langle 1, v, 0, 0 \rangle$ & 4-Factor Associative Square (Archetype LX)**:
    Over any commutative ring $R$ (`[CommRing R]`), for all 3-vectors $v, w \in \mathrm{ZornVec3}\;R$,
    let $\Psi_L = \langle 1, 0, w, 0 \rangle$, $\Psi_R = \langle 1, v, 0, 0 \rangle$, and $\Pi = \Psi_L * \Psi_R$:
    1. Exact Idempotence of Chiral Wavefunction Factors:
       $$\Psi_L * \Psi_L = \Psi_L \qquad \text{and} \qquad \Psi_R * \Psi_R = \Psi_R.$$
    2. Inner vs. Outer Contractions:
       $$\Psi_R * \Psi_L = \mathrm{zornGradeZero}\;(1 + v \cdot w)\;0 \qquad \text{and} \qquad
         \Pi = \langle 1, v, w, w \cdot v \rangle.$$
    3. Exact Vanishing of Sandwich Associators & 4-Factor Associative Square Law:
       $$(\Psi_R * \Psi_L) * \Psi_R + -(\Psi_R * (\Psi_L * \Psi_R)) = 0, \qquad
         (\Psi_L * \Psi_R) * \Psi_L + -(\Psi_L * (\Psi_R * \Psi_L)) = 0,$$
       $$\Pi * \Pi = \Psi_L * ((\Psi_R * \Psi_L) * \Psi_R).$$ -/
theorem zorn_trifactor_wavefunction_and_contact_idempotent
    (w v : ZornVec3 R) :
    let Ψ_L : ZornVectorMatrix R := ⟨1, 0, w, 0⟩
    let Ψ_R : ZornVectorMatrix R := ⟨1, v, 0, 0⟩
    let Pi_tri : ZornVectorMatrix R := Ψ_L * Ψ_R
    Ψ_L * Ψ_L = Ψ_L ∧
    Ψ_R * Ψ_R = Ψ_R ∧
    Ψ_R * Ψ_L = zornGradeZero (1 + ZornVec3.dot v w) 0 ∧
    Pi_tri = ⟨1, v, w, ZornVec3.dot w v⟩ ∧
    (Ψ_R * Ψ_L) * Ψ_R + -(Ψ_R * (Ψ_L * Ψ_R)) = 0 ∧
    (Ψ_L * Ψ_R) * Ψ_L + -(Ψ_L * (Ψ_R * Ψ_L)) = 0 ∧
    Pi_tri * Pi_tri = Ψ_L * ((Ψ_R * Ψ_L) * Ψ_R) := by
  intro Ψ_L Ψ_R Pi_tri
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext
    · simp [Ψ_L, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> (simp [Ψ_L, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;> (simp [Ψ_L, mul, ZornVec3.cross]; try ring)
    · simp [Ψ_L, mul, ZornVec3.dot]
  · ext
    · simp [Ψ_R, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> (simp [Ψ_R, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;> (simp [Ψ_R, mul, ZornVec3.cross]; try ring)
    · simp [Ψ_R, mul, ZornVec3.dot]
  · ext
    · simp [Ψ_L, Ψ_R, zornGradeZero, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> (simp [Ψ_L, Ψ_R, zornGradeZero, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;> (simp [Ψ_L, Ψ_R, zornGradeZero, mul, ZornVec3.cross]; try ring)
    · simp [Ψ_L, Ψ_R, zornGradeZero, mul, ZornVec3.dot]
  · ext
    · simp [Pi_tri, Ψ_L, Ψ_R, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> (simp [Pi_tri, Ψ_L, Ψ_R, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;> (simp [Pi_tri, Ψ_L, Ψ_R, mul, ZornVec3.cross]; try ring)
    · simp [Pi_tri, Ψ_L, Ψ_R, mul, ZornVec3.dot]
  · change bundledAssociator Ψ_R Ψ_L Ψ_R = 0
    exact bundledAssociator_flexible Ψ_R Ψ_L
  · change bundledAssociator Ψ_L Ψ_R Ψ_L = 0
    exact bundledAssociator_flexible Ψ_L Ψ_R
  · ext
    · simp [Pi_tri, Ψ_L, Ψ_R, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [Pi_tri, Ψ_L, Ψ_R, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [Pi_tri, Ψ_L, Ψ_R, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · simp [Pi_tri, Ψ_L, Ψ_R, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring

/-! ## Section 63: The 1934 Jordan–von Neumann–Wigner Fundamental Axiom (III) & Theorem 12 Off-Diagonal Balance on `ZornVectorMatrix R` (Archetypes LXI & LXII) -/

/-- Unscaled Jordan product $X \circ Y = X * Y + Y * X$ on `ZornVectorMatrix R` (JvNW 1934, Page 29). -/
noncomputable def zornJordan (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  X * Y + Y * X

/-- Jordan associator $[X, Y, Z]_J = (X \circ Y) \circ Z + -(X \circ (Y \circ Z))$ on `ZornVectorMatrix R` (JvNW 1934, Page 31, Eq. 1). -/
noncomputable def zornJordanAssoc (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  zornJordan (zornJordan X Y) Z + -(zornJordan X (zornJordan Y Z))

private lemma bundledAssociator_sq_left_right (A B : ZornVectorMatrix R) :
    bundledAssociator (A * A) B A = 0 := by
  rw [bundledAssociator_mul_right A A B, bundledAssociator_left_alt A B]
  exact zero_mul A

private lemma sq_mul_comm_self (A : ZornVectorMatrix R) :
    (A * A) * A = A * (A * A) := by
  exact sub_eq_zero.mp (bundledAssociator_left_alt A A)

private lemma mul_sq_right_assoc (A B : ZornVectorMatrix R) :
    (A * A) * (B * A) = ((A * A) * B) * A := by
  exact (sub_eq_zero.mp (bundledAssociator_sq_left_right A B)).symm

private lemma mul_sq_mid_assoc (A B : ZornVectorMatrix R) :
    (B * (A * A)) * A = (B * A) * (A * A) := by
  have h1 : bundledAssociator B (A * A) A = 0 := by
    rw [bundledAssociator_swap12 B (A * A) A, bundledAssociator_sq_left_right A B, neg_zero]
  have h2 : bundledAssociator B A (A * A) = 0 := by
    rw [bundledAssociator_swap23 B A (A * A), h1, neg_zero]
  rw [sub_eq_zero.mp h1, sq_mul_comm_self A, ← sub_eq_zero.mp h2]

private lemma mul_sq_left_assoc (A B : ZornVectorMatrix R) :
    A * ((A * A) * B) = (A * A) * (A * B) := by
  have h1 : bundledAssociator (A * A) A B = 0 := by
    rw [bundledAssociator_swap23 (A * A) A B, bundledAssociator_sq_left_right A B, neg_zero]
  have h2 : bundledAssociator A (A * A) B = 0 := by
    rw [bundledAssociator_swap12 A (A * A) B, h1, neg_zero]
  rw [← sub_eq_zero.mp h2, ← sq_mul_comm_self A, sub_eq_zero.mp h1]

private lemma mul_sq_far_right_assoc (A B : ZornVectorMatrix R) :
    A * (B * (A * A)) = (A * B) * (A * A) := by
  have h : bundledAssociator A B (A * A) = 0 := by
    rw [bundledAssociator_swap23 A B (A * A), bundledAssociator_swap12 A (A * A) B,
        bundledAssociator_swap23 (A * A) A B, bundledAssociator_sq_left_right A B,
        neg_zero, neg_zero, neg_zero]
  exact (sub_eq_zero.mp h).symm

/-- Structural proof that `(A * A) ∘ (B ∘ A) = ((A * A) ∘ B) ∘ A` in `ZornVectorMatrix R`. -/
lemma zornJordan_sq_assoc (A B : ZornVectorMatrix R) :
    zornJordan (zornJordan (A * A) B) A = zornJordan (A * A) (zornJordan B A) := by
  simp only [zornJordan, _root_.add_mul, _root_.mul_add]
  rw [← mul_sq_right_assoc A B, mul_sq_mid_assoc A B,
      mul_sq_left_assoc A B, mul_sq_far_right_assoc A B]
  abel

/-- **Jordan–von Neumann–Wigner (1934) Fundamental Axiom (III), Page 31 Associator Symmetries, & Theorem 12 Off-Diagonal Balance on `ZornVectorMatrix R` (Archetypes LXI & LXII)**:
    Over any commutative ring $R$ (`[CommRing R]`), for ALL $A, B, C \in \mathrm{ZornVectorMatrix}\;R$
    and all $v, w \in \mathrm{ZornVec3}\;R$:
    1. Jordan Commutativity & JvNW Page 31, Eqs. (2)–(3) Associator Identities:
       $$A \circ B = B \circ A, \qquad [A, B, C]_J + [C, B, A]_J = 0, \qquad
         [A, B, C]_J + [B, C, A]_J + [C, A, B]_J = 0.$$
    2. JvNW Fundamental Jordan Identity (III) (Page 30):
       $$((A \circ A) \circ B) \circ A = (A \circ A) \circ (B \circ A)
         \qquad (\text{i.e., } [A \circ A, B, A]_J = 0).$$
    3. JvNW Theorem 12 Equal-Weight Off-Diagonal Square Law (Page 41, $\alpha = \beta$ on $N_{1/2}(e_{11})$):
       $$\langle 0, v, w, 0 \rangle \circ \langle 0, v, w, 0 \rangle =
         \mathrm{zornGradeZero}\;(2 * (v \cdot w))\;(2 * (v \cdot w)).$$ -/
theorem zorn_jordan_von_neumann_wigner_1934_axiom_III_and_peirce
    (A B C : ZornVectorMatrix R) (v w : ZornVec3 R) :
    let J_vw : ZornVectorMatrix R := ⟨0, v, w, 0⟩
    zornJordan A B = zornJordan B A ∧
    zornJordanAssoc A B C + zornJordanAssoc C B A = 0 ∧
    zornJordanAssoc A B C + zornJordanAssoc B C A + zornJordanAssoc C A B = 0 ∧
    zornJordan (zornJordan (zornJordan A A) B) A =
      zornJordan (zornJordan A A) (zornJordan B A) ∧
    zornJordan J_vw J_vw =
      zornGradeZero (2 * ZornVec3.dot v w) (2 * ZornVec3.dot v w) := by
  intro J_vw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [zornJordan]; abel
  · simp only [zornJordanAssoc, zornJordan, _root_.add_mul, _root_.mul_add]; abel
  · simp only [zornJordanAssoc, zornJordan, _root_.add_mul, _root_.mul_add]; abel
  · simp only [zornJordan, _root_.add_mul, _root_.mul_add]
    rw [← mul_sq_right_assoc A B, mul_sq_mid_assoc A B,
        mul_sq_left_assoc A B, mul_sq_far_right_assoc A B]
    abel
  · ext
    · simp [J_vw, zornJordan, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
    · rename_i i; fin_cases i <;>
        (simp [J_vw, zornJordan, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
               add, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [J_vw, zornJordan, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
               add, mul, ZornVec3.cross]; try ring)
    · simp [J_vw, zornJordan, zornGradeZero, InfoGeometry.Algebra.zvm_add_def,
            add, mul, ZornVec3.dot, Fin.sum_univ_three]; ring

/-! ## Section 64: John Archibald Wheeler's "It from Bit" ($P^2 = P$), "The Boundary of a Boundary is Zero" ($d^2 = 0$), & Participatory Idempotent Loops on `ZornVectorMatrix R` (Archetypes LXIII & LXIV) -/

/-- **John Archibald Wheeler's Pregeometry on `ZornVectorMatrix R`: "It from Bit", "The Boundary of a Boundary is Zero", & Participatory Idempotent Loops (Archetypes LXIII & LXIV)**:
    Over any commutative ring $R$ (`[CommRing R]`), for all $v, w, v_1, v_2, v_3 \in \mathrm{ZornVec3}\;R$,
    let $e_{11} = \langle 1, 0, 0, 0 \rangle$, $e_{22} = \langle 0, 0, 0, 1 \rangle$,
    $P_{\mathrm{row}}(v) = \langle 1, v, 0, 0 \rangle$, $P_{\mathrm{col}}(w) = \langle 1, 0, w, 0 \rangle$,
    $d(v) = P_{\mathrm{row}}(v) + -e_{11}$, and $d^*(w) = P_{\mathrm{col}}(w) + -e_{11}$:
    1. Binary Bit Idempotence ($P^2 = P$) & Boundary-of-a-Boundary Nilpotence ($d^2 = 0$):
       $$P_{\mathrm{row}}(v) * P_{\mathrm{row}}(v) = P_{\mathrm{row}}(v), \qquad
         P_{\mathrm{col}}(w) * P_{\mathrm{col}}(w) = P_{\mathrm{col}}(w),$$
       $$d(v) * d(v) = 0, \qquad d^*(w) * d^*(w) = 0.$$
    2. Born Transition Amplitude, Hodge Laplacian Metric $\{d(v), d^*(w)\}$, & Symplectic Spin Connection $[d(v), d^*(w)]$:
       $$P_{\mathrm{row}}(v) * P_{\mathrm{col}}(w) = \mathrm{zornGradeZero}\;(1 + v \cdot w)\;0,$$
       $$d(v) * d^*(w) + d^*(w) * d(v) = \mathrm{zornGradeZero}\;(v \cdot w)\;(v \cdot w),$$
       $$d(v) * d^*(w) + -(d^*(w) * d(v)) = \mathrm{zornGradeZero}\;(v \cdot w)\;(-(v \cdot w)).$$
    3. 2-Bit Gauge Torsion & 3-Bit Spacetime Volume Determinant:
       $$e_{22} * (P_{\mathrm{row}}(v_1) * P_{\mathrm{row}}(v_2)) = \langle 0, 0, v_1 \times v_2, 0 \rangle,$$
       $$d(v_1) * (d(v_2) * d(v_3)) = \mathrm{zornGradeZero}\;(v_1 \cdot (v_2 \times v_3))\;0,$$
       $$(d(v_1) * d(v_2)) * d(v_3) = \mathrm{zornGradeZero}\;0\;(v_1 \cdot (v_2 \times v_3)).$$ -/
theorem zorn_wheeler_it_from_bit_and_boundary_of_boundary
    (v w v₁ v₂ v₃ : ZornVec3 R) :
    let e₁₁ : ZornVectorMatrix R := ⟨1, 0, 0, 0⟩
    let e₂₂ : ZornVectorMatrix R := ⟨0, 0, 0, 1⟩
    let P_row : ZornVectorMatrix R := ⟨1, v, 0, 0⟩
    let P_col : ZornVectorMatrix R := ⟨1, 0, w, 0⟩
    let P_row1 : ZornVectorMatrix R := ⟨1, v₁, 0, 0⟩
    let P_row2 : ZornVectorMatrix R := ⟨1, v₂, 0, 0⟩
    let d_v : ZornVectorMatrix R := P_row + -e₁₁
    let d_w : ZornVectorMatrix R := P_col + -e₁₁
    let d₁ : ZornVectorMatrix R := ⟨1, v₁, 0, 0⟩ + -e₁₁
    let d₂ : ZornVectorMatrix R := ⟨1, v₂, 0, 0⟩ + -e₁₁
    let d₃ : ZornVectorMatrix R := ⟨1, v₃, 0, 0⟩ + -e₁₁
    let vol := ZornVec3.dot v₁ (ZornVec3.cross v₂ v₃)
    (P_row * P_row = P_row ∧
     P_col * P_col = P_col ∧
     d_v * d_v = 0 ∧
     d_w * d_w = 0) ∧
    (P_row * P_col = zornGradeZero (1 + ZornVec3.dot v w) 0 ∧
     d_v * d_w + d_w * d_v = zornGradeZero (ZornVec3.dot v w) (ZornVec3.dot v w) ∧
     d_v * d_w + -(d_w * d_v) = zornGradeZero (ZornVec3.dot v w) (-ZornVec3.dot v w)) ∧
    (e₂₂ * (P_row1 * P_row2) = ⟨0, 0, ZornVec3.cross v₁ v₂, 0⟩ ∧
     d₁ * (d₂ * d₃) = zornGradeZero vol 0 ∧
     (d₁ * d₂) * d₃ = zornGradeZero 0 vol) := by
  intro e₁₁ e₂₂ P_row P_col P_row1 P_row2 d_v d_w d₁ d₂ d₃ vol
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
  { ext
    · simp [e₁₁, e₂₂, P_row, P_col, P_row1, P_row2, d_v, d_w, d₁, d₂, d₃, vol, zornGradeZero,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;>
        (simp [e₁₁, e₂₂, P_row, P_col, P_row1, P_row2, d_v, d_w, d₁, d₂, d₃, vol, zornGradeZero,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [e₁₁, e₂₂, P_row, P_col, P_row1, P_row2, d_v, d_w, d₁, d₂, d₃, vol, zornGradeZero,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring)
    · simp [e₁₁, e₂₂, P_row, P_col, P_row1, P_row2, d_v, d_w, d₁, d₂, d₃, vol, zornGradeZero,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]; try ring }

/-! ## Section 65: The 5-Graded Super-Grassmannian Euler Operator $\mathcal{E}_5$, KKT Degree-5 Polynomial, & $(2|3)$ Lepton–Quark Supertrace Cancellation on `ZornVectorMatrix R` (Archetypes LXV & LXVI) -/

/-- The Euler 5-grading linear operator $\mathcal{E}_5$ on `ZornVectorMatrix R` with eigenvalues $(-2, -1, 0, +1, +2)$ on $(\mathcal{G}_{-2}, \mathcal{G}_{-1}, \mathcal{G}_0, \mathcal{G}_{+1}, \mathcal{G}_{+2})$. -/
def zornEulerFiveGrading (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨0,
   ![-(2 * X.v 0), X.v 1, X.v 2],
   ![2 * X.w 0, -X.w 1, -X.w 2],
   0⟩

/-- **Euler 5-Grading Nilradical Derivation Law, KKT Degree-5 Polynomial $\mathcal{E}_5^5 - 5\mathcal{E}_5^3 + 4\mathcal{E}_5 = 0$, & $(2|3)$ Lepton–Quark Supertrace Cancellation on `ZornVectorMatrix R` (Archetypes LXV & LXVI)**:
    Over any commutative ring $R$ (`[CommRing R]`), for all $X \in \mathrm{ZornVectorMatrix}\;R$,
    all $y_1, z_1, \xi_1, y_2, z_2, \xi_2 \in R$, and all $u, w \in \mathrm{ZornVec3}\;R$:
    1. Exact Leibniz Derivation Law of $\mathcal{E}_5$ on the Positive Heisenberg Nilradical $\mathcal{N}_+ = \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$:
       $$\mathcal{E}_5(N_1 * N_2) = \mathcal{E}_5(N_1) * N_2 + N_1 * \mathcal{E}_5(N_2).$$
    2. Universal KKT Degree-5 Minimal Polynomial Annihilation ($x^5 - 5x^3 + 4x = 0$):
       $$\mathcal{E}_5^5(X) + -(5 • \mathcal{E}_5^3(X)) + 4 • \mathcal{E}_5(X) = 0.$$
    3. $(2|3)$ Lepton–Quark Supertrace UV Cancellation:
       For the leptonic singlet excitation $L(u, w) = \langle 0, u, 0, 0 \rangle * \langle 0, 0, w, 0 \rangle = \mathrm{zornGradeZero}\;(u \cdot w)\;0$,
       its leptonic trace $L.a + L.b$ equals the $3 \times 3$ quark outer-product trace $u_0 w_0 + u_1 w_1 + u_2 w_2$, so their $(2|3)$ supertrace difference vanishes identically:
       $$(L.a + L.b) - (u 0 * w 0 + u 1 * w 1 + u 2 * w 2) = 0.$$ -/
theorem zorn_euler_five_grading_kkt_and_supercolor_cancellation
    (X : ZornVectorMatrix R) (y₁ z₁ ξ₁ y₂ z₂ ξ₂ : R) (u w : ZornVec3 R) :
    let N₁ := zornGradePlus1 y₁ z₁ + zornGradePlus2 ξ₁
    let N₂ := zornGradePlus1 y₂ z₂ + zornGradePlus2 ξ₂
    let E1 := zornEulerFiveGrading X
    let E2 := zornEulerFiveGrading E1
    let E3 := zornEulerFiveGrading E2
    let E4 := zornEulerFiveGrading E3
    let E5 := zornEulerFiveGrading E4
    let Q_u : ZornVectorMatrix R := ⟨0, u, 0, 0⟩
    let Q_w : ZornVectorMatrix R := ⟨0, 0, w, 0⟩
    let L_uw := Q_u * Q_w
    zornEulerFiveGrading (N₁ * N₂) =
      zornEulerFiveGrading N₁ * N₂ + N₁ * zornEulerFiveGrading N₂ ∧
    E5 + -(E3 + E3 + E3 + E3 + E3) + (E1 + E1 + E1 + E1) = 0 ∧
    L_uw = zornGradeZero (ZornVec3.dot u w) 0 ∧
    (L_uw.a + L_uw.b) - (u 0 * w 0 + u 1 * w 1 + u 2 * w 2) = 0 := by
  intro N₁ N₂ E1 E2 E3 E4 E5 Q_u Q_w L_uw
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext
    · simp [N₁, N₂, zornEulerFiveGrading, zornGradePlus1, zornGradePlus2,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        (simp [N₁, N₂, zornEulerFiveGrading, zornGradePlus1, zornGradePlus2,
               InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [N₁, N₂, zornEulerFiveGrading, zornGradePlus1, zornGradePlus2,
               InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.cross]; try ring)
    · simp [N₁, N₂, zornEulerFiveGrading, zornGradePlus1, zornGradePlus2,
            InfoGeometry.Algebra.zvm_add_def, add, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [E1, E2, E3, E4, E5, zornEulerFiveGrading,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
    · rename_i i; fin_cases i <;>
        (simp [E1, E2, E3, E4, E5, zornEulerFiveGrading,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [E1, E2, E3, E4, E5, zornEulerFiveGrading,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]; try ring)
    · simp [E1, E2, E3, E4, E5, zornEulerFiveGrading,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
  · ext
    · simp [L_uw, Q_u, Q_w, zornGradeZero, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [L_uw, Q_u, Q_w, zornGradeZero, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [L_uw, Q_u, Q_w, zornGradeZero, mul, ZornVec3.cross]
    · simp [L_uw, Q_u, Q_w, zornGradeZero, mul, ZornVec3.dot, Fin.sum_univ_three]
  · simp [L_uw, Q_u, Q_w, mul, ZornVec3.dot, Fin.sum_univ_three]

/-! ## Section 66: Rolf Dahm's Projective Line Geometry, Plücker–Klein 6-Vector Bijection, Simple Line Quadric Vanishing, Maxwell–Poynting Lagrange Identity, & Dihedral $D_4$ / $\mathrm{PG}(3,2)$ Collinear Operator Triples on `ZornVectorMatrix R` (Archetypes LXVII & LXVIII) -/

/-- Radial Plücker 3-vector $(p_{01}, p_{02}, p_{03})$ of the projective line spanned by $x, y \in \mathrm{Fin}\;4 \to R$ (R. Dahm, JPCS 3152 (2025) 012008, §2.3). -/
def zornPluckerRad (x y : Fin 4 → R) : ZornVec3 R :=
  ![x 0 * y 1 - y 0 * x 1, x 0 * y 2 - y 0 * x 2, x 0 * y 3 - y 0 * x 3]

/-- Transverse / dual Plücker 3-vector $(p_{23}, p_{31}, p_{12})$ of the projective line spanned by $x, y \in \mathrm{Fin}\;4 \to R$ (R. Dahm, JPCS 3152 (2025) 012008, §2.3). -/
def zornPluckerTrans (x y : Fin 4 → R) : ZornVec3 R :=
  ![x 2 * y 3 - y 2 * x 3, x 3 * y 1 - y 3 * x 1, x 1 * y 2 - y 1 * x 2]

/-- Dahm's dihedral identity generator $r_0$ in `ZornVectorMatrix R`. -/
def zornDahmR0 : ZornVectorMatrix R :=
  ⟨1, 0, 0, 1⟩

/-- Dahm's order-4 complex structure / rotation generator $r_1 = Q_{02}$ in `ZornVectorMatrix R`. -/
def zornDahmR1 : ZornVectorMatrix R :=
  ⟨0, ![1, 0, 0], ![-1, 0, 0], 0⟩

/-- Dahm's diagonal reflection generator $s_0$ in `ZornVectorMatrix R`. -/
def zornDahmS0 : ZornVectorMatrix R :=
  ⟨1, 0, 0, -1⟩

/-- Dahm's anti-diagonal reflection generator $s_1$ in `ZornVectorMatrix R`. -/
def zornDahmS1 : ZornVectorMatrix R :=
  ⟨0, ![1, 0, 0], ![1, 0, 0], 0⟩

/-- **Rolf Dahm's Projective Line Geometry, Plücker–Klein Quadric Vanishing ($p_{01} p_{23} + p_{02} p_{31} + p_{03} p_{12} = 0$), Maxwell–Poynting Orthogonality & Lagrange Identity, and Dihedral $D_4$ / $\mathrm{PG}(3,2)$ Collinear Operator Triples on `ZornVectorMatrix R` (Archetypes LXVII & LXVIII)**:
    Over any commutative ring $R$ (`[CommRing R]`), for all homogeneous points $x, y : \mathrm{Fin}\;4 \to R$
    and all 3-vectors $E, B, x_{\mathrm{even}}, x_{\mathrm{odd}} : \mathrm{ZornVec3}\;R$:
    1. Exact Plücker–Klein Quadric Vanishing ($M_4^2 \subset \mathbb{P}^5$) for Every Projective Line in $\mathbb{P}^3$ (Dahm §2.3–2.4):
       $$\mathbf{p}_{\mathrm{rad}}(x, y) \cdot \mathbf{p}_{\mathrm{trans}}(x, y) = p_{01} p_{23} + p_{02} p_{31} + p_{03} p_{12} = 0,$$
       and the embedded Zorn line-complex element $L(x, y) = \langle 0, \mathbf{p}_{\mathrm{rad}}(x, y), \mathbf{p}_{\mathrm{trans}}(x, y), 0 \rangle$ is strictly isotropic (`norm L(x, y) = 0`).
    2. Senary Klein-to-Plücker Bijection to the Split $\mathrm{SO}(3,3)$ Quadric (Dahm §2.3, Eq. (1)):
       $$(\mathbf{x}_{\mathrm{even}} + \mathbf{x}_{\mathrm{odd}}) \cdot (\mathbf{x}_{\mathrm{even}} - \mathbf{x}_{\mathrm{odd}}) =
         \mathbf{x}_{\mathrm{even}} \cdot \mathbf{x}_{\mathrm{even}} - \mathbf{x}_{\mathrm{odd}} \cdot \mathbf{x}_{\mathrm{odd}}.$$
    3. Maxwell–Poynting Axis Orthogonality & Lagrange Identity for Line Complexes (Dahm §2.2):
       $$\mathbf{E} \cdot (\mathbf{E} \times \mathbf{B}) = 0, \qquad \mathbf{B} \cdot (\mathbf{E} \times \mathbf{B}) = 0,$$
       $$(\mathbf{E} \times \mathbf{B}) \cdot (\mathbf{E} \times \mathbf{B}) + (\mathbf{E} \cdot \mathbf{B})^2 = (\mathbf{E} \cdot \mathbf{E})(\mathbf{B} \cdot \mathbf{B}).$$
    4. Dihedral $D_4$ Gauge Relations & $\mathrm{PG}(3,2)$ Collinear Operator Triple Product $(s_0 * s_1) * r_1 = -r_0 = -1$ (Dahm §2.4, §3, Fig. 1):
       $$r_1 * r_1 = -r_0, \qquad s_0 * s_0 = r_0, \qquad s_1 * s_1 = r_0, \qquad
         s_0 * r_1 = s_1, \qquad (s_0 * s_1) * r_1 = -r_0.$$ -/
theorem zorn_dahm_plucker_klein_bijection_and_maxwell_lagrange_synthesis
    (x y : Fin 4 → R) (E B x_even x_odd : ZornVec3 R) :
    let p_rad := zornPluckerRad x y
    let p_trans := zornPluckerTrans x y
    let L_line : ZornVectorMatrix R := ⟨0, p_rad, p_trans, 0⟩
    ZornVec3.dot p_rad p_trans = 0 ∧
    norm L_line = 0 ∧
    ZornVec3.dot (x_even + x_odd) (x_even - x_odd) =
      ZornVec3.dot x_even x_even - ZornVec3.dot x_odd x_odd ∧
    ZornVec3.dot E (ZornVec3.cross E B) = 0 ∧
    ZornVec3.dot B (ZornVec3.cross E B) = 0 ∧
    ZornVec3.dot (ZornVec3.cross E B) (ZornVec3.cross E B) +
      ZornVec3.dot E B * ZornVec3.dot E B =
      ZornVec3.dot E E * ZornVec3.dot B B ∧
    (zornDahmR1 : ZornVectorMatrix R) * zornDahmR1 = -zornDahmR0 ∧
    (zornDahmS0 : ZornVectorMatrix R) * zornDahmS0 = zornDahmR0 ∧
    (zornDahmS1 : ZornVectorMatrix R) * zornDahmS1 = zornDahmR0 ∧
    (zornDahmS0 : ZornVectorMatrix R) * zornDahmR1 = zornDahmS1 ∧
    ((zornDahmS0 : ZornVectorMatrix R) * zornDahmS1) * zornDahmR1 = -zornDahmR0 := by
  intro p_rad p_trans L_line
  refine ⟨?_, ?_, ?_, ZornVec3.dot_cross_self_left E B, ZornVec3.dot_cross_self_right E B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [p_rad, p_trans, zornPluckerRad, zornPluckerTrans, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · simp [L_line, norm, p_rad, p_trans, zornPluckerRad, zornPluckerTrans, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · simp [ZornVec3.dot, Fin.sum_univ_three]
    ring
  · rw [ZornVec3.dot_cross_self E B]
    ring
  · ext
    · simp [zornDahmR1, zornDahmR0, InfoGeometry.Algebra.zvm_neg_def, neg, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [zornDahmR1, zornDahmR0, InfoGeometry.Algebra.zvm_neg_def, neg, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [zornDahmR1, zornDahmR0, InfoGeometry.Algebra.zvm_neg_def, neg, mul, ZornVec3.cross]
    · simp [zornDahmR1, zornDahmR0, InfoGeometry.Algebra.zvm_neg_def, neg, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [zornDahmS0, zornDahmR0, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [zornDahmS0, zornDahmR0, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [zornDahmS0, zornDahmR0, mul, ZornVec3.cross]
    · simp [zornDahmS0, zornDahmR0, mul, ZornVec3.dot]
  · ext
    · simp [zornDahmS1, zornDahmR0, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [zornDahmS1, zornDahmR0, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [zornDahmS1, zornDahmR0, mul, ZornVec3.cross]
    · simp [zornDahmS1, zornDahmR0, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [zornDahmS0, zornDahmR1, zornDahmS1, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [zornDahmS0, zornDahmR1, zornDahmS1, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [zornDahmS0, zornDahmR1, zornDahmS1, mul, ZornVec3.cross]
    · simp [zornDahmS0, zornDahmR1, zornDahmS1, mul, ZornVec3.dot]
  · ext
    · simp [zornDahmS0, zornDahmS1, zornDahmR1, zornDahmR0, InfoGeometry.Algebra.zvm_neg_def, neg, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [zornDahmS0, zornDahmS1, zornDahmR1, zornDahmR0, InfoGeometry.Algebra.zvm_neg_def, neg, mul, ZornVec3.dot, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [zornDahmS0, zornDahmS1, zornDahmR1, zornDahmR0, InfoGeometry.Algebra.zvm_neg_def, neg, mul, ZornVec3.dot, ZornVec3.cross]
    · simp [zornDahmS0, zornDahmS1, zornDahmR1, zornDahmR0, InfoGeometry.Algebra.zvm_neg_def, neg, mul, ZornVec3.dot, Fin.sum_univ_three]

/-! ## Section 67: Plücker–Klein Simple Line Square-Zero Nilpotence, Unipotent Line Exponential Group Law, & Zorn Poynting Orthogonality on `ZornVectorMatrix R` (Archetypes LXIX & LXX) -/

/-- Plücker–Klein simple line matrix $J_{\mathrm{line}}(x, y) = \langle 0, \mathbf{p}_{\mathrm{rad}}(x, y), \mathbf{p}_{\mathrm{trans}}(x, y), 0 \rangle$ in `ZornVectorMatrix R`. -/
def zornPluckerLineMatrix (x y : Fin 4 → R) : ZornVectorMatrix R :=
  ⟨0, zornPluckerRad x y, zornPluckerTrans x y, 0⟩

/-- **Plücker–Klein Simple Line Square-Zero Theorem ($J_{\mathrm{line}}(x, y)^2 = 0$), Unipotent Line Exponential Group Law, & Zorn Poynting Orthogonality on `ZornVectorMatrix R` (Archetypes LXIX & LXX)**:
    Over any commutative ring $R$ (`[CommRing R]`), for all homogeneous points $x, y : \mathrm{Fin}\;4 \to R$,
    all scalars $s : R$, and all 3-vector fields $E, B : \mathrm{ZornVec3}\;R$,
    let $J_{\mathrm{line}} = \mathrm{zornPluckerLineMatrix}\;x\;y$, $L_E = \langle 0, E, 0, 0 \rangle$, and $L_B = \langle 0, B, 0, 0 \rangle$:
    1. Exact Vanishing of the Plücker–Klein Norm:
       $$\mathrm{norm}(J_{\mathrm{line}}) = 0.$$
    2. Exact Square-Zero Nilpotence in All 8 Dimensions of `ZornVectorMatrix R`:
       $$J_{\mathrm{line}} * J_{\mathrm{line}} = 0.$$
    3. Exact Unipotent Exponential Inversion of Any Simple Projective Line in $\mathbb{P}^3$:
       $$(\mathrm{one} + s \bullet J_{\mathrm{line}}) * (\mathrm{one} + -(s \bullet J_{\mathrm{line}})) = \mathrm{one}.$$
    4. Zorn Poynting 3-Fold Orthogonality ($L_+(\mathbf{E}) * (L_+(\mathbf{E}) * L_+(\mathbf{B})) = 0$ and $L_+(\mathbf{B}) * (L_+(\mathbf{E}) * L_+(\mathbf{B})) = 0$):
       $$L_E * (L_E * L_B) = 0 \qquad \text{and} \qquad L_B * (L_E * L_B) = 0.$$ -/
theorem dahm_simple_plucker_line_null_square_and_unipotent_inversion
    (x y : Fin 4 → R) (s : R) (E B : ZornVec3 R) :
    let J_line := zornPluckerLineMatrix x y
    let L_E : ZornVectorMatrix R := ⟨0, E, 0, 0⟩
    let L_B : ZornVectorMatrix R := ⟨0, B, 0, 0⟩
    norm J_line = 0 ∧
    J_line * J_line = 0 ∧
    (one + s • J_line) * (one + -(s • J_line)) = one ∧
    L_E * (L_E * L_B) = 0 ∧
    L_B * (L_E * L_B) = 0 := by
  intro J_line L_E L_B
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [J_line, zornPluckerLineMatrix, zornPluckerRad, zornPluckerTrans,
          norm, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · ext
    · simp [J_line, zornPluckerLineMatrix, zornPluckerRad, zornPluckerTrans,
            mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · rename_i i; fin_cases i <;>
        (simp [J_line, zornPluckerLineMatrix, zornPluckerRad, zornPluckerTrans,
               mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [J_line, zornPluckerLineMatrix, zornPluckerRad, zornPluckerTrans,
               mul, ZornVec3.cross]; try ring)
    · simp [J_line, zornPluckerLineMatrix, zornPluckerRad, zornPluckerTrans,
            mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  · ext
    · simp [J_line, zornPluckerLineMatrix, zornPluckerRad, zornPluckerTrans,
            one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_smul_def, add, neg, smul, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · rename_i i; fin_cases i <;>
        (simp [J_line, zornPluckerLineMatrix, zornPluckerRad, zornPluckerTrans,
               one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_smul_def, add, neg, smul, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [J_line, zornPluckerLineMatrix, zornPluckerRad, zornPluckerTrans,
               one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               InfoGeometry.Algebra.zvm_smul_def, add, neg, smul, mul, ZornVec3.cross]; try ring)
    · simp [J_line, zornPluckerLineMatrix, zornPluckerRad, zornPluckerTrans,
            one, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            InfoGeometry.Algebra.zvm_smul_def, add, neg, smul, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  · ext
    · simp [L_E, L_B, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
    · rename_i i; fin_cases i <;> simp [L_E, L_B, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [L_E, L_B, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · simp [L_E, L_B, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  · ext
    · simp [L_E, L_B, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
    · rename_i i; fin_cases i <;> simp [L_E, L_B, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [L_E, L_B, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    · simp [L_E, L_B, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

/-! ## Section 68: Saniga–Holweck–Pracna (2015) Combinatorial Grassmannian $G_2(N+1)$ Edge-Triangle Invariance & Cayley–Dickson Sedenion Zero Divisors on `ZornVectorMatrix R` (Archetypes LXXI & LXXII) -/

/-- Combinatorial Grassmannian $G_2(N+1)$ edge operator $\Omega_{ij} = \langle 0, v_i - v_j, 0, 0 \rangle$ in `ZornVectorMatrix R`. -/
def zornGrassmannEdge (v_i v_j : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨0, v_i - v_j, 0, 0⟩

/-- **Saniga–Holweck–Pracna Combinatorial Grassmannian $G_2(N+1)$ Edge-Triangle Collinear Invariance & Cayley–Dickson Sedenion Zero-Divisor Identity on `ZornVectorMatrix R` (Archetypes LXXI & LXXII)**:
    Over any commutative ring $R$ (`[CommRing R]`), for all vertex 3-vectors $v_i, v_j, v_k, v, w : \mathrm{ZornVec3}\;R$,
    let $\Omega_{ij} = \mathrm{zornGrassmannEdge}\;v_i\;v_j$, $\Omega_{jk} = \mathrm{zornGrassmannEdge}\;v_j\;v_k$,
    $\Omega_{ki} = \mathrm{zornGrassmannEdge}\;v_k\;v_i$, $\Omega_{ik} = \mathrm{zornGrassmannEdge}\;v_i\;v_k$,
    $x = \langle 0, v, 0, 0 \rangle$, $y = \langle 0, 0, w, 0 \rangle$, $X = \langle 0, 0, w, 0 \rangle$, and $Y = -\langle 0, v, 0, 0 \rangle$:
    1. Edge Nilpotence & Veldkamp Collinear Triangle Sum:
       $$\Omega_{ij} * \Omega_{ij} = 0, \qquad \Omega_{ij} + \Omega_{jk} = \Omega_{ik}, \qquad \Omega_{ij} + \Omega_{jk} + \Omega_{ki} = 0.$$
    2. Universal 2-Plane Invariance Across All Three Edges of the Line $\{\{i, j\}, \{j, k\}, \{k, i\}\}$:
       $$\Omega_{ij} * \Omega_{jk} = \Omega_{jk} * \Omega_{ki} \qquad \text{and} \qquad \Omega_{jk} * \Omega_{ki} = \Omega_{ki} * \Omega_{ij}.$$
    3. Universal Sedenion Zero-Divisor Cancellation on `ZornVectorMatrix R` (Saniga–Holweck–Pracna Page 1193, Eq. 2):
       $$x * X + -(Y * \mathrm{conj}\;y) = 0 \qquad \text{and} \qquad \mathrm{conj}\;x * Y + X * y = 0.$$ -/
theorem saniga_holweck_pracna_grassmannian_edge_triangle_and_sedenion_zero_divisors
    (v_i v_j v_k v w : ZornVec3 R) :
    let Ω_ij := zornGrassmannEdge v_i v_j
    let Ω_jk := zornGrassmannEdge v_j v_k
    let Ω_ki := zornGrassmannEdge v_k v_i
    let Ω_ik := zornGrassmannEdge v_i v_k
    let x : ZornVectorMatrix R := ⟨0, v, 0, 0⟩
    let y : ZornVectorMatrix R := ⟨0, 0, w, 0⟩
    let X : ZornVectorMatrix R := ⟨0, 0, w, 0⟩
    let Y : ZornVectorMatrix R := -⟨0, v, 0, 0⟩
    Ω_ij * Ω_ij = 0 ∧
    Ω_ij + Ω_jk = Ω_ik ∧
    (Ω_ij + Ω_jk) + Ω_ki = 0 ∧
    Ω_ij * Ω_jk = Ω_jk * Ω_ki ∧
    Ω_jk * Ω_ki = Ω_ki * Ω_ij ∧
    x * X + -(Y * conj y) = 0 ∧
    conj x * Y + X * y = 0 := by
  intro Ω_ij Ω_jk Ω_ki Ω_ik x y X Y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext
    · simp [Ω_ij, zornGrassmannEdge, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [Ω_ij, zornGrassmannEdge, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> (simp [Ω_ij, zornGrassmannEdge, mul, ZornVec3.cross]; try ring)
    · simp [Ω_ij, zornGrassmannEdge, mul, ZornVec3.dot]
  · ext
    · simp [Ω_ij, Ω_jk, Ω_ik, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, add]
    · rename_i i; fin_cases i <;> (simp [Ω_ij, Ω_jk, Ω_ik, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, add]; try ring)
    · rename_i i; fin_cases i <;> simp [Ω_ij, Ω_jk, Ω_ik, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, add]
    · simp [Ω_ij, Ω_jk, Ω_ik, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, add]
  · ext
    · simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, add]
    · rename_i i; fin_cases i <;> (simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, add]; try ring)
    · rename_i i; fin_cases i <;> simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, add]
    · simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, add]
  · ext
    · simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> (simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, mul, ZornVec3.cross]; try ring)
    · simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, mul, ZornVec3.dot]
  · ext
    · simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;> simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> (simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, mul, ZornVec3.cross]; try ring)
    · simp [Ω_ij, Ω_jk, Ω_ki, zornGrassmannEdge, mul, ZornVec3.dot]
  · ext
    · simp [x, y, X, Y, conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        (simp [x, y, X, Y, conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [x, y, X, Y, conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, ZornVec3.cross]; try ring)
    · simp [x, y, X, Y, conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, ZornVec3.dot]
  · ext
    · simp [x, y, X, Y, conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        (simp [x, y, X, Y, conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [x, y, X, Y, conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
               add, neg, mul, ZornVec3.cross]; try ring)
    · simp [x, y, X, Y, conj, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
            add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]

/-! ## Section 69: Universal Pasch 4-Simplex Tetrahedral Boundary Closure ($\partial_2 \circ \partial_1 = 0$) & Combinatorial Para-Kähler Metric Polarization on `ZornVectorMatrix R` (Archetypes LXXIII & LXXIV) -/

/-- Dual combinatorial Grassmannian edge operator $\Omega_{ij}^- = \langle 0, 0, v_i - v_j, 0 \rangle$ in `ZornVectorMatrix R`. -/
def zornGrassmannEdgeMinus (v_i v_j : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨0, 0, v_i - v_j, 0⟩

/-- Plücker 2-plane line operator $\mathcal{P}_{ijk} = \Omega_{ij}^+ * \Omega_{jk}^+$ in `ZornVectorMatrix R`. -/
noncomputable def zornGrassmannLinePlane (v_i v_j v_k : ZornVec3 R) : ZornVectorMatrix R :=
  zornGrassmannEdge v_i v_j * zornGrassmannEdge v_j v_k

/-- Edge self-metric $g_{ij} = \Omega_{ij}^+ * \Omega_{ij}^- + \Omega_{ij}^- * \Omega_{ij}^+$ in `ZornVectorMatrix R`. -/
noncomputable def zornGrassmannEdgeMetric (v_i v_j : ZornVec3 R) : ZornVectorMatrix R :=
  zornGrassmannEdge v_i v_j * zornGrassmannEdgeMinus v_i v_j +
    zornGrassmannEdgeMinus v_i v_j * zornGrassmannEdge v_i v_j

/-- **Universal Pasch 4-Simplex Boundary Closure ($\partial_2 \circ \partial_1 = 0$) & Combinatorial Para-Kähler Metric Polarization on `ZornVectorMatrix R` (Archetypes LXXIII & LXXIV)**:
    Over any commutative ring $R$ (`[CommRing R]`), for all vertex 3-vectors $v_i, v_j, v_k, v_l : \mathrm{ZornVec3}\;R$:
    1. 1-Boundary Closure on Every Line $\{i, j, k\}$ of $G_2(N+1)$:
       $$\Omega_{ij}^+ + \Omega_{jk}^+ + -\Omega_{ik}^+ = 0.$$
    2. 2-Boundary Closure Around Every Pasch 4-Simplex $\{i, j, k, l\}$ ($\partial_2 \circ \partial_1 = 0$):
       $$( \mathcal{P}_{ijk} + -\mathcal{P}_{ikl} ) + ( \mathcal{P}_{ijl} + -\mathcal{P}_{jkl} ) = 0.$$
    3. Combinatorial Para-Kähler Metric Polarization Law on Every Line $\{i, j, k\}$:
       $$(g_{ik} + -g_{ij}) + -g_{jk} =
         (\Omega_{ij}^+ * \Omega_{jk}^- + \Omega_{jk}^- * \Omega_{ij}^+) +
         (\Omega_{jk}^+ * \Omega_{ij}^- + \Omega_{ij}^- * \Omega_{jk}^+).$$ -/
theorem zorn_pasch_tetrahedral_boundary_and_combinatorial_metric_polarization
    (v_i v_j v_k v_l : ZornVec3 R) :
    let Ω_ij_p := zornGrassmannEdge v_i v_j
    let Ω_jk_p := zornGrassmannEdge v_j v_k
    let Ω_ik_p := zornGrassmannEdge v_i v_k
    let Ω_ij_m := zornGrassmannEdgeMinus v_i v_j
    let Ω_jk_m := zornGrassmannEdgeMinus v_j v_k
    let P_ijk := zornGrassmannLinePlane v_i v_j v_k
    let P_ikl := zornGrassmannLinePlane v_i v_k v_l
    let P_ijl := zornGrassmannLinePlane v_i v_j v_l
    let P_jkl := zornGrassmannLinePlane v_j v_k v_l
    (Ω_ij_p + Ω_jk_p) + -Ω_ik_p = 0 ∧
    (P_jkl + -P_ikl) + (P_ijl + -P_ijk) = 0 ∧
    (zornGrassmannEdgeMetric v_i v_k + -zornGrassmannEdgeMetric v_i v_j) + -zornGrassmannEdgeMetric v_j v_k =
      (Ω_ij_p * Ω_jk_m + Ω_jk_m * Ω_ij_p) + (Ω_jk_p * Ω_ij_m + Ω_ij_m * Ω_jk_p) := by
  intro Ω_ij_p Ω_jk_p Ω_ik_p Ω_ij_m Ω_jk_m P_ijk P_ikl P_ijl P_jkl
  refine ⟨?_, ?_, ?_⟩
  · ext
    · simp [Ω_ij_p, Ω_jk_p, Ω_ik_p, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
    · rename_i i; fin_cases i <;>
        (simp [Ω_ij_p, Ω_jk_p, Ω_ik_p, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]; try ring)
    · rename_i i; fin_cases i <;>
        simp [Ω_ij_p, Ω_jk_p, Ω_ik_p, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
    · simp [Ω_ij_p, Ω_jk_p, Ω_ik_p, zornGrassmannEdge, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg]
  · ext
    · simp [P_ijk, P_ikl, P_ijl, P_jkl, zornGrassmannLinePlane, zornGrassmannEdge,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.dot]
    · rename_i i; fin_cases i <;>
        simp [P_ijk, P_ikl, P_ijl, P_jkl, zornGrassmannLinePlane, zornGrassmannEdge,
              InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;>
        (simp [P_ijk, P_ikl, P_ijl, P_jkl, zornGrassmannLinePlane, zornGrassmannEdge,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.cross]; try ring)
    · simp [P_ijk, P_ikl, P_ijl, P_jkl, zornGrassmannLinePlane, zornGrassmannEdge,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.dot]
  · ext
    · simp [Ω_ij_p, Ω_jk_p, Ω_ij_m, Ω_jk_m, zornGrassmannEdgeMetric, zornGrassmannEdge, zornGrassmannEdgeMinus,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · rename_i i; fin_cases i <;>
        (simp [Ω_ij_p, Ω_jk_p, Ω_ij_m, Ω_jk_m, zornGrassmannEdgeMetric, zornGrassmannEdge, zornGrassmannEdgeMinus,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;>
        (simp [Ω_ij_p, Ω_jk_p, Ω_ij_m, Ω_jk_m, zornGrassmannEdgeMetric, zornGrassmannEdge, zornGrassmannEdgeMinus,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.cross]; try ring)
    · simp [Ω_ij_p, Ω_jk_p, Ω_ij_m, Ω_jk_m, zornGrassmannEdgeMetric, zornGrassmannEdge, zornGrassmannEdgeMinus,
            InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring

/-! ## Section 70: Catto–Gürcan–Khalfan–Kurt (2018) Affine $E_9$, Hyperbolic $E_{10}$ Kac–Moody Roots, & Jacobson Jordan Triple Weyl Reflection Law on `ZornVectorMatrix R` (Archetypes LXXV & LXXVI) -/

/-- Catto et al. Eq. (45) (Page 8, unscaled by $-2$): Lorentzian Kac–Moody pairing
    $\langle X, Y \rangle_{\mathrm{Kac}} = \mathrm{trace}(X * \mathrm{conj}\;Y)$ on `ZornVectorMatrix R`. -/
noncomputable def zornKacMoodyPairing (X Y : ZornVectorMatrix R) : R :=
  trace (X * conj Y)

/-- **Jacobson's Jordan Triple Product (`zornJacobsonTriple X Y Z`)** on `ZornVectorMatrix R`
    (Catto–Gürcan–Khalfan–Kurt 2018, Page 7, Eq. 35, unscaled):
    $\{X, Y, Z\}_{\mathrm{JT}} = ((X \circ Y) \circ Z + X \circ (Y \circ Z)) + -((X \circ Z) \circ Y)$. -/
noncomputable def zornJacobsonTriple (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  (zornJordan (zornJordan X Y) Z + zornJordan X (zornJordan Y Z)) +
    -(zornJordan (zornJordan X Z) Y)

/-- Affine $\tilde{E}_8 = E_9$ root $R_0^{(+)}(x_+, v, w) = \langle x_+, v, w, 0 \rangle$ in `ZornVectorMatrix R`
    (Catto et al. 2018, Page 7, Eq. 31 & Page 9, Eqs. 52, 55). -/
def zornCattoAffineRoot (x_plus : R) (v w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨x_plus, v, w, 0⟩

/-- Coordinate formula for the symmetrized Jordan product `zornJordan X Y = X * Y + Y * X`
    on `ZornVectorMatrix R`: the skew 3-vector cross products cancel identically, leaving
    only scalar traces and dot contractions. -/
theorem zornJordan_eq (X Y : ZornVectorMatrix R) :
    zornJordan X Y =
      ⟨X.a * Y.a + Y.a * X.a + ZornVec3.dot X.v Y.w + ZornVec3.dot Y.v X.w,
       fun i => (X.a + X.b) * Y.v i + (Y.a + Y.b) * X.v i,
       fun i => (X.a + X.b) * Y.w i + (Y.a + Y.b) * X.w i,
       X.b * Y.b + Y.b * X.b + ZornVec3.dot X.w Y.v + ZornVec3.dot Y.w X.v⟩ := by
  ext i
  · simp [zornJordan, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
          add, mul]
    ring
  · fin_cases i <;>
      (simp [zornJordan, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
             add, mul, ZornVec3.cross]; ring)
  · fin_cases i <;>
      (simp [zornJordan, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
             add, mul, ZornVec3.cross]; ring)
  · simp [zornJordan, InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_mul_def,
          add, mul]
    ring

private lemma kirmse_left_conj (X Y : ZornVectorMatrix R) :
    X * (conj X * Y) = norm X • Y := by
  have h := kirmse_left (conj X) Y
  rw [conj_conj, norm_conj] at h
  exact h

private lemma kirmse_right_conj (X Y : ZornVectorMatrix R) :
    (Y * conj X) * X = norm X • Y := by
  have h := kirmse_right (conj X) Y
  rw [conj_conj, norm_conj] at h
  exact h

private lemma zornKacMoodyPairing_self (X : ZornVectorMatrix R) :
    zornKacMoodyPairing X X = 2 * norm X := by
  dsimp [zornKacMoodyPairing]
  change trace (mul X (conj X)) = 2 * norm X
  rw [conj_norm_identity_left, trace_scalar]

/-- **Catto–Gürcan–Khalfan–Kurt (2018) Affine $E_9$, Hyperbolic $E_{10}$ Kac–Moody Root Pairing, Affine Jordan Triple Closure, Hyperbolic Weyl Reflection Formula, & Norm Similitude on `ZornVectorMatrix R` (Archetypes LXXV & LXXVI)**:
    Over any commutative ring $R$ (`[CommRing R]`), for ALL 8D Zorn matrices $A, B \in \mathrm{ZornVectorMatrix}\;R$,
    all scalars $x_1, x_2, x_3 : R$, and all 3-vectors $v, w, v_1, w_1, v_2, w_2, v_3, w_3 : \mathrm{ZornVec3}\;R$:
    1. Lightlike Kac–Moody Root Inner Products & Hyperbolic $E_{10}$ Root Attachment (Pages 9–10, Eqs. 54, 60, 67):
       $$\langle E_{11}, E_{11} \rangle_{\mathrm{Kac}} = 0, \qquad
         \langle E_{22}, E_{22} \rangle_{\mathrm{Kac}} = 0, \qquad
         \langle E_{11}, E_{22} \rangle_{\mathrm{Kac}} = 1,$$
       $$\langle \Gamma, \Gamma \rangle_{\mathrm{Kac}} = -2, \qquad
         \langle \Gamma, \mathrm{offDiagonal}\;v\;w \rangle_{\mathrm{Kac}} = 0, \qquad
         \langle \Gamma, R_0^{(+)}(1, v, w) \rangle_{\mathrm{Kac}} = -1.$$
    2. Affine Kac–Moody Root Closure under Jacobson's Jordan Triple Product (Page 7, Eqs. 31, 35, 37):
       For any three affine roots $R_i = \mathrm{zornCattoAffineRoot}\;x_i\;v_i\;w_i$,
       $$\bigl(\{R_1, \mathrm{conj}\;R_2, R_3\}_{\mathrm{JT}}\bigr).b = 0.$$
    3. Lorentzian Weyl Reflection Formula via Jacobson Triple Product (Page 8, Eqs. 38–39):
       $$\{B, \mathrm{conj}\;A, B\}_{\mathrm{JT}} =
         (4 : R) \bullet \bigl(\mathrm{trace}(A * \mathrm{conj}\;B) \bullet B + -(\mathrm{norm}\;B \bullet A)\bigr).$$
    4. Jacobson Triple Determinant / Norm Similitude Law (Page 7, Eq. 36):
       $$\mathrm{norm}\bigl(\{B, \mathrm{conj}\;A, B\}_{\mathrm{JT}}\bigr) =
         16 * (\mathrm{norm}\;B * \mathrm{norm}\;B) * \mathrm{norm}\;A.$$ -/
theorem catto_jacobson_triple_weyl_reflection_and_norm_similitude
    (A B : ZornVectorMatrix R) (x₁ x₂ x₃ : R)
    (v w v₁ w₁ v₂ w₂ v₃ w₃ : ZornVec3 R) :
    let R₁ := zornCattoAffineRoot x₁ v₁ w₁
    let R₂ := zornCattoAffineRoot x₂ v₂ w₂
    let R₃ := zornCattoAffineRoot x₃ v₃ w₃
    let T_BAB := zornJacobsonTriple B (conj A) B
    zornKacMoodyPairing (E11 : ZornVectorMatrix R) E11 = 0 ∧
    zornKacMoodyPairing (E22 : ZornVectorMatrix R) E22 = 0 ∧
    zornKacMoodyPairing (E11 : ZornVectorMatrix R) E22 = 1 ∧
    zornKacMoodyPairing (zornGamma : ZornVectorMatrix R) zornGamma = -2 ∧
    zornKacMoodyPairing (zornGamma : ZornVectorMatrix R) (offDiagonal v w) = 0 ∧
    zornKacMoodyPairing (zornGamma : ZornVectorMatrix R) (zornCattoAffineRoot 1 v w) = -1 ∧
    (zornJacobsonTriple R₁ (conj R₂) R₃).b = 0 ∧
    T_BAB = (4 : R) • (trace (A * conj B) • B + -(norm B • A)) ∧
    norm T_BAB = 16 * (norm B * norm B) * norm A := by
  intro R₁ R₂ R₃ T_BAB
  have h_bca : (B * conj A) * B = trace (A * conj B) • B + -(norm B • A) := by
    have h1 := congrArg (fun W => mul W B) (conj_trace_identity (mul B (conj A)))
    rw [conj_mul, conj_conj, add_mul, scalar_mul, trace_mul_conj_comm B A] at h1
    have hk : mul (mul A (conj B)) B = smul (norm B) A := kirmse_right_conj B A
    rw [hk] at h1
    exact eq_add_neg_of_add_eq h1
  have h_weyl : T_BAB = (4 : R) • (trace (A * conj B) • B + -(norm B • A)) := by
    ext i
    · simp only [T_BAB, zornJacobsonTriple, zornJordan_eq, conj, trace, norm,
                 InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
                 InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_mul_def,
                 add, neg, smul, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · simp only [T_BAB, zornJacobsonTriple, zornJordan_eq, conj, trace, norm,
                 InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
                 InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_mul_def,
                 add, neg, smul, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · simp only [T_BAB, zornJacobsonTriple, zornJordan_eq, conj, trace, norm,
                 InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
                 InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_mul_def,
                 add, neg, smul, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
    · simp only [T_BAB, zornJacobsonTriple, zornJordan_eq, conj, trace, norm,
                 InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
                 InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_mul_def,
                 add, neg, smul, mul, ZornVec3.dot, Fin.sum_univ_three]
      ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h_weyl, ?_⟩
  · simp [zornKacMoodyPairing, E11, conj, trace, mul, ZornVec3.dot, Fin.sum_univ_three]
  · simp [zornKacMoodyPairing, E22, conj, trace, mul, ZornVec3.dot, Fin.sum_univ_three]
  · simp [zornKacMoodyPairing, E11, E22, conj, trace, mul, ZornVec3.dot, Fin.sum_univ_three]
  · simp [zornKacMoodyPairing, zornGamma, conj, trace, mul, ZornVec3.dot, Fin.sum_univ_three]; ring
  · simp [zornKacMoodyPairing, zornGamma, offDiagonal, conj, trace, mul, ZornVec3.dot, Fin.sum_univ_three]
  · simp [zornKacMoodyPairing, zornGamma, zornCattoAffineRoot, conj, trace, mul, ZornVec3.dot, Fin.sum_univ_three]
  · simp only [R₁, R₂, R₃, zornJacobsonTriple, zornJordan_eq, zornCattoAffineRoot, conj,
               InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def, add, neg,
               ZornVec3.dot, Fin.sum_univ_three]
    ring
  · have h_sandwich : T_BAB = (4 : R) • twoSidedSandwich B (conj A) := by
      dsimp [twoSidedSandwich]
      change T_BAB = (4 : R) • ((B * conj A) * B)
      rw [h_bca, h_weyl]
    rw [h_sandwich, zvm_smul_def, norm_smul, norm_twoSidedSandwich, norm_conj]
    ring

/-! ## Section 71: The 27D Split-Octonion Albert–Conway–Sloane Algebra $\mathfrak{J}_3(\mathrm{Zorn}(R))$, Freudenthal Sharp Adjoint $M^\#$, & Exact Non-Associative Cubic Determinant Law (Archetype LXXVII) -/

/-- **The 27D Freudenthal Cubic Determinant (`albertZornDet x_plus x_minus v Q Ξ₁ Ξ₂`)**
    of the Hermitian $3 \times 3$ split-octonion Conway–Sloane matrix (Catto et al. 2018, Page 10, Eq. 68 & Page 12, Eq. 81):
    $$M = \begin{pmatrix} x_+ & Q & \Xi_1 \\ \bar{Q} & x_- & \Xi_2 \\ \bar{\Xi}_1 & \bar{\Xi}_2 & v \end{pmatrix},$$
    $$\mathrm{Det}_{27}(M) = x_+ x_- v - x_+ N(\Xi_2) - x_- N(\Xi_1) - v N(Q) + \mathrm{trace}((Q * \Xi_2) * \mathrm{conj}\;\Xi_1).$$ -/
noncomputable def albertZornDet (x_plus x_minus v : R) (Q Ξ₁ Ξ₂ : ZornVectorMatrix R) : R :=
  x_plus * x_minus * v -
    x_plus * norm Ξ₂ -
    x_minus * norm Ξ₁ -
    v * norm Q +
    trace ((Q * Ξ₂) * conj Ξ₁)

/-- Off-diagonal $(0, 1)$, $(0, 2)$, and $(1, 2)$ Zorn split-octonion components of the
    27D Freudenthal Sharp Adjoint $M^\#$ (Catto et al. Page 10, Eq. 69). -/
noncomputable def albertZornSharpQ (v : R) (Q Ξ₁ Ξ₂ : ZornVectorMatrix R) : ZornVectorMatrix R :=
  Ξ₁ * conj Ξ₂ + -(v • Q)

noncomputable def albertZornSharpXi1 (x_minus : R) (Q Ξ₁ Ξ₂ : ZornVectorMatrix R) : ZornVectorMatrix R :=
  Q * Ξ₂ + -(x_minus • Ξ₁)

noncomputable def albertZornSharpXi2 (x_plus : R) (Q Ξ₁ Ξ₂ : ZornVectorMatrix R) : ZornVectorMatrix R :=
  conj Q * Ξ₁ + -(x_plus • Ξ₂)

/-- **The 27D Split-Octonion Albert–Conway–Sloane Freudenthal Adjoint & Cubic Determinant Theorem (`albertZorn27D_freudenthal_sharp_and_determinant_law`, Archetype LXXVII)**:
    Over any commutative ring $R$ (`[CommRing R]`), for ALL 27-dimensional split-octonion Albert–Conway–Sloane
    parameters $x_+, x_-, v : R$ and $Q, \Xi_1, \Xi_2 : \mathrm{ZornVectorMatrix}\;R$ (3 scalars + three 8D
    noncommutative, non-associative Zorn split-octonion matrices = 27 dimensions):
    1. Associator Invariance of the Cubic Freudenthal Trace:
       $$\mathrm{trace}((Q * \Xi_2) * \mathrm{conj}\;\Xi_1) = \mathrm{trace}(Q * (\Xi_2 * \mathrm{conj}\;\Xi_1)).$$
    2. Eq. (69) Diagonal Identity (Page 10: All 3 Diagonal Entries of $M \bullet_{27} M^\#$ Equal $2 * \mathrm{Det}_{27}(M)$):
       $$2 * x_+ * (x_- * v - \mathrm{norm}\;\Xi_2) + \langle Q, M^\#_Q \rangle_{\mathrm{Kac}} + \langle \Xi_1, M^\#_{\Xi_1} \rangle_{\mathrm{Kac}} = 2 * \mathrm{Det}_{27}(M),$$
       $$2 * x_- * (x_+ * v - \mathrm{norm}\;\Xi_1) + \langle \bar{Q}, \overline{M^\#_Q} \rangle_{\mathrm{Kac}} + \langle \Xi_2, M^\#_{\Xi_2} \rangle_{\mathrm{Kac}} = 2 * \mathrm{Det}_{27}(M),$$
       $$2 * v * (x_+ * x_- - \mathrm{norm}\;Q) + \langle \Xi_1, M^\#_{\Xi_1} \rangle_{\mathrm{Kac}} + \langle \Xi_2, M^\#_{\Xi_2} \rangle_{\mathrm{Kac}} = 2 * \mathrm{Det}_{27}(M).$$
    3. Eq. (69) Off-Diagonal Identity (Page 10: All 24 Off-Diagonal Split-Octonion Components of $M \bullet_{27} M^\#$ Vanish Identically by Artin's Alternative Laws):
       $$((x_+ + x_-) \bullet M^\#_Q + ((x_- * v - \mathrm{norm}\;\Xi_2) + (x_+ * v - \mathrm{norm}\;\Xi_1)) \bullet Q) +
         (\Xi_1 * \mathrm{conj}\;M^\#_{\Xi_2} + M^\#_{\Xi_1} * \mathrm{conj}\;\Xi_2) = 0,$$
       $$((x_+ + v) \bullet M^\#_{\Xi_1} + ((x_- * v - \mathrm{norm}\;\Xi_2) + (x_+ * x_- - \mathrm{norm}\;Q)) \bullet \Xi_1) +
         (Q * M^\#_{\Xi_2} + M^\#_Q * \Xi_2) = 0,$$
       $$((x_- + v) \bullet M^\#_{\Xi_2} + ((x_+ * v - \mathrm{norm}\;\Xi_1) + (x_+ * x_- - \mathrm{norm}\;Q)) \bullet \Xi_2) +
         (\mathrm{conj}\;Q * M^\#_{\Xi_1} + \mathrm{conj}\;M^\#_Q * \Xi_1) = 0.$$ -/
theorem albertZorn27D_freudenthal_sharp_and_determinant_law
    (x_plus x_minus v : R) (Q Ξ₁ Ξ₂ : ZornVectorMatrix R) :
    let S_xp := x_minus * v - norm Ξ₂
    let S_xm := x_plus * v - norm Ξ₁
    let S_v := x_plus * x_minus - norm Q
    let S_Q := albertZornSharpQ v Q Ξ₁ Ξ₂
    let S_Xi1 := albertZornSharpXi1 x_minus Q Ξ₁ Ξ₂
    let S_Xi2 := albertZornSharpXi2 x_plus Q Ξ₁ Ξ₂
    let det27 := albertZornDet x_plus x_minus v Q Ξ₁ Ξ₂
    trace ((Q * Ξ₂) * conj Ξ₁) = trace (Q * (Ξ₂ * conj Ξ₁)) ∧
    2 * x_plus * S_xp + zornKacMoodyPairing Q S_Q + zornKacMoodyPairing Ξ₁ S_Xi1 = 2 * det27 ∧
    2 * x_minus * S_xm + zornKacMoodyPairing (conj Q) (conj S_Q) + zornKacMoodyPairing Ξ₂ S_Xi2 = 2 * det27 ∧
    2 * v * S_v + zornKacMoodyPairing Ξ₁ S_Xi1 + zornKacMoodyPairing Ξ₂ S_Xi2 = 2 * det27 ∧
    ((x_plus + x_minus) • S_Q + (S_xp + S_xm) • Q) + (Ξ₁ * conj S_Xi2 + S_Xi1 * conj Ξ₂) = 0 ∧
    ((x_plus + v) • S_Xi1 + (S_xp + S_v) • Ξ₁) + (Q * S_Xi2 + S_Q * Ξ₂) = 0 ∧
    ((x_minus + v) • S_Xi2 + (S_xm + S_v) • Ξ₂) + (conj Q * S_Xi1 + conj S_Q * Ξ₁) = 0 := by
  intro S_xp S_xm S_v S_Q S_Xi1 S_Xi2 det27
  have h_assoc : trace ((Q * Ξ₂) * conj Ξ₁) = trace (Q * (Ξ₂ * conj Ξ₁)) :=
    trace_mul_assoc Q Ξ₂ (conj Ξ₁)
  have h_pair_Q : zornKacMoodyPairing Q S_Q = trace ((Q * Ξ₂) * conj Ξ₁) - 2 * v * norm Q := by
    dsimp [zornKacMoodyPairing, S_Q, albertZornSharpQ]
    change trace (mul Q (conj (add (mul Ξ₁ (conj Ξ₂)) (neg (smul v Q))))) = _
    rw [conj_add, conj_neg, conj_mul, conj_conj, conj_smul,
        mul_add, mul_neg, mul_smul, trace_add, trace_neg, trace_smul,
        conj_norm_identity_left, trace_scalar, ← trace_mul_assoc Q Ξ₂ (conj Ξ₁)]
    ring
  have h_pair_Xi1 : zornKacMoodyPairing Ξ₁ S_Xi1 = trace ((Q * Ξ₂) * conj Ξ₁) - 2 * x_minus * norm Ξ₁ := by
    dsimp [zornKacMoodyPairing, S_Xi1, albertZornSharpXi1]
    change trace (mul Ξ₁ (conj (add (mul Q Ξ₂) (neg (smul x_minus Ξ₁))))) = _
    rw [conj_add, conj_neg, conj_smul,
        mul_add, mul_neg, mul_smul, trace_add, trace_neg, trace_smul,
        conj_norm_identity_left, trace_scalar, trace_mul_conj_comm Ξ₁ (mul Q Ξ₂)]
    ring
  have h_pair_Xi2 : zornKacMoodyPairing Ξ₂ S_Xi2 = trace ((Q * Ξ₂) * conj Ξ₁) - 2 * x_plus * norm Ξ₂ := by
    dsimp [zornKacMoodyPairing, S_Xi2, albertZornSharpXi2]
    change trace (mul Ξ₂ (conj (add (mul (conj Q) Ξ₁) (neg (smul x_plus Ξ₂))))) = _
    have h_cyc : trace (mul Ξ₂ (mul (conj Ξ₁) Q)) = trace (mul (mul Q Ξ₂) (conj Ξ₁)) := by
      rw [← trace_mul_assoc Ξ₂ (conj Ξ₁) Q, ← trace_mul_cyclic Q Ξ₂ (conj Ξ₁)]
    rw [conj_add, conj_neg, conj_mul, conj_conj, conj_smul,
        mul_add, mul_neg, mul_smul, trace_add, trace_neg, trace_smul,
        conj_norm_identity_left, trace_scalar, h_cyc]
    ring
  have h_pair_conjQ : zornKacMoodyPairing (conj Q) (conj S_Q) = zornKacMoodyPairing Q S_Q := by
    dsimp [zornKacMoodyPairing]
    change trace (mul (conj Q) (conj (conj S_Q))) = trace (mul Q (conj S_Q))
    rw [trace_mul_conj_comm (conj Q) (conj S_Q), conj_conj]
    exact trace_mul_comm (conj S_Q) Q
  refine ⟨h_assoc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_pair_Q, h_pair_Xi1]
    dsimp [S_xp, det27, albertZornDet]
    ring
  · rw [h_pair_conjQ, h_pair_Q, h_pair_Xi2]
    dsimp [S_xm, det27, albertZornDet]
    ring
  · rw [h_pair_Xi1, h_pair_Xi2]
    dsimp [S_v, det27, albertZornDet]
    ring
  · have h1 : Ξ₁ * conj S_Xi2 = norm Ξ₁ • Q + -(x_plus • (Ξ₁ * conj Ξ₂)) := by
      dsimp [S_Xi2, albertZornSharpXi2]
      change mul Ξ₁ (conj (add (mul (conj Q) Ξ₁) (neg (smul x_plus Ξ₂)))) = _
      rw [conj_add, conj_neg, conj_mul, conj_conj, conj_smul,
          mul_add, mul_neg, mul_smul]
      exact congrArg (fun W => W + -(x_plus • (Ξ₁ * conj Ξ₂))) (kirmse_left_conj Ξ₁ Q)
    have h2 : S_Xi1 * conj Ξ₂ = norm Ξ₂ • Q + -(x_minus • (Ξ₁ * conj Ξ₂)) := by
      dsimp [S_Xi1, albertZornSharpXi1]
      change mul (add (mul Q Ξ₂) (neg (smul x_minus Ξ₁))) (conj Ξ₂) = _
      rw [add_mul, neg_mul, smul_mul]
      exact congrArg (fun W => W + -(x_minus • (Ξ₁ * conj Ξ₂))) (kirmse_right Ξ₂ Q)
    rw [h1, h2]
    dsimp [S_Q, albertZornSharpQ, S_xp, S_xm]
    ext <;>
      (simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
             add, neg, smul, zero]; ring)
  · have h1 : Q * S_Xi2 = norm Q • Ξ₁ + -(x_plus • (Q * Ξ₂)) := by
      dsimp [S_Xi2, albertZornSharpXi2]
      change mul Q (add (mul (conj Q) Ξ₁) (neg (smul x_plus Ξ₂))) = _
      rw [mul_add, mul_neg, mul_smul]
      exact congrArg (fun W => W + -(x_plus • (Q * Ξ₂))) (kirmse_left_conj Q Ξ₁)
    have h2 : S_Q * Ξ₂ = norm Ξ₂ • Ξ₁ + -(v • (Q * Ξ₂)) := by
      dsimp [S_Q, albertZornSharpQ]
      change mul (add (mul Ξ₁ (conj Ξ₂)) (neg (smul v Q))) Ξ₂ = _
      rw [add_mul, neg_mul, smul_mul]
      exact congrArg (fun W => W + -(v • (Q * Ξ₂))) (kirmse_right_conj Ξ₂ Ξ₁)
    rw [h1, h2]
    dsimp [S_Xi1, albertZornSharpXi1, S_xp, S_v]
    ext <;>
      (simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
             add, neg, smul, zero]; ring)
  · have h1 : conj Q * S_Xi1 = norm Q • Ξ₂ + -(x_minus • (conj Q * Ξ₁)) := by
      dsimp [S_Xi1, albertZornSharpXi1]
      change mul (conj Q) (add (mul Q Ξ₂) (neg (smul x_minus Ξ₁))) = _
      rw [mul_add, mul_neg, mul_smul]
      exact congrArg (fun W => W + -(x_minus • (conj Q * Ξ₁))) (kirmse_left Q Ξ₂)
    have h2 : conj S_Q * Ξ₁ = norm Ξ₁ • Ξ₂ + -(v • (conj Q * Ξ₁)) := by
      dsimp [S_Q, albertZornSharpQ]
      change mul (conj (add (mul Ξ₁ (conj Ξ₂)) (neg (smul v Q)))) Ξ₁ = _
      rw [conj_add, conj_neg, conj_mul, conj_conj, conj_smul,
          add_mul, neg_mul, smul_mul]
      exact congrArg (fun W => W + -(v • (conj Q * Ξ₁))) (kirmse_right_conj Ξ₁ Ξ₂)
    rw [h1, h2]
    dsimp [S_Xi2, albertZornSharpXi2, S_xm, S_v]
    ext <;>
      (simp [InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_smul_def, InfoGeometry.Algebra.zvm_zero_def,
             add, neg, smul, zero]; ring)

/-! ## 72. Steen H. Hansen (2026) Conformal Doublet Tower, Dirac–Majorana Dichotomy, & Triality Marriage in `ZornVectorMatrix R` (`Archetype LXXXIII`) -/

/-- **Theorem (`zorn_hansen_conformal_doublet_and_triality_marriage`)**:
    Over *any* commutative ring $R$ (`[CommRing R]`), for all 3-vectors $v, w, v_1, v_2, w_1, w_2 \in R^3$, let
    $D = \mathrm{zornGradeZero}\;1\;(-1)$, $e_1 = \mathrm{zornGradeZero}\;1\;0$, $e_2 = \mathrm{zornGradeZero}\;0\;1$,
    $U(v) = \langle 0, v, 0, 0 \rangle$, and $V(w) = \langle 0, 0, w, 0 \rangle$:
    1. Conformal Doublet Eigenvalue Selection & Anticommutation (Hansen 2026, Theorem 3.1 & Lemma 8.1):
       $$D * U(v) + -(U(v) * D) = U(v) + U(v), \qquad
         D * V(w) + -(V(w) * D) = -(V(w) + V(w)),$$
       $$D * U(v) + U(v) * D = 0, \qquad
         D * V(w) + V(w) * D = 0.$$
    2. Universal Nilpotency & Single-Projector Proportionality Law (Hansen Theorems 3.2 & 3.3):
       $$U(v) * U(v) = 0, \qquad V(w) * V(w) = 0,$$
       $$U(v) * V(w) = \mathrm{zornGradeZero}\;(v \cdot w)\;0, \qquad
         V(w) * U(v) = \mathrm{zornGradeZero}\;0\;(w \cdot v).$$
    3. Non-Abelian Octonionic Triality Upgrade of the Parabolic Nilradicals (Resolving Hansen §10.2):
       $$U(v_1) * U(v_2) + -(U(v_2) * U(v_1)) = \langle 0, 0, v_1 \times v_2 + v_1 \times v_2, 0 \rangle,$$
       $$V(w_1) * V(w_2) + -(V(w_2) * V(w_1)) = -\langle 0, w_1 \times w_2 + w_1 \times w_2, 0, 0 \rangle.$$
    4. Top-Rung Majorana vs. Dirac Sector Swap & Opposite-Sign Squares (Hansen Theorem 8.2):
       $$(U(v) + V(w)) * (U(v) + V(w)) = \mathrm{zornGradeZero}\;(v \cdot w)\;(w \cdot v),$$
       $$(U(v) + -V(w)) * (U(v) + -V(w)) = \mathrm{zornGradeZero}\;(-(v \cdot w))\;(-(w \cdot v)),$$
       $$(U(v) + V(w)) * e_1 = e_2 * (U(v) + V(w)), \qquad
         (U(v) + -V(w)) * e_1 = e_2 * (U(v) + -V(w)).$$ -/
theorem zorn_hansen_conformal_doublet_and_triality_marriage
    (v w v₁ v₂ w₁ w₂ : ZornVec3 R) :
    let D : ZornVectorMatrix R := zornGradeZero 1 (-1)
    let e₁ : ZornVectorMatrix R := zornGradeZero 1 0
    let e₂ : ZornVectorMatrix R := zornGradeZero 0 1
    let Uv : ZornVectorMatrix R := ⟨0, v, 0, 0⟩
    let Vw : ZornVectorMatrix R := ⟨0, 0, w, 0⟩
    let Uv1 : ZornVectorMatrix R := ⟨0, v₁, 0, 0⟩
    let Uv2 : ZornVectorMatrix R := ⟨0, v₂, 0, 0⟩
    let Vw1 : ZornVectorMatrix R := ⟨0, 0, w₁, 0⟩
    let Vw2 : ZornVectorMatrix R := ⟨0, 0, w₂, 0⟩
    let IM := Uv + Vw
    let ID := Uv + -Vw
    let cr_v := ZornVec3.cross v₁ v₂
    let cr_w := ZornVec3.cross w₁ w₂
    D * Uv + -(Uv * D) = Uv + Uv ∧
    D * Vw + -(Vw * D) = -(Vw + Vw) ∧
    D * Uv + Uv * D = 0 ∧
    D * Vw + Vw * D = 0 ∧
    Uv * Uv = 0 ∧
    Vw * Vw = 0 ∧
    Uv * Vw = zornGradeZero (ZornVec3.dot v w) 0 ∧
    Vw * Uv = zornGradeZero 0 (ZornVec3.dot w v) ∧
    Uv1 * Uv2 + -(Uv2 * Uv1) = ⟨0, 0, cr_v + cr_v, 0⟩ ∧
    Vw1 * Vw2 + -(Vw2 * Vw1) = -⟨0, cr_w + cr_w, 0, 0⟩ ∧
    IM * IM = zornGradeZero (ZornVec3.dot v w) (ZornVec3.dot w v) ∧
    ID * ID = zornGradeZero (-ZornVec3.dot v w) (-ZornVec3.dot w v) ∧
    IM * e₁ = e₂ * IM ∧
    ID * e₁ = e₂ * ID := by
  intro D e₁ e₂ Uv Vw Uv1 Uv2 Vw1 Vw2 IM ID cr_v cr_w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext
     · simp [D, e₁, e₂, Uv, Vw, Uv1, Uv2, Vw1, Vw2, IM, ID, cr_v,
             zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def,
             InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_zero_def,
             mul, add, neg, zero, ZornVec3.dot, Fin.sum_univ_three]
       try ring
     · rename_i i
       fin_cases i <;>
         (simp [D, e₁, e₂, Uv, Vw, Uv1, Uv2, Vw1, Vw2, IM, ID, cr_v, cr_w,
                zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def,
                InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_zero_def,
                mul, add, neg, zero, ZornVec3.cross];
          try ring)
     · rename_i i
       fin_cases i <;>
         (simp [D, e₁, e₂, Uv, Vw, Uv1, Uv2, Vw1, Vw2, IM, ID, cr_v,
                zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def,
                InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_zero_def,
                mul, add, neg, zero, ZornVec3.cross];
          try ring)
     · simp [D, e₁, e₂, Uv, Vw, Uv1, Uv2, Vw1, Vw2, IM, ID, cr_v,
             zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def,
             InfoGeometry.Algebra.zvm_neg_def, InfoGeometry.Algebra.zvm_zero_def,
             mul, add, neg, zero, ZornVec3.dot, Fin.sum_univ_three]
       try ring)

/-! ## 73. Zero Chiral 3-Volume, Parabolic Boundary Sheaf, & Universal Majorana Horizon Zero Modes in `ZornVectorMatrix R` (`Archetypes LXXXIV & LXXXV`) -/

/-- **Theorem (`zorn_zero_chiral_volume_and_parabolic_majorana_zero_modes`)**:
    Over *any* commutative ring $R$ (`[CommRing R]`), for all boundary coordinates $y_i, z_i, \xi, y, z, \xi' \in R$, let
    $v_i = ![0, y_i, z_i] \in \mathrm{ZornVec3}\;R$,
    $P_b = \langle 1, ![0, -y, -z], ![\xi, 0, 0], 0 \rangle \in \mathrm{ZornVectorMatrix}\;R$,
    $P_{\perp} = \mathrm{one} + -P_b$,
    $E_1 = \langle 0, ![0, y, z], 0, 0 \rangle$, and
    $Z_{\mathrm{Maj}} = \langle 0, 0, ![\xi', 0, 0], 0 \rangle$:
    1. Identical Vanishing of Chiral 3-Volume on the 2D Transverse Screen:
       $$v_1 \cdot (v_2 \times v_3) = 0 \qquad \text{and} \qquad (v_1 \times v_2) \cdot v_3 = 0.$$
    2. Parabolic Boundary Section Idempotence & Mutual Orthogonality:
       $$P_b * P_b = P_b, \qquad P_b * P_{\perp} = 0, \qquad P_{\perp} * P_b = 0.$$
    3. Universal Majorana Horizon Zero-Mode Stabilization & Nullspace Annihilation:
       $$E_1 * Z_{\mathrm{Maj}} = 0, \qquad Z_{\mathrm{Maj}} * E_1 = 0,$$
       $$P_b * Z_{\mathrm{Maj}} = 0, \qquad Z_{\mathrm{Maj}} * P_b = Z_{\mathrm{Maj}},$$
       $$P_{\perp} * Z_{\mathrm{Maj}} = Z_{\mathrm{Maj}}, \qquad Z_{\mathrm{Maj}} * P_{\perp} = 0.$$ -/
theorem zorn_zero_chiral_volume_and_parabolic_majorana_zero_modes
    (y₁ z₁ y₂ z₂ y₃ z₃ ξ y z ξ' : R) :
    let v₁ : ZornVec3 R := ![0, y₁, z₁]
    let v₂ : ZornVec3 R := ![0, y₂, z₂]
    let v₃ : ZornVec3 R := ![0, y₃, z₃]
    let P_b : ZornVectorMatrix R := ⟨1, ![0, -y, -z], ![ξ, 0, 0], 0⟩
    let P_perp : ZornVectorMatrix R := one + -P_b
    let E₁ : ZornVectorMatrix R := ⟨0, ![0, y, z], 0, 0⟩
    let Z_Maj : ZornVectorMatrix R := ⟨0, 0, ![ξ', 0, 0], 0⟩
    ZornVec3.dot v₁ (ZornVec3.cross v₂ v₃) = 0 ∧
    ZornVec3.dot (ZornVec3.cross v₁ v₂) v₃ = 0 ∧
    P_b * P_b = P_b ∧
    P_b * P_perp = 0 ∧
    P_perp * P_b = 0 ∧
    E₁ * Z_Maj = 0 ∧
    Z_Maj * E₁ = 0 ∧
    P_b * Z_Maj = 0 ∧
    Z_Maj * P_b = Z_Maj ∧
    P_perp * Z_Maj = Z_Maj ∧
    Z_Maj * P_perp = 0 := by
  intro v₁ v₂ v₃ P_b P_perp E₁ Z_Maj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [v₁, v₂, v₃, ZornVec3.dot, ZornVec3.cross]
  · simp [v₁, v₂, v₃, ZornVec3.dot, ZornVec3.cross]
  all_goals
    (ext
     · simp [P_b, P_perp, E₁, Z_Maj, InfoGeometry.Algebra.zvm_mul_def,
             InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_zero_def, mul, add, neg, zero, one,
             ZornVec3.dot, Fin.sum_univ_three]
       try ring
     · rename_i i
       fin_cases i <;>
         (simp [P_b, P_perp, E₁, Z_Maj, InfoGeometry.Algebra.zvm_mul_def,
                InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
                InfoGeometry.Algebra.zvm_zero_def, mul, add, neg, zero, one,
                ZornVec3.cross];
          try ring)
     · rename_i i
       fin_cases i <;>
         (simp [P_b, P_perp, E₁, Z_Maj, InfoGeometry.Algebra.zvm_mul_def,
                InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
                InfoGeometry.Algebra.zvm_zero_def, mul, add, neg, zero, one,
                ZornVec3.cross];
          try ring)
     · simp [P_b, P_perp, E₁, Z_Maj, InfoGeometry.Algebra.zvm_mul_def,
             InfoGeometry.Algebra.zvm_add_def, InfoGeometry.Algebra.zvm_neg_def,
             InfoGeometry.Algebra.zvm_zero_def, mul, add, neg, zero, one,
             ZornVec3.dot, Fin.sum_univ_three]
       try ring)

/-! ## 74. Chevalley–Lounesto–Shirokov Spinor Ideals & Associative Ket-Bra-Ket Calculus in `ZornVectorMatrix R` (`Archetypes LXXXVI & LXXXVII`) -/

/-- **Theorem (`zorn_chevalley_shirokov_spinor_bra_ket_and_associative_contact_sandwich`)**:
    Over *any* commutative ring $R$ (`[CommRing R]`), for all $a, b, a_1, \xi_1, b_2, \eta_2, a_3, \xi_3 \in R$
    and $v, w \in \mathrm{ZornVec3}\;R$, let
    $e_1 = \mathrm{zornGradeZero}\;1\;0$, $e_2 = \mathrm{zornGradeZero}\;0\;1$,
    $\mathrm{ket} = \langle a, 0, w, 0 \rangle$, $\mathrm{bra} = \langle b, v, 0, 0 \rangle$,
    $\psi_1 = \langle a_1, 0, ![\xi_1, 0, 0], 0 \rangle$,
    $\bar{\phi}_2 = \langle b_2, ![\eta_2, 0, 0], 0, 0 \rangle$, and
    $\psi_3 = \langle a_3, 0, ![\xi_3, 0, 0], 0 \rangle$:
    1. Peirce Absorption & Universal Bra-Ket / Ket-Bra Products:
       $$\mathrm{ket} * e_1 = \mathrm{ket}, \qquad \mathrm{ket} * e_2 = 0, \qquad
         e_1 * \mathrm{bra} = \mathrm{bra}, \qquad e_2 * \mathrm{bra} = 0,$$
       $$\mathrm{bra} * \mathrm{ket} = \mathrm{zornGradeZero}\;(b * a + v \cdot w)\;0,$$
       $$\mathrm{ket} * \mathrm{bra} = \langle a * b,\; a \bullet v,\; b \bullet w,\; w \cdot v \rangle.$$
    2. Associative Ket-Bra-Ket Sandwich on the Contact Spinor Ideal:
       $$(\psi_1 * \bar{\phi}_2) * \psi_3 = \psi_1 * (\bar{\phi}_2 * \psi_3) =
         \bigl\langle a_1 * (b_2 * a_3 + \eta_2 * \xi_3),\; 0,\; ![\xi_1 * (b_2 * a_3 + \eta_2 * \xi_3), 0, 0],\; 0 \bigr\rangle.$$ -/
theorem zorn_chevalley_shirokov_spinor_bra_ket_and_associative_contact_sandwich
    (a b a₁ ξ₁ b₂ η₂ a₃ ξ₃ : R) (v w : ZornVec3 R) :
    let e₁ : ZornVectorMatrix R := zornGradeZero 1 0
    let e₂ : ZornVectorMatrix R := zornGradeZero 0 1
    let ket : ZornVectorMatrix R := ⟨a, 0, w, 0⟩
    let bra : ZornVectorMatrix R := ⟨b, v, 0, 0⟩
    let ψ₁ : ZornVectorMatrix R := ⟨a₁, 0, ![ξ₁, 0, 0], 0⟩
    let φ₂_bar : ZornVectorMatrix R := ⟨b₂, ![η₂, 0, 0], 0, 0⟩
    let ψ₃ : ZornVectorMatrix R := ⟨a₃, 0, ![ξ₃, 0, 0], 0⟩
    let inner₂₃ : R := b₂ * a₃ + η₂ * ξ₃
    ket * e₁ = ket ∧
    ket * e₂ = 0 ∧
    e₁ * bra = bra ∧
    e₂ * bra = 0 ∧
    bra * ket = zornGradeZero (b * a + ZornVec3.dot v w) 0 ∧
    ket * bra = ⟨a * b, a • v, b • w, ZornVec3.dot w v⟩ ∧
    (ψ₁ * φ₂_bar) * ψ₃ = ψ₁ * (φ₂_bar * ψ₃) ∧
    (ψ₁ * φ₂_bar) * ψ₃ = ⟨a₁ * inner₂₃, 0, ![ξ₁ * inner₂₃, 0, 0], 0⟩ := by
  intro e₁ e₂ ket bra ψ₁ φ₂_bar ψ₃ inner₂₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext
     · simp [e₁, e₂, ket, bra, ψ₁, φ₂_bar, ψ₃, inner₂₃, zornGradeZero,
             InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
             mul, zero, ZornVec3.dot, Fin.sum_univ_three]
       try ring
     · rename_i i
       fin_cases i <;>
         (simp [e₁, e₂, ket, bra, ψ₁, φ₂_bar, ψ₃, inner₂₃, zornGradeZero,
                InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
                mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three];
          try ring)
     · rename_i i
       fin_cases i <;>
         (simp [e₁, e₂, ket, bra, ψ₁, φ₂_bar, ψ₃, inner₂₃, zornGradeZero,
                InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
                mul, zero, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three];
          try ring)
     · simp [e₁, e₂, ket, bra, ψ₁, φ₂_bar, ψ₃, inner₂₃, zornGradeZero,
             InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_zero_def,
             mul, zero, ZornVec3.dot, Fin.sum_univ_three]
       try ring)

/-! ## 75. Trifactor + Loxodromic Local Compass, Peirce-Doubled 4-Vector Potential, & Zorn–Riccati Möbius Fixed Point in `ZornVectorMatrix R` (`Archetypes LXXXVIII & LXXXIX`) -/

/-- **Theorem (`zorn_trifactor_loxodromic_compass_doubled_four_potential_and_riccati_fixed_point`)**:
    Over *any* commutative ring $R$ (`[CommRing R]`), for all $X \in \mathrm{ZornVectorMatrix}\;R$,
    $a, b, \lambda, \mu, \Delta \in R$, and $v, w, q \in \mathrm{ZornVec3}\;R$, let
    $e_1 = \mathrm{zornGradeZero}\;1\;0$, $e_2 = \mathrm{zornGradeZero}\;0\;1$,
    $A_+ = \langle a, v, 0, 0 \rangle$, $A_- = \langle 0, 0, w, b \rangle$,
    $P_{\mathrm{row}} = \langle 1, v, 0, 0 \rangle$, $P_{\mathrm{col}} = \langle 1, 0, w, 0 \rangle$,
    $U_+ = \langle 1, q, 0, 1 \rangle$, $U_- = \langle 1, -q, 0, 1 \rangle$, and
    $T_{\mathrm{tri}} = (\langle 1, 0, w, 1 \rangle * \mathrm{zornGradeZero}\;1\;\Delta) * \langle 1, v, 0, 1 \rangle$:
    1. Peirce-Doubled 4-Vector Potential Split & Cross-Pole Contraction:
       $$e_1 * X = \langle X.a, X.v, 0, 0 \rangle, \qquad e_2 * X = \langle 0, 0, X.w, X.b \rangle, \qquad
         e_1 * X + e_2 * X = X,$$
       $$A_+ * A_- = \langle v \cdot w,\; b \bullet v,\; 0,\; 0 \rangle, \qquad
         A_- * A_+ = \langle 0,\; 0,\; a \bullet w,\; w \cdot v \rangle.$$
    2. Compass Needle Idempotence & Trifactor Decomposition:
       $$P_{\mathrm{row}} * P_{\mathrm{row}} = P_{\mathrm{row}}, \qquad
         P_{\mathrm{col}} * P_{\mathrm{col}} = P_{\mathrm{col}},$$
       $$T_{\mathrm{tri}} = (P_{\mathrm{col}} * e_1) * P_{\mathrm{row}} + \mathrm{zornGradeZero}\;0\;\Delta.$$
    3. Moving-Frame Zorn–Riccati Operator & Exact Trifactor Schur Residual / Fixed Point:
       $$\bigl((U_- * X) * U_+\bigr).v = (X.a - q \cdot X.w) \bullet q + -(X.b \bullet q) + X.v,$$
       $$-(T_{\mathrm{tri}}.w \cdot v) \bullet v + T_{\mathrm{tri}}.b \bullet v + T_{\mathrm{tri}}.a \bullet v + -T_{\mathrm{tri}}.v = \Delta \bullet v.$$ -/
theorem zorn_trifactor_loxodromic_compass_doubled_four_potential_and_riccati_fixed_point
    (X : ZornVectorMatrix R) (a b Δ : R) (v w q : ZornVec3 R) :
    let e₁ : ZornVectorMatrix R := zornGradeZero 1 0
    let e₂ : ZornVectorMatrix R := zornGradeZero 0 1
    let A_plus : ZornVectorMatrix R := ⟨a, v, 0, 0⟩
    let A_minus : ZornVectorMatrix R := ⟨0, 0, w, b⟩
    let P_row : ZornVectorMatrix R := ⟨1, v, 0, 0⟩
    let P_col : ZornVectorMatrix R := ⟨1, 0, w, 0⟩
    let U_plus : ZornVectorMatrix R := ⟨1, q, 0, 1⟩
    let U_minus : ZornVectorMatrix R := ⟨1, -q, 0, 1⟩
    let T_tri : ZornVectorMatrix R := (⟨1, 0, w, 1⟩ * zornGradeZero 1 Δ) * ⟨1, v, 0, 1⟩
    e₁ * X = ⟨X.a, X.v, 0, 0⟩ ∧
    e₂ * X = ⟨0, 0, X.w, X.b⟩ ∧
    e₁ * X + e₂ * X = X ∧
    A_plus * A_minus = ⟨ZornVec3.dot v w, b • v, 0, 0⟩ ∧
    A_minus * A_plus = ⟨0, 0, a • w, ZornVec3.dot w v⟩ ∧
    P_row * P_row = P_row ∧
    P_col * P_col = P_col ∧
    T_tri = (P_col * e₁) * P_row + zornGradeZero 0 Δ ∧
    ((U_minus * X) * U_plus).v = (X.a - ZornVec3.dot q X.w) • q + -(X.b • q) + X.v ∧
    (-(ZornVec3.dot T_tri.w v)) • v + T_tri.b • v + T_tri.a • v + -T_tri.v = Δ • v := by
  intro e₁ e₂ A_plus A_minus P_row P_col U_plus U_minus T_tri
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext
    · simp [e₁, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [e₁, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [e₁, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · simp [e₁, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [e₂, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [e₂, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [e₂, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · simp [e₂, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [e₁, e₂, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def, mul, add, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [e₁, e₂, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def, mul, add, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [e₁, e₂, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def, mul, add, ZornVec3.cross]
    · simp [e₁, e₂, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def, mul, add, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [A_plus, A_minus, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [A_plus, A_minus, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [A_plus, A_minus, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · simp [A_plus, A_minus, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [A_plus, A_minus, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;> simp [A_plus, A_minus, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;> simp [A_plus, A_minus, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · simp [A_plus, A_minus, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [P_row, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        simp [P_row, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · rename_i i; fin_cases i <;>
        (simp [P_row, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross] <;>
         (change _ = (0 : R); ring))
    · simp [P_row, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [P_col, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
    · rename_i i; fin_cases i <;>
        (simp [P_col, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross] <;>
         (change _ = (0 : R); ring))
    · rename_i i; fin_cases i <;>
        simp [P_col, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.cross]
    · simp [P_col, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, Fin.sum_univ_three]
  · ext
    · simp [T_tri, P_col, P_row, e₁, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def, mul, add, ZornVec3.dot, Fin.sum_univ_three]; try ring
    · rename_i i; fin_cases i <;> (simp [T_tri, P_col, P_row, e₁, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def, mul, add, ZornVec3.cross]; try ring)
    · rename_i i; fin_cases i <;> (simp [T_tri, P_col, P_row, e₁, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def, mul, add, ZornVec3.cross]; try ring)
    · simp [T_tri, P_col, P_row, e₁, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, InfoGeometry.Algebra.zvm_add_def, mul, add, ZornVec3.dot, Fin.sum_univ_three]; try ring
  · ext i
    fin_cases i <;>
      (simp [U_minus, U_plus, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three];
       try ring)
  · ext i
    fin_cases i <;>
      (simp [T_tri, zornGradeZero, InfoGeometry.Algebra.zvm_mul_def, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three];
       try ring)

end InfoGeometry.Algebra.ZornVectorMatrix
