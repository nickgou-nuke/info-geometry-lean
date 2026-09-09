import InfoGeometry.Algebra.ZornDerivationBridge

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

private noncomputable def bundledAssociator
    (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  (X * Y) * Z - X * (Y * Z)

private lemma bundledAssociator_add_left (X Y Z W : ZornVectorMatrix R) :
    bundledAssociator (X + Y) Z W =
      bundledAssociator X Z W + bundledAssociator Y Z W := by
  simp only [bundledAssociator, _root_.add_mul]
  abel

private lemma bundledAssociator_add_mid (X Y Z W : ZornVectorMatrix R) :
    bundledAssociator X (Y + Z) W =
      bundledAssociator X Y W + bundledAssociator X Z W := by
  simp only [bundledAssociator, _root_.add_mul, _root_.mul_add]
  abel

private lemma bundledAssociator_add_right (X Y Z W : ZornVectorMatrix R) :
    bundledAssociator X Y (Z + W) =
      bundledAssociator X Y Z + bundledAssociator X Y W := by
  simp only [bundledAssociator, _root_.mul_add]
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
  simp only [bundledAssociator]
  noncomm_ring

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
    simpa only [_root_.add_zero, _root_.sub_zero] using h1
  rw [bundledAssociator_swap23 (X * X) Z Y,
    bundledAssociator_swap23 X (X * Z) Y, bundledAssociator_left_alt,
    bundledAssociator_swap23 X Z Y, bundledAssociator_left_alt] at h2
  have e2 :
      -bundledAssociator (X * X) Y Z + bundledAssociator X Y (X * Z) +
        X * bundledAssociator X Y Z = 0 := by
    rw [show (0 : ZornVectorMatrix R) * Y = 0 from zero_mul Y] at h2
    simpa only [neg_neg, _root_.add_zero, _root_.sub_zero,
      _root_.mul_neg, sub_neg_eq_add] using h2
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
    simpa only [neg_neg, _root_.add_zero, _root_.sub_zero,
      _root_.mul_neg, sub_neg_eq_add] using h3
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
  simp only [_root_.sub_zero] at h
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
      simp only [bundledAssociator]
      noncomm_ring
    _ = ((X * Y) * Z) * X - bundledAssociator X Y Z * X := by rw [hxy]
    _ = (X * (Y * Z)) * X := by
      simp only [bundledAssociator]
      noncomm_ring
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
    rw [h_zero, sub_zero] at h_teich_rearr
    exact h_teich_rearr
  have h_def : bundledAssociator (Z * X) Z Y + bundledAssociator Z X (Z * Y) =
      ((Z * X) * Z) * Y - Z * (X * (Z * Y)) := by
    simp only [bundledAssociator]
    noncomm_ring
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
      simpa only [_root_.add_zero, _root_.sub_zero] using h1
    rw [bundledAssociator_swap23 (X * X) Z Y, bundledAssociator_swap23 X (X * Z) Y,
      bundledAssociator_left_alt, bundledAssociator_swap23 X Z Y, bundledAssociator_left_alt] at h2
    have e2 : -bundledAssociator (X * X) Y Z + bundledAssociator X Y (X * Z) + X * bundledAssociator X Y Z = 0 := by
      rw [show (0 : ZornVectorMatrix R) * Y = 0 from zero_mul Y] at h2
      simpa only [neg_neg, _root_.add_zero, _root_.sub_zero, _root_.mul_neg, sub_neg_eq_add] using h2
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
    rw [h_zero, sub_zero] at h_teich_rearr
    exact h_teich_rearr
  have h_def : bundledAssociator (Y * X) Z X + bundledAssociator Y X (Z * X) =
      ((Y * X) * Z) * X - Y * (X * (Z * X)) := by
    simp only [bundledAssociator]
    noncomm_ring
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
  simp only [_root_.sub_mul, _root_.mul_sub, smul_mul_assoc,
    mul_smul_comm, smul_sub, smul_smul]
  rw [hprod, hY, hZ]
  module

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

end InfoGeometry.Algebra.ZornVectorMatrix
