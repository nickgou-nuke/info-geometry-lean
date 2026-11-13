/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv

/-!
# The ordered Clifford-algebra maps underlying Freed's Pin suspensions

For any quadratic form `Q`, the two target forms are `Q ⊕ (-r²)` and `Q ⊕ r²`.
The source forms are respectively `Q` and `-Q`.  In both cases a source vector
is sent to the ordered target product `(v, 0) * (0, 1)` from Freed,
*Index Theory on Pin Manifolds*, equations (1.9)--(1.10).

Mathlib's `equivEven` uses the reverse order `(0, 1) * (v, 0)`.  Grade
involution corrects that order for the positive suspension.  For the negative
suspension the sign is supplied by `evenEquivEvenNeg`.  Both maps are algebra
equivalences onto the actual even Clifford subalgebra.

These statements concern the universal Clifford algebras and their native even
subalgebras.  Group membership, Lie-group components, Dirac operators, Morita
equivalences, and index-theoretic conclusions require separate constructions.
-/

namespace InfoGeometry.Clifford.FreedCliffordSuspension

open CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The target quadratic form for the `Pin⁺` suspension. -/
abbrev positiveForm (Q : QuadraticForm R M) : QuadraticForm R (M × R) :=
  Q.prod (-QuadraticMap.sq (R := R))

/-- The target quadratic form for the `Pin⁻` suspension.  This presentation
keeps the native even-negation equivalence free of transports. -/
abbrev negativeForm (Q : QuadraticForm R M) : QuadraticForm R (M × R) :=
  -(positiveForm (-Q))

variable (Q : QuadraticForm R M)

theorem positiveForm_apply (x : M × R) :
    positiveForm Q x = Q x.1 - x.2 * x.2 :=
  CliffordAlgebra.EquivEven.Q'_apply Q x

theorem negativeForm_eq : negativeForm Q = Q.prod (QuadraticMap.sq (R := R)) := by
  ext x
  simp [negativeForm, positiveForm, add_comm]

theorem negativeForm_apply (x : M × R) :
    negativeForm Q x = Q x.1 + x.2 * x.2 := by
  rw [negativeForm_eq]
  rfl

theorem positive_extra_sq :
    ι (positiveForm Q) (0, 1) * ι (positiveForm Q) (0, 1) = -1 :=
  EquivEven.e0_mul_e0 Q

theorem negative_extra_sq :
    ι (negativeForm Q) (0, 1) * ι (negativeForm Q) (0, 1) = 1 := by
  rw [ι_sq_scalar, negativeForm_apply]
  simp

theorem positive_extra_mul_vector (m : M) :
    ι (positiveForm Q) (0, 1) * ι (positiveForm Q) (m, 0) =
      -(ι (positiveForm Q) (m, 0) * ι (positiveForm Q) (0, 1)) :=
  ι_mul_ι_comm_of_isOrtho (QuadraticMap.IsOrtho.inr_inl m 1)

theorem negative_extra_mul_vector (m : M) :
    ι (negativeForm Q) (0, 1) * ι (negativeForm Q) (m, 0) =
      -(ι (negativeForm Q) (m, 0) * ι (negativeForm Q) (0, 1)) := by
  apply ι_mul_ι_comm_of_isOrtho
  rw [negativeForm_eq]
  exact QuadraticMap.IsOrtho.inr_inl m 1

/-- The positive suspension equivalence, with Freed's vector order. -/
def positiveEquiv : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra.even (positiveForm Q) :=
  (CliffordAlgebra.involuteEquiv (Q := Q)).trans (CliffordAlgebra.equivEven Q)

/-- The negative suspension equivalence, with Freed's vector order. -/
def negativeEquiv : CliffordAlgebra (-Q) ≃ₐ[R] CliffordAlgebra.even (negativeForm Q) :=
  (CliffordAlgebra.equivEven (-Q)).trans
    (CliffordAlgebra.evenEquivEvenNeg (positiveForm (-Q)))

/-- The positive suspension as an algebra map into the full target algebra. -/
def positiveMap : CliffordAlgebra Q →ₐ[R] CliffordAlgebra (positiveForm Q) :=
  (CliffordAlgebra.even (positiveForm Q)).val.comp (positiveEquiv Q).toAlgHom

/-- The negative suspension as an algebra map into the full target algebra. -/
def negativeMap : CliffordAlgebra (-Q) →ₐ[R] CliffordAlgebra (negativeForm Q) :=
  (CliffordAlgebra.even (negativeForm Q)).val.comp (negativeEquiv Q).toAlgHom

theorem positiveMap_injective : Function.Injective (positiveMap Q) := by
  intro x y h
  exact (positiveEquiv Q).injective (Subtype.ext h)

theorem negativeMap_injective : Function.Injective (negativeMap Q) := by
  intro x y h
  exact (negativeEquiv Q).injective (Subtype.ext h)

theorem positiveMap_mem_even (x : CliffordAlgebra Q) :
    positiveMap Q x ∈ CliffordAlgebra.even (positiveForm Q) :=
  (positiveEquiv Q x).property

theorem negativeMap_mem_even (x : CliffordAlgebra (-Q)) :
    negativeMap Q x ∈ CliffordAlgebra.even (negativeForm Q) :=
  (negativeEquiv Q x).property

theorem positiveMap_range : (positiveMap Q).range = CliffordAlgebra.even (positiveForm Q) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact positiveMap_mem_even Q y
  · intro hx
    obtain ⟨y, hy⟩ := (positiveEquiv Q).surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

theorem negativeMap_range : (negativeMap Q).range = CliffordAlgebra.even (negativeForm Q) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact negativeMap_mem_even Q y
  · intro hx
    obtain ⟨y, hy⟩ := (negativeEquiv Q).surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

/-- Freed's generator formula for `Pin⁺`, including its noncommutative order. -/
theorem positiveMap_ι (m : M) :
    positiveMap Q (ι Q m) =
      ι (positiveForm Q) (m, 0) * ι (positiveForm Q) (0, 1) := by
  change (CliffordAlgebra.toEven Q (CliffordAlgebra.involute (ι Q m)) :
    CliffordAlgebra (positiveForm Q)) = _
  rw [involute_ι, map_neg, Subalgebra.coe_neg, toEven_ι]
  exact EquivEven.neg_e0_mul_v Q m

/-- Freed's generator formula for `Pin⁻`.  Its source has quadratic form `-Q`. -/
theorem negativeMap_ι (m : M) :
    negativeMap Q (ι (-Q) m) =
      ι (negativeForm Q) (m, 0) * ι (negativeForm Q) (0, 1) := by
  have hpair : CliffordAlgebra.toEven (-Q) (ι (-Q) m) =
      (CliffordAlgebra.even.ι (positiveForm (-Q))).bilin (0, 1) (m, 0) := by
    apply Subtype.ext
    exact toEven_ι (-Q) m
  change (CliffordAlgebra.evenToNeg (positiveForm (-Q)) (negativeForm Q) rfl
    (CliffordAlgebra.toEven (-Q) (ι (-Q) m)) : CliffordAlgebra (negativeForm Q)) = _
  rw [hpair, evenToNeg_ι]
  change -(ι (negativeForm Q) (0, 1) * ι (negativeForm Q) (m, 0)) = _
  rw [negative_extra_mul_vector, neg_neg]

/-- The positive inverse on all even vector pairs, not only on the suspended generators. -/
theorem positiveEquiv_symm_pair (a b : M × R) :
    (positiveEquiv Q).symm ((CliffordAlgebra.even.ι (positiveForm Q)).bilin a b) =
      (ι Q a.1 - algebraMap R _ a.2) * (ι Q b.1 + algebraMap R _ b.2) := by
  change CliffordAlgebra.involute
    (CliffordAlgebra.ofEven Q ((CliffordAlgebra.even.ι (positiveForm Q)).bilin a b)) = _
  rw [ofEven_ι]
  simpa only [map_mul, map_add, map_sub, map_neg, involute_ι, AlgHom.commutes,
    sub_eq_add_neg, neg_add, neg_neg] using
    neg_mul_neg (ι Q a.1 - algebraMap R _ a.2) (ι Q b.1 + algebraMap R _ b.2)

/-- The negative inverse retains the ordered pair sign supplied by even negation. -/
theorem negativeEquiv_symm_pair (a b : M × R) :
    (negativeEquiv Q).symm ((CliffordAlgebra.even.ι (negativeForm Q)).bilin a b) =
      -((ι (-Q) a.1 + algebraMap R _ a.2) *
        (ι (-Q) b.1 - algebraMap R _ b.2)) := by
  change CliffordAlgebra.ofEven (-Q)
    (CliffordAlgebra.evenToNeg (negativeForm Q) (positiveForm (-Q))
      (neg_neg (positiveForm (-Q))).symm
      ((CliffordAlgebra.even.ι (negativeForm Q)).bilin a b)) = _
  rw [evenToNeg_ι, map_neg, ofEven_ι]

/-- An ordered pair of positive source vectors has no extra sign after suspension. -/
theorem positiveMap_ι_mul_ι (m n : M) :
    positiveMap Q (ι Q m * ι Q n) =
      ι (positiveForm Q) (m, 0) * ι (positiveForm Q) (n, 0) := by
  rw [map_mul, positiveMap_ι, positiveMap_ι]
  change (EquivEven.v Q m * EquivEven.e0 Q) *
    (EquivEven.v Q n * EquivEven.e0 Q) = EquivEven.v Q m * EquivEven.v Q n
  rw [mul_assoc, ← mul_assoc (EquivEven.e0 Q), EquivEven.e0_mul_v_mul_e0]

/-- The corresponding ordered pair in the negative suspension acquires a minus sign. -/
theorem negativeMap_ι_mul_ι (m n : M) :
    negativeMap Q (ι (-Q) m * ι (-Q) n) =
      -(ι (negativeForm Q) (m, 0) * ι (negativeForm Q) (n, 0)) := by
  rw [map_mul, negativeMap_ι, negativeMap_ι]
  calc
    (ι (negativeForm Q) (m, 0) * ι (negativeForm Q) (0, 1)) *
        (ι (negativeForm Q) (n, 0) * ι (negativeForm Q) (0, 1)) =
        ι (negativeForm Q) (m, 0) *
          ((ι (negativeForm Q) (0, 1) * ι (negativeForm Q) (n, 0)) *
            ι (negativeForm Q) (0, 1)) := by simp only [mul_assoc]
    _ = ι (negativeForm Q) (m, 0) *
          ((-(ι (negativeForm Q) (n, 0) * ι (negativeForm Q) (0, 1))) *
            ι (negativeForm Q) (0, 1)) := by rw [negative_extra_mul_vector]
    _ = -(ι (negativeForm Q) (m, 0) * ι (negativeForm Q) (n, 0)) := by
      rw [neg_mul, mul_assoc (ι (negativeForm Q) (n, 0)), negative_extra_sq,
        mul_one, mul_neg]

theorem positive_generator_sq (m : M) :
    (ι (positiveForm Q) (m, 0) * ι (positiveForm Q) (0, 1)) *
        (ι (positiveForm Q) (m, 0) * ι (positiveForm Q) (0, 1)) =
      algebraMap R _ (Q m) := by
  simpa only [map_mul, positiveMap_ι, AlgHom.commutes] using
    congrArg (positiveMap Q) (ι_sq_scalar Q m)

theorem negative_generator_sq (m : M) :
    (ι (negativeForm Q) (m, 0) * ι (negativeForm Q) (0, 1)) *
        (ι (negativeForm Q) (m, 0) * ι (negativeForm Q) (0, 1)) =
      -algebraMap R _ (Q m) := by
  simpa only [map_mul, negativeMap_ι, AlgHom.commutes, neg_apply, map_neg] using
    congrArg (negativeMap Q) (ι_sq_scalar (-Q) m)

theorem positive_normalized_generator_sq (m : M) (hm : Q m = 1) :
    (ι (positiveForm Q) (m, 0) * ι (positiveForm Q) (0, 1)) *
        (ι (positiveForm Q) (m, 0) * ι (positiveForm Q) (0, 1)) = 1 := by
  rw [positive_generator_sq, hm, map_one]

theorem negative_normalized_generator_sq (m : M) (hm : Q m = 1) :
    (ι (negativeForm Q) (m, 0) * ι (negativeForm Q) (0, 1)) *
        (ι (negativeForm Q) (m, 0) * ι (negativeForm Q) (0, 1)) = -1 := by
  rw [negative_generator_sq, hm, map_one]

theorem reverse_positiveMap_ι (m : M) :
    CliffordAlgebra.reverse (positiveMap Q (ι Q m)) = -positiveMap Q (ι Q m) := by
  simp only [positiveMap_ι, reverse.map_mul, reverse_ι]
  exact positive_extra_mul_vector Q m

theorem reverse_negativeMap_ι (m : M) :
    CliffordAlgebra.reverse (negativeMap Q (ι (-Q) m)) = -negativeMap Q (ι (-Q) m) := by
  simp only [negativeMap_ι, reverse.map_mul, reverse_ι]
  exact negative_extra_mul_vector Q m

/-- Suspension turns source Clifford conjugation into target reversion. -/
theorem positiveMap_reverse_involute (x : CliffordAlgebra Q) :
    positiveMap Q (CliffordAlgebra.reverse (CliffordAlgebra.involute x)) =
      CliffordAlgebra.reverse (positiveMap Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, reverse.commutes]
  | ι m =>
    rw [involute_ι, map_neg, reverse_ι, map_neg, reverse_positiveMap_ι]
  | mul x y hx hy => simp only [map_mul, reverse.map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The same conjugation/reversion compatibility holds for the negative suspension. -/
theorem negativeMap_reverse_involute (x : CliffordAlgebra (-Q)) :
    negativeMap Q (CliffordAlgebra.reverse (CliffordAlgebra.involute x)) =
      CliffordAlgebra.reverse (negativeMap Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, reverse.commutes]
  | ι m =>
    rw [involute_ι, map_neg, reverse_ι, map_neg, reverse_negativeMap_ι]
  | mul x y hx hy => simp only [map_mul, reverse.map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end InfoGeometry.Clifford.FreedCliffordSuspension
