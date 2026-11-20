/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fintype.Card

/-!
# Boundary reconstruction, hidden states, and ordered operator lifting

For encoding `E` and decoding `D`, boundary consistency is the explicit
hypothesis `E.comp D = id`. It constructs a bulk projector `D.comp E`, not
full recovery. The bulk splits into decoded boundary data and `ker E`.
Boundary endomorphisms lift faithfully into the resulting noncommutative
corner; composition order is never exchanged. No metric, area law, or bulk
field equation is inferred from these algebraic results.

Source motivation: holographic white paper v6.1, section 2.5, pp. 12-13.
-/

namespace InfoGeometry.Holographic.BoundaryReconstruction

section Modules

variable {R Bulk Boundary : Type*} [Ring R]
variable [AddCommGroup Bulk] [Module R Bulk]
variable [AddCommGroup Boundary] [Module R Boundary]
variable (E : Bulk →ₗ[R] Boundary) (D : Boundary →ₗ[R] Bulk)

theorem encode_decode (h : E.comp D = LinearMap.id) (b : Boundary) : E (D b) = b :=
  LinearMap.congr_fun h b

theorem decode_injective (h : E.comp D = LinearMap.id) : Function.Injective D :=
  (show Function.LeftInverse E D from encode_decode E D h).injective

theorem encode_surjective (h : E.comp D = LinearMap.id) : Function.Surjective E :=
  (show Function.RightInverse D E from encode_decode E D h).surjective

/-- The ordered encoding/decoding composite is an idempotent bulk operator. -/
theorem reconstruction_idempotent (h : E.comp D = LinearMap.id) :
    (D.comp E).comp (D.comp E) = D.comp E := by
  ext x
  change D (E (D (E x))) = D (E x)
  rw [encode_decode E D h]

theorem encode_reconstruction (h : E.comp D = LinearMap.id) :
    E.comp (D.comp E) = E := by
  rw [← LinearMap.comp_assoc, h, LinearMap.id_comp]

theorem reconstruction_decode (h : E.comp D = LinearMap.id) :
    (D.comp E).comp D = D := by
  rw [LinearMap.comp_assoc, h, LinearMap.comp_id]

/-- A bulk state is fixed by reconstruction exactly when it is decoded data. -/
theorem reconstruction_eq_self_iff (h : E.comp D = LinearMap.id) (x : Bulk) :
    D (E x) = x ↔ x ∈ LinearMap.range D := by
  constructor
  · intro hx
    exact ⟨E x, hx⟩
  · rintro ⟨b, rfl⟩
    rw [encode_decode E D h]

theorem range_reconstruction (h : E.comp D = LinearMap.id) :
    LinearMap.range (D.comp E) = LinearMap.range D := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨E y, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨D b, by simp [encode_decode E D h]⟩

theorem ker_reconstruction (h : E.comp D = LinearMap.id) :
    LinearMap.ker (D.comp E) = LinearMap.ker E := by
  ext x
  change D (E x) = 0 ↔ E x = 0
  constructor
  · intro hx
    apply decode_injective E D h
    simpa using hx
  · intro hx
    simp [hx]

/-- The unrecovered remainder is exactly the kernel of the encoding. -/
theorem range_hidden (h : E.comp D = LinearMap.id) :
    LinearMap.range (LinearMap.id - D.comp E) = LinearMap.ker E :=
  (LinearMap.ker_eq_range_of_comp_eq_id h).symm

/-- A constructive splitting, with inverse `(b, k) ↦ D b + k`. -/
def splitEquiv (h : E.comp D = LinearMap.id) :
    Bulk ≃ₗ[R] Boundary × LinearMap.ker E where
  toFun x := (E x, ⟨x - D (E x), by
    change E (x - D (E x)) = 0
    rw [map_sub, encode_decode E D h, sub_self]⟩)
  invFun y := D y.1 + y.2
  left_inv x := by simp
  right_inv y := by
    rcases y with ⟨b, k⟩
    have hk : E k = 0 := k.property
    apply Prod.ext
    · simp [encode_decode E D h, hk]
    · apply Subtype.ext
      simp [encode_decode E D h, hk]
  map_add' x y := by
    apply Prod.ext
    · exact E.map_add x y
    · apply Subtype.ext
      simp [map_add, add_sub_add_comm]
  map_smul' r x := by
    apply Prod.ext
    · exact E.map_smul r x
    · apply Subtype.ext
      simp [map_smul, smul_sub]

/-- Full recovery is an extra condition, equivalent here to injective encoding. -/
theorem full_reconstruction_iff_injective (h : E.comp D = LinearMap.id) :
    D.comp E = LinearMap.id ↔ Function.Injective E := by
  constructor
  · intro hfull
    exact (show Function.LeftInverse D E from fun x => LinearMap.congr_fun hfull x).injective
  · intro hinj
    ext x
    apply hinj
    exact encode_decode E D h (E x)

/-- Different states differing by a nonzero hidden component have the same encoding. -/
theorem hidden_state_collision {k : Bulk} (hk : k ∈ LinearMap.ker E) (hne : k ≠ 0)
    (x : Bulk) : E (x + k) = E x ∧ x + k ≠ x := by
  constructor
  · simp [map_add, show E k = 0 from hk]
  · intro heq
    apply hne
    exact (add_right_inj x).mp (by simpa using heq)

/-- The boundary operator acts in the decoded bulk corner. -/
def liftOperator (A : Module.End R Boundary) : Module.End R Bulk :=
  D.comp (A.comp E)

theorem liftOperator_add (A B : Module.End R Boundary) :
    liftOperator E D (A + B) = liftOperator E D A + liftOperator E D B := by
  ext x
  simp [liftOperator]

/-- Ordered products are preserved, without a commutativity hypothesis. -/
theorem liftOperator_mul (h : E.comp D = LinearMap.id)
    (A B : Module.End R Boundary) :
    liftOperator E D (A * B) = liftOperator E D A * liftOperator E D B := by
  ext x
  change D (A (B (E x))) = D (A (E (D (B (E x)))))
  rw [encode_decode E D h]

theorem liftOperator_one : liftOperator E D 1 = D.comp E := by
  ext x
  rfl

/-- A native non-unital ring homomorphism; the unit maps to the bulk projector. -/
def liftOperatorHom (h : E.comp D = LinearMap.id) :
    Module.End R Boundary →ₙ+* Module.End R Bulk where
  toFun := liftOperator E D
  map_zero' := by
    ext x
    simp [liftOperator]
  map_add' := liftOperator_add E D
  map_mul' := liftOperator_mul E D h

/-- The lifted action is faithful even when bulk reconstruction is incomplete. -/
theorem liftOperator_injective (h : E.comp D = LinearMap.id) :
    Function.Injective (liftOperator E D) := by
  intro A B hab
  ext b
  have hx := congrArg (fun f : Module.End R Bulk => E (f (D b))) hab
  simpa [liftOperator, encode_decode E D h] using hx

/-- Lifting after compression keeps exactly the `P X P` corner. -/
theorem lift_compressed_operator (X : Module.End R Bulk) :
    liftOperator E D (E.comp (X.comp D)) = (D.comp E) * X * (D.comp E) := by
  ext x
  rfl

/-- The image of the operator lift is precisely the noncommutative `P X P` corner. -/
theorem range_liftOperator_iff_corner (h : E.comp D = LinearMap.id)
    (X : Module.End R Bulk) :
    X ∈ Set.range (liftOperator E D) ↔ (D.comp E) * X * (D.comp E) = X := by
  constructor
  · rintro ⟨A, rfl⟩
    ext x
    change D (E (D (A (E (D (E x)))))) = D (A (E x))
    rw [encode_decode E D h, encode_decode E D h]
  · intro hcorner
    exact ⟨E.comp (X.comp D), (lift_compressed_operator E D X).trans hcorner⟩

/-- The commutator survives faithful lifting with its original order. -/
theorem liftOperator_commutator (h : E.comp D = LinearMap.id)
    (A B : Module.End R Boundary) :
    liftOperator E D (A * B - B * A) =
      liftOperator E D A * liftOperator E D B -
        liftOperator E D B * liftOperator E D A := by
  rw [← liftOperator_mul E D h, ← liftOperator_mul E D h]
  ext x
  simp [liftOperator]

theorem lifted_commute_iff (h : E.comp D = LinearMap.id)
    (A B : Module.End R Boundary) :
    Commute (liftOperator E D A) (liftOperator E D B) ↔ Commute A B := by
  simp only [commute_iff_eq, ← liftOperator_mul E D h]
  exact (liftOperator_injective E D h).eq_iff

end Modules

section Capacity

variable {K Bulk Boundary : Type*} [DivisionRing K]
variable [AddCommGroup Bulk] [Module K Bulk]
variable [AddCommGroup Boundary] [Module K Boundary]

/-- Exact reconstruction cannot reduce finite linear information capacity. -/
theorem full_reconstruction_finrank_le [FiniteDimensional K Boundary]
    (E : Bulk →ₗ[K] Boundary) (D : Boundary →ₗ[K] Bulk)
    (hfull : D.comp E = LinearMap.id) :
    Module.finrank K Bulk ≤ Module.finrank K Boundary := by
  apply LinearMap.finrank_le_finrank_of_injective
  exact (show Function.LeftInverse D E from fun x => LinearMap.congr_fun hfull x).injective

/-- All missing finite-dimensional information is accounted for by the kernel. -/
theorem boundary_finrank_add_hidden [FiniteDimensional K Bulk]
    (E : Bulk →ₗ[K] Boundary) (D : Boundary →ₗ[K] Bulk)
    (h : E.comp D = LinearMap.id) :
    Module.finrank K Boundary + Module.finrank K (LinearMap.ker E) =
      Module.finrank K Bulk := by
  have hr : LinearMap.range E = ⊤ := LinearMap.range_eq_top.mpr (encode_surjective E D h)
  have hn := E.finrank_range_add_finrank_ker
  rw [hr, finrank_top] at hn
  exact hn

end Capacity

/-- The corresponding capacity bound needs no linear structure for finite sets. -/
theorem full_reconstruction_card_le {Bulk Boundary : Type*} [Fintype Bulk] [Fintype Boundary]
    (E : Bulk → Boundary) (D : Boundary → Bulk) (h : Function.LeftInverse D E) :
    Fintype.card Bulk ≤ Fintype.card Boundary :=
  Fintype.card_le_of_injective E h.injective

end InfoGeometry.Holographic.BoundaryReconstruction
