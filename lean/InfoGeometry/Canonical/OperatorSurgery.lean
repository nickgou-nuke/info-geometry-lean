import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry/Canonical/OperatorSurgery.lean

Schur-Drazin algebraic surgery interface.

This file provides genuine Drazin surgery properties. It proves that once a Drazin
inverse candidate is supplied with its algebraic laws, the core/nil projectors
are constructively obtained.
-/

namespace InfoGeometry.Canonical.OperatorSurgery

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

local notation "EndV" => V →ₗ[ℝ] V

/--
Drazin inverse property.

`A` is the singular operator and `D` is the Drazin inverse candidate.
-/
@[rep_depth operator]
abbrev IsDrazinInverse (A D : EndV) : Prop :=
  D * A * D = D ∧ A * D = D * A ∧
    ∃ k : ℕ, A ^ (k + 1) * D = A ^ k

/--
Proof-carrying Drazin-style projector split data.

`projector_core` represents the regular/core sector and `projector_nil`
represents the complementary nil/radical sector.
-/
@[rep_depth operator]
structure DrazinSurgeryData (A : EndV) where
  projector_core : EndV
  projector_nil : EndV

/-- The core and nil projectors satisfy the expected algebraic relations. -/
@[rep_depth operator]
abbrev IsDrazinSurgery (A : EndV) (S : DrazinSurgeryData A) : Prop :=
  S.projector_core * S.projector_core = S.projector_core ∧
    S.projector_nil * S.projector_nil = S.projector_nil ∧
    S.projector_core * S.projector_nil = 0 ∧
    S.projector_core + S.projector_nil = LinearMap.id ∧
    S.projector_core * A = A * S.projector_core ∧
    ∃ k : ℕ, A ^ k * S.projector_nil = 0

namespace DrazinSurgeryData

/-- The core projector is idempotent. -/
@[simp]
theorem core_idempotent {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) :
    W.projector_core * W.projector_core = W.projector_core :=
  hW.1

/-- The nil projector is idempotent. -/
@[simp]
theorem nil_idempotent {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) :
    W.projector_nil * W.projector_nil = W.projector_nil :=
  hW.2.1

/-- The stored core/nil projectors are disjoint in the declared order. -/
@[simp]
theorem core_nil_disjoint {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) :
    W.projector_core * W.projector_nil = 0 :=
  hW.2.2.1

/-- The core and nil projectors partition the identity. -/
theorem core_add_nil {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) :
    W.projector_core + W.projector_nil = LinearMap.id :=
  hW.2.2.2.1

/-- The core projector commutes with the operator under surgery. -/
theorem core_commutes_with_A {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) :
    W.projector_core * A = A * W.projector_core :=
  hW.2.2.2.2.1

/-- The nil/radical projector is annihilated by some power of `A`. -/
theorem nil_power_annihilates {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) :
    ∃ k : ℕ, A ^ k * W.projector_nil = 0 :=
  hW.2.2.2.2.2

/-- Pointwise form of nil-power annihilation. -/
theorem nil_power_annihilates_apply {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) :
    ∃ k : ℕ, ∀ v : V, (A ^ k) (W.projector_nil v) = 0 := by
  rcases hW.2.2.2.2.2 with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro v
  change (A ^ k * W.projector_nil) v = (0 : EndV) v
  exact congrArg (fun f : EndV => f v) hk

/-- Pointwise form of `projector_core * projector_nil = 0`. -/
theorem core_nil_apply_eq_zero {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) (v : V) :
    W.projector_core (W.projector_nil v) = 0 := by
  change (W.projector_core * W.projector_nil) v = (0 : EndV) v
  exact congrArg (fun f : EndV => f v) hW.2.2.1

/-- Pointwise form of `projector_core + projector_nil = id`. -/
theorem core_add_nil_apply {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) (v : V) :
      W.projector_core v + W.projector_nil v = v := by
  have hpart := congrArg (fun f : EndV => f v) hW.2.2.2.1
  simpa only [LinearMap.add_apply, LinearMap.id_coe, id_eq] using hpart

/--
The nil projector annihilates the core projector on the other side.

This is derived, not stored.
-/
@[simp]
theorem nil_core_disjoint {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) :
    W.projector_nil * W.projector_core = 0 := by
  ext v
  have hpart := congrArg (fun f : EndV => f (W.projector_core v)) hW.2.2.2.1
  have hcore := congrArg (fun f : EndV => f v) hW.1
  have hpart' :
      W.projector_core (W.projector_core v) + W.projector_nil (W.projector_core v) = W.projector_core v := by
    simpa only [LinearMap.add_apply, LinearMap.id_coe, id_eq] using hpart
  have hcore' : W.projector_core (W.projector_core v) = W.projector_core v := by
    change (W.projector_core * W.projector_core) v = W.projector_core v
    exact hcore
  have hcancel : W.projector_core v + W.projector_nil (W.projector_core v) = W.projector_core v + 0 := by
    simpa [hcore'] using hpart'
  exact add_left_cancel hcancel

/-- Pointwise form of `projector_nil * projector_core = 0`. -/
theorem nil_core_apply_eq_zero {A : EndV} {W : DrazinSurgeryData A} (hW : IsDrazinSurgery A W) (v : V) :
    W.projector_nil (W.projector_core v) = 0 := by
  have hpart := congrArg (fun f : EndV => f (W.projector_core v)) hW.2.2.2.1
  have hcore := congrArg (fun f : EndV => f v) hW.1
  have hpart' :
      W.projector_core (W.projector_core v) + W.projector_nil (W.projector_core v) = W.projector_core v := by
    simpa only [LinearMap.add_apply, LinearMap.id_coe, id_eq] using hpart
  have hcore' : W.projector_core (W.projector_core v) = W.projector_core v := by
    change (W.projector_core * W.projector_core) v = W.projector_core v
    exact hcore
  have hcancel : W.projector_core v + W.projector_nil (W.projector_core v) = W.projector_core v + 0 := by
    simpa [hcore'] using hpart'
  exact add_left_cancel hcancel

/--
Construct the Drazin surgery projectors from a supplied Drazin inverse witness.

Core projector: `P = A * D`.

Nil/radical projector: `N = 1 - P`.

The Drazin power law certifies that the nil projector is killed by a power of
`A`, namely `A^k * N = 0`.
-/
@[rep_depth operator]
def ofDrazinInverse {A D : EndV}
    (_hD : IsDrazinInverse A D) :
    DrazinSurgeryData A where
  projector_core := A * D
  projector_nil := 1 - A * D

/--
The projectors constructed from a Drazin inverse satisfy the Drazin surgery properties.
-/
@[rep_depth operator]
theorem isDrazinSurgery_ofDrazinInverse {A D : EndV}
    (hD : IsDrazinInverse A D) :
    IsDrazinSurgery A (ofDrazinInverse hD) := by
  let P : EndV := A * D
  have hP : P * P = P := by
    dsimp [P]
    calc
      (A * D) * (A * D)
          = A * (D * A * D) := by rw [mul_assoc, ← mul_assoc D A D]
      _ = A * D := by rw [hD.1]

  have hNilPower : ∃ k : ℕ, A ^ k * (1 - P) = 0 := by
    rcases hD.2.2 with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    dsimp [P]
    have hPowSucc : A ^ k * A = A ^ (k + 1) := by rw [pow_succ]
    calc
      A ^ k * (1 - A * D)
          = A ^ k * 1 - A ^ k * (A * D) := by rw [mul_sub]
      _ = A ^ k - (A ^ k * A) * D := by rw [mul_one, ← mul_assoc]
      _ = A ^ k - A ^ (k + 1) * D := by rw [hPowSucc]
      _ = A ^ k - A ^ k := by rw [hk]
      _ = 0 := by simp

  refine ⟨hP, ?_, ?_, ?_, ?_, hNilPower⟩

  · calc
      (1 - P) * (1 - P)
          = 1 * (1 - P) - P * (1 - P) := by rw [sub_mul]
      _ = (1 - P) - (P * 1 - P * P) := by rw [one_mul, mul_sub]
      _ = (1 - P) - (P - P * P) := by rw [mul_one]
      _ = (1 - P) - (P - P) := by rw [hP]
      _ = 1 - P := by simp

  · calc
      P * (1 - P)
          = P * 1 - P * P := by rw [mul_sub]
      _ = P - P := by rw [mul_one, hP]
      _ = 0 := by simp

  · change P + (1 - P) = (1 : EndV)
    rw [add_comm, sub_add_cancel]

  · calc
      (A * D) * A
          = A * (D * A) := by rw [mul_assoc]
      _ = A * (A * D) := by rw [← hD.2.1]

/--
The trivial identity/zero projector split.

This is a constructive inhabitant of the projector-law interface for every
linear operator. It is not a Drazin radical decomposition and should not be
used as an existence theorem for nontrivial Drazin surgery.
-/
@[rep_depth operator]
def identitySplit (A : EndV) : DrazinSurgeryData A where
  projector_core := LinearMap.id
  projector_nil := 0

@[rep_depth operator]
theorem isDrazinSurgery_identitySplit (A : EndV) : IsDrazinSurgery A (identitySplit A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change LinearMap.id * LinearMap.id = LinearMap.id
    exact mul_one LinearMap.id
  · change 0 * 0 = (0 : EndV)
    exact mul_zero 0
  · change LinearMap.id * 0 = (0 : EndV)
    exact mul_zero LinearMap.id
  · change LinearMap.id + 0 = LinearMap.id
    exact add_zero LinearMap.id
  · change LinearMap.id * A = A * LinearMap.id
    exact (one_mul A).trans (mul_one A).symm
  · exact ⟨0, by change A ^ 0 * 0 = (0 : EndV); exact mul_zero _⟩

@[simp]
theorem identitySplit_projector_core (A : EndV) :
    (identitySplit A).projector_core = LinearMap.id :=
  rfl

@[simp]
theorem identitySplit_projector_nil (A : EndV) :
    (identitySplit A).projector_nil = 0 :=
  rfl

/--
Constructive inhabitance of the projector-law interface.

This theorem is intentionally named as an identity split, not as Drazin
existence.
-/
theorem exists_identitySplit (A : EndV) :
    ∃ W : DrazinSurgeryData A,
      W.projector_core = LinearMap.id ∧ W.projector_nil = 0 :=
  ⟨identitySplit A, rfl, rfl⟩

end DrazinSurgeryData

/--
Constructive Schur-Drazin algebraic surgery.

This is the correct replacement for an unconditional finite-dimensional
existence theorem.
-/
@[rep_depth operator]
def drazinSurgeryOfDrazinInverse
    {A D : EndV} (hD : IsDrazinInverse A D) :
    DrazinSurgeryData A :=
  DrazinSurgeryData.ofDrazinInverse hD

theorem isDrazinSurgery_drazinSurgeryOfDrazinInverse
    {A D : EndV} (hD : IsDrazinInverse A D) :
    IsDrazinSurgery A (drazinSurgeryOfDrazinInverse hD) :=
  DrazinSurgeryData.isDrazinSurgery_ofDrazinInverse hD

/-! ## Generic noncommutative ring consequences -/

/-- An index-one Drazin outer-inverse law makes `A * D` idempotent. -/
theorem drazin_indexOne_projector_idempotent_ring
    {R : Type*} [Ring R]
    {A D : R}
    (hDAD : D * A * D = D) :
    (A * D) * (A * D) = A * D := by
  calc
    (A * D) * (A * D) = A * (D * A * D) := by noncomm_ring
    _ = A * D := by rw [hDAD]

/-- The source operator annihilates the right defect under the index-one
inverse and commutation laws. -/
theorem drazin_indexOne_annihilates_right_defect_ring
    {R : Type*} [Ring R]
    {A D : R}
    (hADA : A * D * A = A)
    (hcomm : A * D = D * A) :
    A * (1 - A * D) = 0 := by
  have hAeq : A = A * (A * D) := by
    calc
      A = A * D * A := by symm; exact hADA
      _ = A * (D * A) := by rw [mul_assoc]
      _ = A * (A * D) := by rw [hcomm]
  calc
    A * (1 - A * D) = A * 1 - A * (A * D) := by rw [mul_sub]
    _ = A - A * (A * D) := by rw [mul_one]
    _ = 0 := sub_eq_zero.mpr hAeq

/-- The source operator annihilates the left defect under the index-one
inverse law. -/
theorem drazin_indexOne_annihilates_left_defect_ring
    {R : Type*} [Ring R]
    {A D : R}
    (hADA : A * D * A = A) :
    (1 - A * D) * A = 0 := by
  calc
    (1 - A * D) * A = 1 * A - (A * D) * A := by rw [sub_mul]
    _ = A - (A * D) * A := by rw [one_mul]
    _ = A - A := by rw [hADA]
    _ = 0 := by simp

end InfoGeometry.Canonical.OperatorSurgery
