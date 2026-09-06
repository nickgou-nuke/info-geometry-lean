import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry/Canonical/OperatorSurgery.lean

Schur-Drazin algebraic surgery interface.

This file is witness-gated. It does not prove that every finite-dimensional
operator admits a Drazin decomposition. Instead, it proves that once a Drazin
inverse candidate is supplied with its algebraic laws, the core/nil projectors
are constructively obtained.
-/

namespace InfoGeometry.Canonical

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

local notation "EndV" => V →ₗ[ℝ] V

/--
Drazin inverse witness.

`A` is the singular operator and `D` is the Drazin inverse candidate.
-/
@[rep_depth operator]
structure DrazinInverseWitness (A D : EndV) : Prop where
  drazin_outer :
    D * A * D = D
  commute :
    A * D = D * A
  drazin_power :
    ∃ k : ℕ, A ^ (k + 1) * D = A ^ k

/--
Proof-carrying Drazin-style projector split.

`projector_core` represents the regular/core sector and `projector_nil`
represents the complementary nil/radical sector.
-/
@[rep_depth operator]
structure DrazinSurgeryWitness (A : EndV) where
  projector_core : EndV
  projector_nil : EndV
  is_idempotent_core :
    projector_core * projector_core = projector_core
  is_idempotent_nil :
    projector_nil * projector_nil = projector_nil
  is_disjoint :
    projector_core * projector_nil = 0
  is_partition :
    projector_core + projector_nil = LinearMap.id
  commutes_with_A :
    projector_core * A = A * projector_core
  nil_eventually_annihilated :
    ∃ k : ℕ, A ^ k * projector_nil = 0

namespace DrazinSurgeryWitness

variable {A : EndV}
variable (W : DrazinSurgeryWitness A)

/-- The core projector is idempotent. -/
@[simp]
theorem core_idempotent :
    DrazinSurgeryWitness.projector_core (V := V) W *
        DrazinSurgeryWitness.projector_core (V := V) W =
      DrazinSurgeryWitness.projector_core (V := V) W :=
  DrazinSurgeryWitness.is_idempotent_core (V := V) W

/-- The nil projector is idempotent. -/
@[simp]
theorem nil_idempotent :
    DrazinSurgeryWitness.projector_nil (V := V) W *
        DrazinSurgeryWitness.projector_nil (V := V) W =
      DrazinSurgeryWitness.projector_nil (V := V) W :=
  DrazinSurgeryWitness.is_idempotent_nil (V := V) W

/-- The stored core/nil projectors are disjoint in the declared order. -/
@[simp]
theorem core_nil_disjoint :
    DrazinSurgeryWitness.projector_core (V := V) W *
        DrazinSurgeryWitness.projector_nil (V := V) W = 0 :=
  DrazinSurgeryWitness.is_disjoint (V := V) W

/-- The core and nil projectors partition the identity. -/
theorem core_add_nil :
    DrazinSurgeryWitness.projector_core (V := V) W +
        DrazinSurgeryWitness.projector_nil (V := V) W =
      LinearMap.id :=
  DrazinSurgeryWitness.is_partition (V := V) W

/-- The core projector commutes with the operator under surgery. -/
theorem core_commutes_with_A :
    DrazinSurgeryWitness.projector_core (V := V) W * A =
      A * DrazinSurgeryWitness.projector_core (V := V) W :=
  DrazinSurgeryWitness.commutes_with_A (V := V) W

/-- The nil/radical projector is annihilated by some power of `A`. -/
theorem nil_power_annihilates {A : EndV} (W : DrazinSurgeryWitness A) :
    ∃ k : ℕ, A ^ k * DrazinSurgeryWitness.projector_nil (V := V) W = 0 :=
  @DrazinSurgeryWitness.nil_eventually_annihilated V _ _ A W

/-- Pointwise form of nil-power annihilation. -/
theorem nil_power_annihilates_apply {A : EndV} (W : DrazinSurgeryWitness A) :
    ∃ k : ℕ, ∀ v : V, (A ^ k) (DrazinSurgeryWitness.projector_nil (V := V) W v) = 0 := by
  rcases W.nil_eventually_annihilated with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro v
  change (A ^ k * DrazinSurgeryWitness.projector_nil (V := V) W) v = (0 : EndV) v
  exact congrArg (fun f : EndV => f v) hk

/-- Pointwise form of `projector_core * projector_nil = 0`. -/
theorem core_nil_apply_eq_zero (v : V) :
    DrazinSurgeryWitness.projector_core (V := V) W
        (DrazinSurgeryWitness.projector_nil (V := V) W v) = 0 := by
  change
    (DrazinSurgeryWitness.projector_core (V := V) W *
        DrazinSurgeryWitness.projector_nil (V := V) W) v = (0 : EndV) v
  exact congrArg (fun f : EndV => f v) (DrazinSurgeryWitness.is_disjoint (V := V) W)

/-- Pointwise form of `projector_core + projector_nil = id`. -/
theorem core_add_nil_apply (v : V) :
      DrazinSurgeryWitness.projector_core (V := V) W v +
        DrazinSurgeryWitness.projector_nil (V := V) W v =
      v := by
  simpa only [LinearMap.add_apply, LinearMap.id_coe, id_eq] using
    congrArg (fun f : EndV => f v) (DrazinSurgeryWitness.is_partition (V := V) W)

/--
The nil projector annihilates the core projector on the other side.

This is derived, not stored.
-/
@[simp]
theorem nil_core_disjoint :
    DrazinSurgeryWitness.projector_nil (V := V) W *
        DrazinSurgeryWitness.projector_core (V := V) W =
      0 := by
  ext v
  have hpart :=
    congrArg
      (fun f : EndV => f (DrazinSurgeryWitness.projector_core (V := V) W v))
      (DrazinSurgeryWitness.is_partition (V := V) W)
  have hcore :=
    congrArg
      (fun f : EndV => f v)
      (DrazinSurgeryWitness.is_idempotent_core (V := V) W)
  have hpart' :
      DrazinSurgeryWitness.projector_core (V := V) W
          (DrazinSurgeryWitness.projector_core (V := V) W v)
        + DrazinSurgeryWitness.projector_nil (V := V) W
          (DrazinSurgeryWitness.projector_core (V := V) W v)
        =
      DrazinSurgeryWitness.projector_core (V := V) W v := by
    simpa only [LinearMap.add_apply, LinearMap.id_coe, id_eq] using hpart
  have hcore' :
      DrazinSurgeryWitness.projector_core (V := V) W
          (DrazinSurgeryWitness.projector_core (V := V) W v) =
        DrazinSurgeryWitness.projector_core (V := V) W v := by
    change
      (DrazinSurgeryWitness.projector_core (V := V) W *
          DrazinSurgeryWitness.projector_core (V := V) W) v =
        DrazinSurgeryWitness.projector_core (V := V) W v
    exact hcore
  have hcancel :
      DrazinSurgeryWitness.projector_core (V := V) W v
        + DrazinSurgeryWitness.projector_nil (V := V) W
          (DrazinSurgeryWitness.projector_core (V := V) W v)
        =
      DrazinSurgeryWitness.projector_core (V := V) W v + 0 := by
    simpa [hcore'] using hpart'
  exact add_left_cancel hcancel

/-- Pointwise form of `projector_nil * projector_core = 0`. -/
theorem nil_core_apply_eq_zero (v : V) :
    DrazinSurgeryWitness.projector_nil (V := V) W
        (DrazinSurgeryWitness.projector_core (V := V) W v) = 0 := by
  have hpart :=
    congrArg
      (fun f : EndV => f (DrazinSurgeryWitness.projector_core (V := V) W v))
      (DrazinSurgeryWitness.is_partition (V := V) W)
  have hcore :=
    congrArg
      (fun f : EndV => f v)
      (DrazinSurgeryWitness.is_idempotent_core (V := V) W)
  have hpart' :
      DrazinSurgeryWitness.projector_core (V := V) W
          (DrazinSurgeryWitness.projector_core (V := V) W v)
        + DrazinSurgeryWitness.projector_nil (V := V) W
          (DrazinSurgeryWitness.projector_core (V := V) W v)
        =
      DrazinSurgeryWitness.projector_core (V := V) W v := by
    simpa only [LinearMap.add_apply, LinearMap.id_coe, id_eq] using hpart
  have hcore' :
      DrazinSurgeryWitness.projector_core (V := V) W
          (DrazinSurgeryWitness.projector_core (V := V) W v) =
        DrazinSurgeryWitness.projector_core (V := V) W v := by
    change
      (DrazinSurgeryWitness.projector_core (V := V) W *
          DrazinSurgeryWitness.projector_core (V := V) W) v =
        DrazinSurgeryWitness.projector_core (V := V) W v
    exact hcore
  have hcancel :
      DrazinSurgeryWitness.projector_core (V := V) W v
        + DrazinSurgeryWitness.projector_nil (V := V) W
          (DrazinSurgeryWitness.projector_core (V := V) W v)
        =
      DrazinSurgeryWitness.projector_core (V := V) W v + 0 := by
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
    (hD : DrazinInverseWitness A D) :
    DrazinSurgeryWitness A := by
  let P : EndV := A * D

  have hP : P * P = P := by
    dsimp [P]
    calc
      (A * D) * (A * D)
          = A * (D * A * D) := by
            rw [mul_assoc, ← mul_assoc D A D]
      _ = A * D := by
            rw [hD.drazin_outer]

  have hNilPower : ∃ k : ℕ, A ^ k * (1 - P) = 0 := by
    rcases hD.drazin_power with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    dsimp [P]
    have hPowSucc : A ^ k * A = A ^ (k + 1) := by
      rw [pow_succ]
    calc
      A ^ k * (1 - A * D)
          = A ^ k * 1 - A ^ k * (A * D) := by
            rw [mul_sub]
      _ = A ^ k - (A ^ k * A) * D := by
            rw [mul_one, ← mul_assoc]
      _ = A ^ k - A ^ (k + 1) * D := by
            rw [hPowSucc]
      _ = A ^ k - A ^ k := by
            rw [hk]
      _ = 0 := by
            simp

  refine
    { projector_core := P
      projector_nil := 1 - P
      is_idempotent_core := hP
      is_idempotent_nil := ?_
      is_disjoint := ?_
      is_partition := ?_
      commutes_with_A := ?_
      nil_eventually_annihilated := hNilPower }

  · calc
      (1 - P) * (1 - P)
          = 1 * (1 - P) - P * (1 - P) := by
            rw [sub_mul]
      _ = (1 - P) - (P * 1 - P * P) := by
            rw [one_mul, mul_sub]
      _ = (1 - P) - (P - P * P) := by
            rw [mul_one]
      _ = (1 - P) - (P - P) := by
            rw [hP]
      _ = 1 - P := by
            simp

  · calc
      P * (1 - P)
          = P * 1 - P * P := by
            rw [mul_sub]
      _ = P - P := by
            rw [mul_one, hP]
      _ = 0 := by
            simp

  · change P + (1 - P) = (1 : EndV)
    rw [add_comm, sub_add_cancel]

  · dsimp [P]
    calc
      (A * D) * A
          = A * (D * A) := by
            rw [mul_assoc]
      _ = A * (A * D) := by
            rw [← hD.commute]

/--
The trivial identity/zero projector split.

This is a constructive inhabitant of the projector-law interface for every
linear operator. It is not a Drazin radical decomposition and should not be
used as an existence theorem for nontrivial Drazin surgery.
-/
@[rep_depth operator]
def identitySplit (A : EndV) : DrazinSurgeryWitness A where
  projector_core := LinearMap.id
  projector_nil := 0
  is_idempotent_core := by
    ext v
    simp
  is_idempotent_nil := by
    ext v
    simp
  is_disjoint := by
    ext v
    simp
  is_partition := by
    ext v
    simp
  commutes_with_A := by
    ext v
    simp
  nil_eventually_annihilated := by
    refine ⟨0, ?_⟩
    ext v
    simp

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
    ∃ W : DrazinSurgeryWitness A,
      W.projector_core = LinearMap.id ∧ W.projector_nil = 0 :=
  ⟨identitySplit A, rfl, rfl⟩

end DrazinSurgeryWitness

/--
Constructive Schur-Drazin algebraic surgery.

This is the correct replacement for an unconditional finite-dimensional
existence theorem.
-/
@[rep_depth operator]
def drazinSurgeryOfDrazinInverse
    {A D : EndV} (hD : DrazinInverseWitness A D) :
    DrazinSurgeryWitness A :=
  DrazinSurgeryWitness.ofDrazinInverse hD

end InfoGeometry.Canonical
