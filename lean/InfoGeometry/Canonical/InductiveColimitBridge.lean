import Mathlib.Tactic
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Canonical.CategoryTheoryConeUniqueness

/-!
# Inductive Colimit Bridge

This module is the theorem-safe elevator from finite `n`-dependent statements to
an explicit inductive-colimit interface.

The key discipline is that a theorem depending on a fixed finite stage is only a
stage theorem.  To state a limit theorem, one must supply:

* finite stages `Stage n`;
* transition morphisms `bond n : Stage n → Stage (n+1)`;
* a cone/readout `toLimit n : Stage n → Limit`;
* cone compatibility;
* compatibility of the finite property with the transition morphisms; and
* a readout/preservation rule into the limit property.

This file deliberately does not assert analytic C*-completion, a concrete
Kuzmin theorem, configuration-space stability, or Penrose tiling K-theory.
Those are supplied by specialized owner modules as explicit premises and then
read through this generic colimit interface.
-/

namespace InfoGeometry.Canonical.InductiveColimitBridge

universe u v

/-- A concrete sequential directed system with a cocone into a proposed limit. -/
structure SequentialColimitSystem where
  Stage : ℕ → Type u
  Limit : Type v
  bond : ∀ n : ℕ, Stage n → Stage (n + 1)
  toLimit : ∀ n : ℕ, Stage n → Limit
  cone_comm : ∀ (n : ℕ) (x : Stage n), toLimit (n + 1) (bond n x) = toLimit n x

namespace SequentialColimitSystem

variable (S : SequentialColimitSystem)

/-- Iterated transition map from stage `n` to stage `n+m`. -/
def bondSeq (n : ℕ) : ∀ m : ℕ, S.Stage n → S.Stage (n + m)
  | 0 => id
  | m + 1 => S.bond (n + m) ∘ bondSeq n m

@[simp] theorem bondSeq_zero (n : ℕ) (x : S.Stage n) :
    S.bondSeq n 0 x = x := rfl

@[simp] theorem bondSeq_succ (n m : ℕ) (x : S.Stage n) :
    S.bondSeq n (m + 1) x = S.bond (n + m) (S.bondSeq n m x) := rfl

/-- The cocone readout is invariant under any finite number of bonding steps. -/
theorem toLimit_bondSeq (n m : ℕ) (x : S.Stage n) :
    S.toLimit (n + m) (S.bondSeq n m x) = S.toLimit n x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      calc
        S.toLimit (n + (m + 1)) (S.bondSeq n (m + 1) x)
            = S.toLimit (n + m) (S.bondSeq n m x) := by
                simpa [Nat.add_assoc] using S.cone_comm (n + m) (S.bondSeq n m x)
        _ = S.toLimit n x := ih

/-- A finite-stage property compatible with the transition maps. -/
def CompatibleProperty (P : ∀ n : ℕ, S.Stage n → Prop) : Prop :=
  ∀ (n : ℕ) (x : S.Stage n), P n x → P (n + 1) (S.bond n x)

/-- Compatibility iterated along the tower. -/
theorem compatibleProperty_bondSeq
    (P : ∀ n : ℕ, S.Stage n → Prop) (hP : S.CompatibleProperty P)
    (n m : ℕ) (x : S.Stage n) (hx : P n x) :
    P (n + m) (S.bondSeq n m x) := by
  induction m with
  | zero => exact hx
  | succ m ih =>
      simpa [Nat.add_assoc] using hP (n + m) (S.bondSeq n m x) ih

/--
A limit property readout for a stage property.  This is the proof-level map
from the finite theorem family into the colimit statement.
-/
def LimitReadout (P : ∀ n : ℕ, S.Stage n → Prop) (Pinf : S.Limit → Prop) : Prop :=
  ∀ (n : ℕ) (x : S.Stage n), P n x → Pinf (S.toLimit n x)

/-- A compatible finite theorem gives a theorem about its image in the colimit. -/
theorem stage_property_to_limit
    (P : ∀ n : ℕ, S.Stage n → Prop) (Pinf : S.Limit → Prop)
    (hread : S.LimitReadout P Pinf)
    (n : ℕ) (x : S.Stage n) (hx : P n x) :
    Pinf (S.toLimit n x) :=
  hread n x hx

/--
A compatible finite theorem remains valid after any finite number of transitions
and then maps to the same colimit element.
-/
theorem transported_stage_property_to_same_limit
    (P : ∀ n : ℕ, S.Stage n → Prop) (Pinf : S.Limit → Prop)
    (hP : S.CompatibleProperty P) (hread : S.LimitReadout P Pinf)
    (n m : ℕ) (x : S.Stage n) (hx : P n x) :
    Pinf (S.toLimit (n + m) (S.bondSeq n m x)) :=
  hread (n + m) (S.bondSeq n m x)
    (S.compatibleProperty_bondSeq P hP n m x hx)

/-- The transported proof concerns the same colimit point as the original proof. -/
theorem transported_limit_point_eq
    (n m : ℕ) (x : S.Stage n) :
    S.toLimit (n + m) (S.bondSeq n m x) = S.toLimit n x :=
  S.toLimit_bondSeq n m x

end SequentialColimitSystem

/-! ## Proof families and theorem colimits -/

/--
A proof family over a sequential directed system: every finite stage has a
property, and the property is preserved by the bonding maps.
-/
abbrev CompatibleProofFamily (S : SequentialColimitSystem) :=
  { P : (∀ n : ℕ, S.Stage n → Prop) // S.CompatibleProperty P }

namespace CompatibleProofFamily

variable {S : SequentialColimitSystem} (F : CompatibleProofFamily S)

/-- The proof family transports along any finite number of bonding maps. -/
theorem transport (n m : ℕ) (x : S.Stage n) (hx : F.1 n x) :
    F.1 (n + m) (S.bondSeq n m x) :=
  S.compatibleProperty_bondSeq F.1 F.2 n m x hx

/-- Read a compatible proof family into a limit predicate. -/
theorem to_limit {Pinf : S.Limit → Prop}
    (hread : S.LimitReadout F.1 Pinf)
    (n : ℕ) (x : S.Stage n) (hx : F.1 n x) :
    Pinf (S.toLimit n x) :=
  hread n x hx

end CompatibleProofFamily

/-! ## Kuzmin/Cuntz--Toeplitz-style abstract interface -/

/--
Abstract interface for a finite-stage isomorphism theorem that must be transported
to an infinite-generator colimit.  `LeftStage` may model the `q`-CCR side and
`RightStage` the Cuntz--Toeplitz side; this file requires only transition maps
and compatible finite equivalences.
-/
structure CompatibleFiniteEquivalenceTower where
  Left : SequentialColimitSystem
  Right : SequentialColimitSystem
  equivAt : ∀ n : ℕ, Left.Stage n → Right.Stage n → Prop
  equiv_compat : ∀ (n : ℕ) (x : Left.Stage n) (y : Right.Stage n),
    equivAt n x y → equivAt (n + 1) (Left.bond n x) (Right.bond n y)
  limitEquiv : Left.Limit → Right.Limit → Prop
  limit_readout : ∀ (n : ℕ) (x : Left.Stage n) (y : Right.Stage n),
    equivAt n x y → limitEquiv (Left.toLimit n x) (Right.toLimit n y)

namespace CompatibleFiniteEquivalenceTower

variable (T : CompatibleFiniteEquivalenceTower)

/-- A finite compatible equivalence transports to any later finite stage. -/
theorem finite_equiv_transports
    (n m : ℕ) (x : T.Left.Stage n) (y : T.Right.Stage n)
    (hxy : T.equivAt n x y) :
    T.equivAt (n + m) (T.Left.bondSeq n m x) (T.Right.bondSeq n m y) := by
  induction m with
  | zero => exact hxy
  | succ m ih =>
      simpa [Nat.add_assoc] using
        T.equiv_compat (n + m) (T.Left.bondSeq n m x) (T.Right.bondSeq n m y) ih

/-- A finite compatible equivalence has an infinite-colimit readout. -/
theorem finite_equiv_to_colimit
    (n : ℕ) (x : T.Left.Stage n) (y : T.Right.Stage n)
    (hxy : T.equivAt n x y) :
    T.limitEquiv (T.Left.toLimit n x) (T.Right.toLimit n y) :=
  T.limit_readout n x y hxy

/-- Transporting the finite equivalence first gives the same colimit pair. -/
theorem transported_equiv_to_same_colimit
    (n m : ℕ) (x : T.Left.Stage n) (y : T.Right.Stage n)
    (hxy : T.equivAt n x y) :
    T.limitEquiv
      (T.Left.toLimit (n + m) (T.Left.bondSeq n m x))
      (T.Right.toLimit (n + m) (T.Right.bondSeq n m y)) :=
  T.limit_readout (n + m) (T.Left.bondSeq n m x) (T.Right.bondSeq n m y)
    (T.finite_equiv_transports n m x y hxy)

end CompatibleFiniteEquivalenceTower

end InfoGeometry.Canonical.InductiveColimitBridge
