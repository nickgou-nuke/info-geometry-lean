import InfoGeometry.Canonical.FinitePenrosePatchTower
import InfoGeometry.Canonical.InductiveColimitBridge

/-!
# Finite Penrose patch colimit bridge

This file connects the finite Penrose patch-tower lane to the repo's generic
sequential colimit interface.

BUCKET 1: CLOSED FINITE/COLIMIT BRIDGES
- a monotone patch tower gives a sequential colimit system on patch-local states;
- compatible local-state properties read out to any supplied limit predicate;
- compatible finite comparisons between patch-local states and another sequential
  system read out to the corresponding limit comparison.

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
- every limit statement here depends on explicit cone maps / readout maps and
  compatibility premises supplied by the caller.

BUCKET 3: OPEN CLOSURE DEBT
- this file does not construct a concrete Penrose AF algebra, a concrete colimit,
  or a twistor/K-theoretic classification theorem.
-/

namespace FinitePenrosePatchColimit

open InfoGeometry.Canonical.FinitePenrosePatchCategory
open InfoGeometry.Canonical.FinitePenrosePatchTower
open InfoGeometry.Canonical.InductiveColimitBridge

universe u v w

section Basic

variable {α : Type u} {𝕜 T D : Type u}
variable [PartialOrder α]
variable [CommRing 𝕜]
variable [AddCommGroup T] [Module 𝕜 T]
variable [AddCommGroup D] [Module 𝕜 D]

variable {S : InfoGeometry.Canonical.DiscretePenroseSpinNet.SpinNet α 𝕜 T D}

/--
A monotone finite patch tower determines a sequential directed system on its
patch-local states, once a compatible readout into a proposed limit is supplied.
-/
def localStateSequentialSystem
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x) :
    SequentialColimitSystem where
  Stage := fun n => localState (α := α) S (Twr.stage n)
  Limit := Limit
  bond := fun n => mapLocalState (α := α) S (PLift.up (Twr.bond n))
  toLimit := toLimit
  cone_comm := cone_comm

/-- A compatible local-state theorem at a finite patch stage reads out to the limit. -/
theorem localState_property_to_colimit
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (P : ∀ n : ℕ, localState (α := α) S (Twr.stage n) → Prop)
    (Pinf : Limit → Prop)
    (hread :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).LimitReadout P Pinf)
    (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (hx : P n x) :
    Pinf (toLimit n x) :=
  (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).stage_property_to_limit
    P Pinf hread n x hx

/--
A compatible local-state theorem may first be transported along the patch tower
before being read at the same limit point.
-/
theorem transported_localState_property_to_same_limit
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (P : ∀ n : ℕ, localState (α := α) S (Twr.stage n) → Prop)
    (Pinf : Limit → Prop)
    (hP :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).CompatibleProperty P)
    (hread :
      (localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).LimitReadout P Pinf)
    (n m : ℕ) (x : localState (α := α) S (Twr.stage n)) (hx : P n x) :
    Pinf
      (toLimit (n + m)
        ((localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).bondSeq n m x)) :=
  SequentialColimitSystem.transported_stage_property_to_same_limit
    (S := localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm)
    P Pinf hP hread n m x hx

/--
The transported local state and the original local state determine the same limit
point.
-/
theorem transported_localState_limit_eq
    (Twr : PatchTower S)
    (Limit : Type v)
    (toLimit : ∀ n, localState (α := α) S (Twr.stage n) → Limit)
    (cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        toLimit n x)
    (n m : ℕ) (x : localState (α := α) S (Twr.stage n)) :
    toLimit (n + m)
        ((localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm).bondSeq n m x) =
      toLimit n x :=
  SequentialColimitSystem.transported_limit_point_eq
    (S := localStateSequentialSystem (α := α) (S := S) Twr Limit toLimit cone_comm)
    n m x

/--
A finite comparison between patch-local states and another sequential system,
packaged in the generic `CompatibleFiniteEquivalenceTower` interface.
-/
def patchLocalStateComparisonTower
    (Twr : PatchTower S)
    (LeftLimit : Type v)
    (left_toLimit : ∀ n, localState (α := α) S (Twr.stage n) → LeftLimit)
    (left_cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      left_toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        left_toLimit n x)
    (RightStage : ℕ → Type w)
    (RightLimit : Type w)
    (right_bond : ∀ n, RightStage n → RightStage (n + 1))
    (right_toLimit : ∀ n, RightStage n → RightLimit)
    (right_cone_comm : ∀ (n : ℕ) (y : RightStage n),
      right_toLimit (n + 1) (right_bond n y) = right_toLimit n y)
    (equivAt : ∀ n, localState (α := α) S (Twr.stage n) → RightStage n → Prop)
    (equiv_compat : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y →
        equivAt (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) (right_bond n y))
    (limitEquiv : LeftLimit → RightLimit → Prop)
    (limit_readout : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y → limitEquiv (left_toLimit n x) (right_toLimit n y)) :
    CompatibleFiniteEquivalenceTower where
  Left := localStateSequentialSystem (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
  Right :=
    { Stage := RightStage
      Limit := RightLimit
      bond := right_bond
      toLimit := right_toLimit
      cone_comm := right_cone_comm }
  equivAt := equivAt
  equiv_compat := equiv_compat
  limitEquiv := limitEquiv
  limit_readout := limit_readout

/-- A finite patch-local comparison has the supplied limit readout. -/
theorem patchLocalState_equiv_to_colimit
    (Twr : PatchTower S)
    (LeftLimit : Type v)
    (left_toLimit : ∀ n, localState (α := α) S (Twr.stage n) → LeftLimit)
    (left_cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      left_toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        left_toLimit n x)
    (RightStage : ℕ → Type w)
    (RightLimit : Type w)
    (right_bond : ∀ n, RightStage n → RightStage (n + 1))
    (right_toLimit : ∀ n, RightStage n → RightLimit)
    (right_cone_comm : ∀ (n : ℕ) (y : RightStage n),
      right_toLimit (n + 1) (right_bond n y) = right_toLimit n y)
    (equivAt : ∀ n, localState (α := α) S (Twr.stage n) → RightStage n → Prop)
    (equiv_compat : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y →
        equivAt (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) (right_bond n y))
    (limitEquiv : LeftLimit → RightLimit → Prop)
    (limit_readout : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y → limitEquiv (left_toLimit n x) (right_toLimit n y))
    (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n)
    (hxy : equivAt n x y) :
    limitEquiv (left_toLimit n x) (right_toLimit n y) :=
  CompatibleFiniteEquivalenceTower.finite_equiv_to_colimit
    (patchLocalStateComparisonTower (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
      RightStage RightLimit right_bond right_toLimit right_cone_comm
      equivAt equiv_compat limitEquiv limit_readout)
    n x y hxy

/--
A finite patch-local comparison remains valid after any finite number of tower
bonding steps before taking the limit readout.
-/
theorem transported_patchLocalState_equiv_to_colimit
    (Twr : PatchTower S)
    (LeftLimit : Type v)
    (left_toLimit : ∀ n, localState (α := α) S (Twr.stage n) → LeftLimit)
    (left_cone_comm : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)),
      left_toLimit (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) =
        left_toLimit n x)
    (RightStage : ℕ → Type w)
    (RightLimit : Type w)
    (right_bond : ∀ n, RightStage n → RightStage (n + 1))
    (right_toLimit : ∀ n, RightStage n → RightLimit)
    (right_cone_comm : ∀ (n : ℕ) (y : RightStage n),
      right_toLimit (n + 1) (right_bond n y) = right_toLimit n y)
    (equivAt : ∀ n, localState (α := α) S (Twr.stage n) → RightStage n → Prop)
    (equiv_compat : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y →
        equivAt (n + 1) (mapLocalState (α := α) S (PLift.up (Twr.bond n)) x) (right_bond n y))
    (limitEquiv : LeftLimit → RightLimit → Prop)
    (limit_readout : ∀ (n : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n),
      equivAt n x y → limitEquiv (left_toLimit n x) (right_toLimit n y))
    (n m : ℕ) (x : localState (α := α) S (Twr.stage n)) (y : RightStage n)
    (hxy : equivAt n x y) :
    limitEquiv
      (left_toLimit (n + m)
        ((localStateSequentialSystem (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm).bondSeq n m x))
      (right_toLimit (n + m)
        ((patchLocalStateComparisonTower (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
          RightStage RightLimit right_bond right_toLimit right_cone_comm
          equivAt equiv_compat limitEquiv limit_readout).Right.bondSeq n m y)) :=
  CompatibleFiniteEquivalenceTower.transported_equiv_to_same_colimit
    (patchLocalStateComparisonTower (α := α) (S := S) Twr LeftLimit left_toLimit left_cone_comm
      RightStage RightLimit right_bond right_toLimit right_cone_comm
      equivAt equiv_compat limitEquiv limit_readout)
    n m x y hxy

end Basic

end FinitePenrosePatchColimit
