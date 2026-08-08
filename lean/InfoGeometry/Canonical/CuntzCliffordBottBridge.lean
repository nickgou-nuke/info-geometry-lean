import InfoGeometry.Canonical.CuntzMapKreinBridge
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Cuntz Clock to the Split Clifford Bott Tower

This file formalizes the finite algebraic part of the synthesis

`Cuntz clock -> Cl(1,1) tensor tower -> algebraic direct limit`.

It does not assert an isomorphism between `O_2` and an infinite Clifford
completion, nor does it prove Cuntz's K-theory theorem `K_0(O_2)=K_1(O_2)=0`.
Those are genuine external closure debt unless represented by owner theorems.

#### BUCKET 1: CLOSED FINITE THEOREMS
If a Cuntz-clock iterate is encoded in the split `Cl(1,1)` stage tower and the
encoding commutes with the Bott bonding maps, then its image is constant in the
algebraic direct limit. Square-zero, idempotent, and involutive relations at
stage zero are preserved in that limit.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
All bridge theorems depend on the explicit stage-compatibility property
`hcompat`.

#### BUCKET 3: OPEN CLOSURE DEBT
The analytic infinite tensor-product completion, `O_2`/CAR identification, and
the vanishing of `K_*(O_2)`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.CuntzCliffordBottBridge

open InfoGeometry.Canonical.CuntzMapKreinBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

variable {Op : Type*} [Ring Op] [StarRing Op]

abbrev Stage (n : ℕ) : Type :=
  InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n

/--
Stage sequence obtained by iterating a witnessed Cuntz clock and encoding the
`n`th iterate into the `n`th split `Cl(1,1)` Bott stage.
-/
def clockStageSequence
    (M : DiscreteCuntzModularStep Op)
    (encode : ∀ n : ℕ, Op → Stage n)
    (seed : Op) :
    ∀ n : ℕ, Stage n :=
  fun n => encode n (Nat.iterate M.sigma n seed)

/-- Readback at stage zero. -/
@[simp]
theorem clockStageSequence_zero
    (M : DiscreteCuntzModularStep Op)
    (encode : ∀ n : ℕ, Op → Stage n)
    (seed : Op) :
    clockStageSequence M encode seed 0 = encode 0 seed := by
  rfl

/--
The Cuntz-clock stage sequence is compatible with the Bott bonding maps when
the supplied encoder commutes with one clock tick.
-/
theorem clockStageSequence_succ
    (M : DiscreteCuntzModularStep Op)
    (encode : ∀ n : ℕ, Op → Stage n)
    (seed : Op)
    (hcompat : ∀ n : ℕ,
      stageEmbed n (encode n (Nat.iterate M.sigma n seed)) =
        encode (n + 1) (Nat.iterate M.sigma (n + 1) seed))
    (n : ℕ) :
    stageEmbed n (clockStageSequence M encode seed n) =
      clockStageSequence M encode seed (n + 1) := by
  exact hcompat n

/-! ## Direct-limit consequences -/

/--
A Cuntz-clocked `Cl(1,1)` stage family has constant image in the algebraic
Bott direct limit when the encoder commutes with the bonding maps.
-/
theorem cuntz_clock_constant_in_cl11_limit
    (M : DiscreteCuntzModularStep Op)
    (encode : ∀ n : ℕ, Op → Stage n)
    (seed : Op)
    (hcompat : ∀ n : ℕ,
      stageEmbed n (encode n (Nat.iterate M.sigma n seed)) =
        encode (n + 1) (Nat.iterate M.sigma (n + 1) seed)) :
    ∀ n : ℕ,
      ofStage n (encode n (Nat.iterate M.sigma n seed)) =
        ofStage 0 (encode 0 seed) := by
  exact finite_sequence_constant_in_limit
    (F := clockStageSequence M encode seed)
    (hF := clockStageSequence_succ M encode seed hcompat)

/-- Square-zero stage-zero data remain square-zero along the Cuntz-clock limit. -/
theorem cuntz_clock_square_zero_in_cl11_limit
    (M : DiscreteCuntzModularStep Op)
    (encode : ∀ n : ℕ, Op → Stage n)
    (seed : Op)
    (hcompat : ∀ n : ℕ,
      stageEmbed n (encode n (Nat.iterate M.sigma n seed)) =
        encode (n + 1) (Nat.iterate M.sigma (n + 1) seed))
    (h0 : encode 0 seed * encode 0 seed = 0) :
    ∀ n : ℕ,
      ofStage n (encode n (Nat.iterate M.sigma n seed)) *
          ofStage n (encode n (Nat.iterate M.sigma n seed)) = 0 := by
  exact finite_sequence_square_zero_in_limit
    (F := clockStageSequence M encode seed)
    (hF := clockStageSequence_succ M encode seed hcompat)
    (h0 := h0)

/-- Idempotent stage-zero data remain idempotent along the Cuntz-clock limit. -/
theorem cuntz_clock_idempotent_in_cl11_limit
    (M : DiscreteCuntzModularStep Op)
    (encode : ∀ n : ℕ, Op → Stage n)
    (seed : Op)
    (hcompat : ∀ n : ℕ,
      stageEmbed n (encode n (Nat.iterate M.sigma n seed)) =
        encode (n + 1) (Nat.iterate M.sigma (n + 1) seed))
    (h0 : encode 0 seed * encode 0 seed = encode 0 seed) :
    ∀ n : ℕ,
      ofStage n (encode n (Nat.iterate M.sigma n seed)) *
          ofStage n (encode n (Nat.iterate M.sigma n seed)) =
        ofStage n (encode n (Nat.iterate M.sigma n seed)) := by
  exact finite_sequence_idempotent_in_limit
    (F := clockStageSequence M encode seed)
    (hF := clockStageSequence_succ M encode seed hcompat)
    (h0 := h0)

/-- Involutive stage-zero data remain involutive along the Cuntz-clock limit. -/
theorem cuntz_clock_involution_in_cl11_limit
    (M : DiscreteCuntzModularStep Op)
    (encode : ∀ n : ℕ, Op → Stage n)
    (seed : Op)
    (hcompat : ∀ n : ℕ,
      stageEmbed n (encode n (Nat.iterate M.sigma n seed)) =
        encode (n + 1) (Nat.iterate M.sigma (n + 1) seed))
    (h0 : encode 0 seed * encode 0 seed = 1) :
    ∀ n : ℕ,
      ofStage n (encode n (Nat.iterate M.sigma n seed)) *
          ofStage n (encode n (Nat.iterate M.sigma n seed)) = 1 := by
  exact finite_sequence_involution_in_limit
    (F := clockStageSequence M encode seed)
    (hF := clockStageSequence_succ M encode seed hcompat)
    (h0 := h0)

end InfoGeometry.Canonical.CuntzCliffordBottBridge
