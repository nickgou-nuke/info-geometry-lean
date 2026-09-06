import InfoGeometry.Canonical.CuntzCliffordBottBridge
import InfoGeometry.Canonical.CuntzMapKreinBridge
import InfoGeometry.Topology.FractalCantorFock

/-!
# Çelik--Koçak Split Fock Data as a Cuntz Clock

This file records the honest finite relation:

`creation / annihilation CAR data -> Cuntz clock branches -> Cl(1,1) Bott tower`.

It does not assert that a concrete Cuntz algebra is isomorphic to the analytic
infinite Clifford/Fock completion.  The Cuntz/Fock identification is exposed as
explicit compatibility, and the direct-limit consequences are inherited from the already
proved `CuntzCliffordBottBridge`.

#### BUCKET 1: CLOSED FINITE THEOREMS
The Cuntz branches read back to creation/annihilation under the supplied split
Fock clock, and the CAR/nilpotence laws transfer to those branches.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT COMPATIBILITY
The `Cl(1,1)` direct-limit statements require an encoder compatible with the
Cuntz clock and Bott bonding maps.

#### BUCKET 3: OPEN CLOSURE DEBT
The analytic infinite Fock completion, `O_2`/CAR isomorphism, K-theory
vanishing, and historical attribution beyond the existing interface citation.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakCuntzFockBridge

open InfoGeometry.Canonical.CuntzMapKreinBridge
open InfoGeometry.Canonical.CuntzCliffordBottBridge
open InfoGeometry.Topology.FractalCantorFock
open InfoGeometry.Clifford.Cl11TensorTowerLimit

variable {Op : Type*} [Ring Op] [StarRing Op]

theorem realCARPair_creation_annihilation_eq_one
    (C : RealCARPair Op) :
    C.creation * C.annihilation + C.annihilation * C.creation = 1 := by
  rw [add_comm]
  exact C.car

theorem realCARPair_creation_sq_zero
    (C : RealCARPair Op) :
    C.creation * C.creation = 0 :=
  C.nilpotent_creation

theorem realCARPair_annihilation_sq_zero
    (C : RealCARPair Op) :
    C.annihilation * C.annihilation = 0 :=
  C.nilpotent_annihilation

/--
Split Fock clock data: a real CAR pair whose creation/annihilation operators
are the left/right branches of a witnessed Cuntz modular step.
-/
def IsSplitFockCuntzClock
    {Op : Type*} [Ring Op] [StarRing Op]
    (car : RealCARPair Op)
    (clock : DiscreteCuntzModularStep Op) : Prop :=
  clock.S_left = car.creation ∧
    clock.S_right = car.annihilation

namespace SplitFockCuntzClock

variable (car : RealCARPair Op)
variable (clock : DiscreteCuntzModularStep Op)

/-- The left Cuntz branch is the split-Fock creation operator. -/
@[rep_depth operator]
theorem left_branch_eq_creation
    (h : IsSplitFockCuntzClock car clock) :
    clock.S_left = car.creation :=
  h.1

/-- The right Cuntz branch is the split-Fock annihilation operator. -/
@[rep_depth operator]
theorem right_branch_eq_annihilation
    (h : IsSplitFockCuntzClock car clock) :
    clock.S_right = car.annihilation :=
  h.2

/-- The left Cuntz/Fock branch is nilpotent under the supplied CAR data. -/
@[rep_depth operator]
theorem left_branch_sq_zero
    (h : IsSplitFockCuntzClock car clock) :
    clock.S_left * clock.S_left = 0 := by
  rw [h.1]
  exact car.creation_sq_zero

/-- The right Cuntz/Fock branch is nilpotent under the supplied CAR data. -/
@[rep_depth operator]
theorem right_branch_sq_zero
    (h : IsSplitFockCuntzClock car clock) :
    clock.S_right * clock.S_right = 0 := by
  rw [h.2]
  exact car.annihilation_sq_zero

/-- The Cuntz/Fock branches satisfy the CAR anticommutator in creation/right order. -/
@[rep_depth operator]
theorem branch_creation_annihilation_car
    (h : IsSplitFockCuntzClock car clock) :
    clock.S_right * clock.S_left + clock.S_left * clock.S_right = 1 := by
  rw [h.1, h.2]
  exact car.anticommutator_eq_one

/-- The Cuntz/Fock branches satisfy the CAR anticommutator in left/right order. -/
@[rep_depth operator]
theorem branch_left_right_car
    (h : IsSplitFockCuntzClock car clock) :
    clock.S_left * clock.S_right + clock.S_right * clock.S_left = 1 := by
  rw [h.1, h.2]
  calc
    car.creation * car.annihilation + car.annihilation * car.creation
        = car.annihilation * car.creation + car.creation * car.annihilation := by
          rw [add_comm]
    _ = 1 := car.anticommutator_eq_one

@[rep_depth operator]
theorem branch_right_left_idempotent
    (h : IsSplitFockCuntzClock car clock) :
    (clock.S_right * clock.S_left) *
        (clock.S_right * clock.S_left) =
      clock.S_right * clock.S_left := by
  rw [h.1, h.2]
  exact car.annihilation_creation_idempotent

@[rep_depth operator]
theorem branch_left_right_idempotent
    (h : IsSplitFockCuntzClock car clock) :
    (clock.S_left * clock.S_right) *
        (clock.S_left * clock.S_right) =
      clock.S_left * clock.S_right := by
  rw [h.1, h.2]
  exact car.creation_annihilation_idempotent

@[rep_depth operator]
theorem branch_right_left_orthogonal_left_right
    (h : IsSplitFockCuntzClock car clock) :
    (clock.S_right * clock.S_left) *
        (clock.S_left * clock.S_right) = 0 := by
  rw [h.1, h.2]
  exact car.annihilation_creation_orthogonal

@[rep_depth operator]
theorem branch_left_right_orthogonal_right_left
    (h : IsSplitFockCuntzClock car clock) :
    (clock.S_left * clock.S_right) *
        (clock.S_right * clock.S_left) = 0 := by
  rw [h.1, h.2]
  exact car.creation_annihilation_orthogonal

/-! ## Bott-limit transport for the split Fock clock -/

abbrev Stage (n : ℕ) : Type :=
  InfoGeometry.Canonical.CuntzCliffordBottBridge.Stage n

/--
The split-Fock Cuntz clock has constant image in the `Cl(1,1)` Bott direct
limit whenever the encoder commutes with one clock tick and the Bott bonding
maps.
-/
@[rep_depth operator]
theorem constant_in_cl11_limit
    (encode : ∀ n : ℕ, Op → Stage n)
    (seed : Op)
    (hcompat : ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n
          (encode n (Nat.iterate clock.sigma n seed)) =
        encode (n + 1) (Nat.iterate clock.sigma (n + 1) seed)) :
    ∀ n : ℕ,
      ofStage n (encode n (Nat.iterate clock.sigma n seed)) =
        ofStage 0 (encode 0 seed) := by
  exact cuntz_clock_constant_in_cl11_limit
    (M := clock) (encode := encode) (seed := seed) hcompat

/--
Creation seeds remain square-zero after transport through a compatible
split-Fock Cuntz clock into the `Cl(1,1)` Bott direct limit.
-/
@[rep_depth operator]
theorem creation_seed_square_zero_in_cl11_limit
    (encode : ∀ n : ℕ, Op → Stage n)
    (hcompat : ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n
          (encode n (Nat.iterate clock.sigma n car.creation)) =
        encode (n + 1) (Nat.iterate clock.sigma (n + 1) car.creation))
    (hencode0 : encode 0 car.creation * encode 0 car.creation = 0) :
    ∀ n : ℕ,
      ofStage n (encode n (Nat.iterate clock.sigma n car.creation)) *
          ofStage n (encode n (Nat.iterate clock.sigma n car.creation)) = 0 := by
  exact cuntz_clock_square_zero_in_cl11_limit
    (M := clock) (encode := encode) (seed := car.creation)
    (hcompat := hcompat) (h0 := hencode0)

/--
Annihilation seeds remain square-zero after transport through a compatible
split-Fock Cuntz clock into the `Cl(1,1)` Bott direct limit.
-/
@[rep_depth operator]
theorem annihilation_seed_square_zero_in_cl11_limit
    (encode : ∀ n : ℕ, Op → Stage n)
    (hcompat : ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n
          (encode n (Nat.iterate clock.sigma n car.annihilation)) =
        encode (n + 1) (Nat.iterate clock.sigma (n + 1) car.annihilation))
    (hencode0 : encode 0 car.annihilation * encode 0 car.annihilation = 0) :
    ∀ n : ℕ,
      ofStage n (encode n (Nat.iterate clock.sigma n car.annihilation)) *
          ofStage n (encode n (Nat.iterate clock.sigma n car.annihilation)) = 0 := by
  exact cuntz_clock_square_zero_in_cl11_limit
    (M := clock) (encode := encode) (seed := car.annihilation)
    (hcompat := hcompat) (h0 := hencode0)

end SplitFockCuntzClock

end InfoGeometry.Canonical.CelikKocakCuntzFockBridge
