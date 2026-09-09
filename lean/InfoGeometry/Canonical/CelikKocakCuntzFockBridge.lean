import InfoGeometry.Canonical.CuntzCliffordBottBridge
import InfoGeometry.Canonical.CuntzMapKreinBridge
import InfoGeometry.Canonical.CelikKocakInfiniteCantorCliffordFockSocket
import InfoGeometry.Topology.FractalCantorFockWitness

/-!
# Çelik--Koçak Split Fock Data as a Cuntz Clock

This file records the honest finite bridge:

`creation / annihilation CAR data -> Cuntz clock branches -> Cl(1,1) Bott tower`.

It does not assert that a concrete Cuntz algebra is isomorphic to the analytic
infinite Clifford/Fock completion.  The Cuntz/Fock identification is exposed as
explicit data, and the direct-limit consequences are inherited from the already
proved `CuntzCliffordBottBridge`.

#### BUCKET 1: CLOSED FINITE THEOREMS
The Cuntz branches read back to creation/annihilation under the supplied split
Fock clock, and the CAR/nilpotence laws transfer to those branches.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The `Cl(1,1)` direct-limit statements require an encoder compatible with the
Cuntz clock and Bott bonding maps.

#### BUCKET 3: OPEN CLOSURE DEBT
The analytic infinite Fock completion, `O_2`/CAR isomorphism, K-theory
vanishing, and historical attribution beyond the existing socket citation.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakCuntzFockBridge

open InfoGeometry.Canonical.CuntzMapKreinBridge
open InfoGeometry.Canonical.CuntzCliffordBottBridge
open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Clifford.Cl11TensorTowerLimit

variable {Op : Type*} [Ring Op] [StarRing Op]

/--
Split Fock clock data: a real CAR pair whose creation/annihilation operators
are the left/right branches of a witnessed Cuntz modular step.
-/
@[rep_depth operator]
structure SplitFockCuntzClock (Op : Type*) [Ring Op] [StarRing Op] where
  car : RealCARPair Op
  clock : DiscreteCuntzModularStep Op
  left_eq_creation : clock.S_left = car.creation
  right_eq_annihilation : clock.S_right = car.annihilation

namespace SplitFockCuntzClock

variable (F : SplitFockCuntzClock Op)

/-- The left Cuntz branch is the split-Fock creation operator. -/
@[rep_depth operator]
theorem left_branch_eq_creation :
    F.clock.S_left = F.car.creation :=
  F.left_eq_creation

/-- The right Cuntz branch is the split-Fock annihilation operator. -/
@[rep_depth operator]
theorem right_branch_eq_annihilation :
    F.clock.S_right = F.car.annihilation :=
  F.right_eq_annihilation

/-- The left Cuntz/Fock branch is nilpotent under the supplied CAR data. -/
@[rep_depth operator]
theorem left_branch_sq_zero :
    F.clock.S_left * F.clock.S_left = 0 := by
  rw [F.left_eq_creation]
  exact F.car.creation_sq_zero

/-- The right Cuntz/Fock branch is nilpotent under the supplied CAR data. -/
@[rep_depth operator]
theorem right_branch_sq_zero :
    F.clock.S_right * F.clock.S_right = 0 := by
  rw [F.right_eq_annihilation]
  exact F.car.annihilation_sq_zero

/-- The Cuntz/Fock branches satisfy the CAR anticommutator in creation/right order. -/
@[rep_depth operator]
theorem branch_creation_annihilation_car :
    F.clock.S_right * F.clock.S_left + F.clock.S_left * F.clock.S_right = 1 := by
  rw [F.left_eq_creation, F.right_eq_annihilation]
  exact F.car.anticommutator_eq_one

/-- The Cuntz/Fock branches satisfy the CAR anticommutator in left/right order. -/
@[rep_depth operator]
theorem branch_left_right_car :
    F.clock.S_left * F.clock.S_right + F.clock.S_right * F.clock.S_left = 1 := by
  rw [F.left_eq_creation, F.right_eq_annihilation]
  calc
    F.car.creation * F.car.annihilation + F.car.annihilation * F.car.creation
        = F.car.annihilation * F.car.creation + F.car.creation * F.car.annihilation := by
          rw [add_comm]
    _ = 1 := F.car.anticommutator_eq_one

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
          (encode n (Nat.iterate F.clock.sigma n seed)) =
        encode (n + 1) (Nat.iterate F.clock.sigma (n + 1) seed)) :
    ∀ n : ℕ,
      ofStage n (encode n (Nat.iterate F.clock.sigma n seed)) =
        ofStage 0 (encode 0 seed) := by
  exact cuntz_clock_constant_in_cl11_limit
    (M := F.clock) (encode := encode) (seed := seed) hcompat

/--
Creation seeds remain square-zero after transport through a compatible
split-Fock Cuntz clock into the `Cl(1,1)` Bott direct limit.
-/
@[rep_depth operator]
theorem creation_seed_square_zero_in_cl11_limit
    (encode : ∀ n : ℕ, Op → Stage n)
    (hcompat : ∀ n : ℕ,
      InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n
          (encode n (Nat.iterate F.clock.sigma n F.car.creation)) =
        encode (n + 1) (Nat.iterate F.clock.sigma (n + 1) F.car.creation))
    (hencode0 : encode 0 F.car.creation * encode 0 F.car.creation = 0) :
    ∀ n : ℕ,
      ofStage n (encode n (Nat.iterate F.clock.sigma n F.car.creation)) *
          ofStage n (encode n (Nat.iterate F.clock.sigma n F.car.creation)) = 0 := by
  exact cuntz_clock_square_zero_in_cl11_limit
    (M := F.clock) (encode := encode) (seed := F.car.creation)
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
          (encode n (Nat.iterate F.clock.sigma n F.car.annihilation)) =
        encode (n + 1) (Nat.iterate F.clock.sigma (n + 1) F.car.annihilation))
    (hencode0 : encode 0 F.car.annihilation * encode 0 F.car.annihilation = 0) :
    ∀ n : ℕ,
      ofStage n (encode n (Nat.iterate F.clock.sigma n F.car.annihilation)) *
          ofStage n (encode n (Nat.iterate F.clock.sigma n F.car.annihilation)) = 0 := by
  exact cuntz_clock_square_zero_in_cl11_limit
    (M := F.clock) (encode := encode) (seed := F.car.annihilation)
    (hcompat := hcompat) (h0 := hencode0)

end SplitFockCuntzClock

end InfoGeometry.Canonical.CelikKocakCuntzFockBridge
