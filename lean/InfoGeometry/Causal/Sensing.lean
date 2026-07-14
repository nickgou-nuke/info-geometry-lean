import Mathlib
open Set

/-!
# Sensing — The Formal Sensing Function

A `Sensor` maps one causal order into another without reversing implication.
The forward/backward cone definitions are self-contained.
-/

namespace Sensing

/-- Forward cone in a Preorder. -/
def forwardCone [Preorder α] (a : α) : Set α := {b | a ≤ b}

/-- Backward cone in a Preorder. -/
def backwardCone [Preorder α] (a : α) : Set α := {b | b ≤ a}

section SensingBridge

variable {World Proof : Type*} [Preorder World] [Preorder Proof]

/--
A `Sensor` maps one causal order into another without reversing implication.
-/
structure Sensor (World Proof : Type*) [Preorder World] [Preorder Proof] where
  sense : World → Proof
  monotone_sense : Monotone sense

theorem sensor_maps_forward
    (S : Sensor World Proof) {a b : World}
    (h : b ∈ forwardCone a) : S.sense b ∈ forwardCone (S.sense a) :=
  S.monotone_sense h

theorem sensor_maps_backward
    (S : Sensor World Proof) {a b : World}
    (h : b ∈ backwardCone a) : S.sense b ∈ backwardCone (S.sense a) :=
  S.monotone_sense h

/--
A faithful sensor reflects proof-order comparison back into the sensed domain.
-/
structure FaithfulSensor
    (World Proof : Type*) [Preorder World] [Preorder Proof]
    extends Sensor World Proof where
  reflects_order : ∀ {a b : World}, sense a ≤ sense b → a ≤ b

theorem faithful_sensor_reflects_order
    (S : FaithfulSensor World Proof) {a b : World}
    (h : S.sense a ≤ S.sense b) : a ≤ b :=
  S.reflects_order h

theorem faithful_sensor_reflects_no_loop
    (S : FaithfulSensor World Proof) {a b : World}
    (hab : S.sense a ≤ S.sense b) (hba : S.sense b ≤ S.sense a) :
    a ≤ b ∧ b ≤ a :=
  ⟨S.reflects_order hab, S.reflects_order hba⟩

end SensingBridge

section InterpretationLayer

variable {World Proof : Type*} [Preorder World] [Preorder Proof]

theorem sensing_interprets_forward_cone
    (S : Sensor World Proof) {a b : World} (h : b ∈ forwardCone a) :
    S.sense b ∈ forwardCone (S.sense a) :=
  sensor_maps_forward S h

theorem sensing_interprets_no_loop
    (S : FaithfulSensor World Proof) {a b : World}
    (hab : S.sense a ≤ S.sense b) (hba : S.sense b ≤ S.sense a) :
    a ≤ b ∧ b ≤ a :=
  faithful_sensor_reflects_no_loop S hab hba

end InterpretationLayer

end Sensing
