/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
import InfoGeometry.Causal.FiniteDependencySchedule

/-!
# Causal schedules and noncommutative operator semantics

The existing de Bruijn rotor archetype has a diamond dependency poset: its
oscillator and rotor branches are incomparable, and either may occur first in
a valid topological schedule. This file assigns those two events the existing
noncommuting `2 × 2` integer-matrix operators and proves that the two valid
schedules produce different composites.

This is a finite counterexample to schedule-independent replay without an
independence law for concurrent events. A distributed compiler or peer
replication layer must either impose a canonical order or prove that operators
on reorderable events commute. The theorem says nothing about cryptographic
hashes, Lean kernel execution, network consensus, or the semantics of arbitrary
InfoTrees.
-/

namespace InfoGeometry.Canonical.CausalScheduleMatrixSemantics

open InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
open InfoGeometry.Canonical.DeBruijnRotorAlternationCycle.DeBruijnRotorArchetype
open InfoGeometry.Causal.FiniteDependencySchedule

abbrev Operator := Matrix (Fin 2) (Fin 2) ℤ

/-- The two incomparable diamond events act by the existing off-diagonal seeds. -/
def eventOperator : DeBruijnRotorArchetype → Operator
  | .deBruijnOneHillTwoPoles => 1
  | .infinitesimalAlternationOscillator => seedD
  | .algebraicCircularRotor => seedB
  | .movingIdempotentAndNonCommutingWitness => 1

/-- Composite obtained by applying the listed event operators in schedule order
to column states; each later event acts by left multiplication. -/
def scheduleOperator (schedule : List DeBruijnRotorArchetype) : Operator :=
  schedule.foldl (fun composite event => eventOperator event * composite) 1

/-- The second topological order swaps only the incomparable middle events. -/
def alternateSchedule : List DeBruijnRotorArchetype :=
  [.deBruijnOneHillTwoPoles, .infinitesimalAlternationOscillator,
   .algebraicCircularRotor, .movingIdempotentAndNonCommutingWitness]

theorem canonicalSchedule_valid :
    ValidSchedule (∅ : Finset DeBruijnRotorArchetype)
      DeBruijnRotorArchetype.canonicalSchedule := by
  decide

theorem alternateSchedule_valid :
    ValidSchedule (∅ : Finset DeBruijnRotorArchetype) alternateSchedule := by
  decide

theorem canonicalSchedule_same_events :
    DeBruijnRotorArchetype.canonicalSchedule.toFinset = alternateSchedule.toFinset := by
  decide

@[simp] theorem canonicalSchedule_operator :
    scheduleOperator DeBruijnRotorArchetype.canonicalSchedule = seedD * seedB := by
  simp [scheduleOperator, eventOperator,
    DeBruijnRotorArchetype.canonicalSchedule]

@[simp] theorem alternateSchedule_operator :
    scheduleOperator alternateSchedule = seedB * seedD := by
  simp [scheduleOperator, eventOperator, alternateSchedule]

/-- For these two topological schedules, replay agrees exactly when the two
branch operators commute. -/
theorem schedule_replay_agrees_iff_branch_operators_commute :
    scheduleOperator DeBruijnRotorArchetype.canonicalSchedule =
        scheduleOperator alternateSchedule ↔ seedD * seedB = seedB * seedD := by
  rw [canonicalSchedule_operator, alternateSchedule_operator]

/-- Both replicas can respect the same causal diamond and receive the same
events, yet obtain different operator composites because the branch actions
are genuinely noncommuting. -/
theorem valid_replicas_can_diverge :
    ∃ first second : List DeBruijnRotorArchetype,
      ValidSchedule (∅ : Finset DeBruijnRotorArchetype) first ∧
      ValidSchedule (∅ : Finset DeBruijnRotorArchetype) second ∧
      first.toFinset = second.toFinset ∧
      scheduleOperator first ≠ scheduleOperator second := by
  refine ⟨DeBruijnRotorArchetype.canonicalSchedule, alternateSchedule,
    canonicalSchedule_valid, alternateSchedule_valid,
    canonicalSchedule_same_events, ?_⟩
  rw [canonicalSchedule_operator, alternateSchedule_operator]
  exact mat2Z_rotor_alternation_witness.1

end InfoGeometry.Canonical.CausalScheduleMatrixSemantics
