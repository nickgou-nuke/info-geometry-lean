/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Causal.CertifiedDependencyCompiler
import InfoGeometry.Causal.VerifiedDevelopmentState
import InfoGeometry.Meta.DeclaredResearchDependencies
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Finite Meta-Compiler and Peirce Operator Bridge

## i. Overview

This module formalizes a finite declared dependency protocol, certified development states,
and a generic Peirce operator interpretation. `compiled_protocol_fixed` is a fixed point of
the finite schedule compiler; it is not a theorem that Lean compiles this source file as its
own input. `protocol_fixed_point_with_peirce_aporia` places that schedule result beside the
general square-compression identity in an arbitrary ring, and `scheduleConeExcursion` together
with `schedule_cone_excursion_compiler_fixed_point_and_peirce_aporia` defines the explicit
schedule-to-operator map from `List DeclaredProtocol.Archetype` into `B` whose value on the
compiled fixed-point schedule `alternateSchedule` equals `conePlus P X * coneMinus P X =
P * (X * X) * P - (P * X * P) * (P * X * P)` while its thesis projection on `schedule.reverse`
vanishes.

## ii. Key results

- `DeclaredProtocol.compiled_protocol_fixed`: fixed point of the finite schedule compiler.
- `meta_epistemic_compiler_operator_tetraktys`: operator witnesses for the declared protocol.
- `protocol_fixed_point_with_peirce_aporia`: schedule fixed point and generic Peirce defect.
- `scheduleConeExcursion`, `schedule_cone_excursion_compiler_fixed_point_and_peirce_aporia`:
  typed schedule-to-operator map and compiler fixed-point Peirce aporia theorem (Rank 4).
- `finite_certified_compilation`, `executable_certified_compilation`: finite schedule results.

## iii. Table of contents

- Declared protocol poset and schedules
- Verified development-state bridge
- Finite proof compilation
- Peirce operator interpretation

## iv. References

- Repository owners `InfoGeometry.Causal.FiniteDependencySchedule` and
  `InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys`.

### Three-Bucket Audit Map
* **BUCKET 1 (Keep / Proved Kernel Content):**
  `DeclaredProtocol.compiled_protocol_fixed`, `finite_certified_compilation`,
  `executable_certified_compilation`, `meta_epistemic_compiler_operator_tetraktys`,
  `protocol_fixed_point_with_peirce_aporia`, `scheduleConeExcursion`,
  `schedule_cone_excursion_compiler_fixed_point_and_peirce_aporia`.
* **BUCKET 2 (Delete / Rejected Surrogates):**
  None; all protocol schedules and Peirce operator evaluations are constructive.
* **BUCKET 3 (Conditional / Open Context):**
  Operator identities require an associative ring `[Ring B]` and idempotent `hP : P * P = P`.
-/

namespace InfoGeometry.MetaCompiler

open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.ProofCarryingSchedule

namespace DeclaredProtocol

/-- Six-stage archetype enumeration of the declared dependency protocol. -/
inductive Archetype
  | statementSpecification
  | dependencyOrder
  | admissibility
  | topologicalSchedule
  | proofEvidence
  | certifiedCompilation
  deriving DecidableEq

/-- Explicit equivalence between `Archetype` and `Fin 6`. -/
private def archetypeEquivFin : Archetype ≃ Fin 6 where
  toFun
    | .statementSpecification => 0
    | .dependencyOrder => 1
    | .admissibility => 2
    | .topologicalSchedule => 3
    | .proofEvidence => 4
    | .certifiedCompilation => 5
  invFun
    | 0 => .statementSpecification
    | 1 => .dependencyOrder
    | 2 => .admissibility
    | 3 => .topologicalSchedule
    | 4 => .proofEvidence
    | _ => .certifiedCompilation
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Archetype := Fintype.ofEquiv (Fin 6) archetypeEquivFin.symm

open Archetype

/-- Reflexive prerequisite closure of each `Archetype` stage. -/
def prerequisites : Archetype → Finset Archetype
  | statementSpecification => {statementSpecification}
  | dependencyOrder => {statementSpecification, dependencyOrder}
  | admissibility => {statementSpecification, dependencyOrder, admissibility}
  | topologicalSchedule =>
      {statementSpecification, dependencyOrder, admissibility, topologicalSchedule}
  | proofEvidence => {statementSpecification, proofEvidence}
  | certifiedCompilation =>
      {statementSpecification, dependencyOrder, admissibility, topologicalSchedule,
        proofEvidence, certifiedCompilation}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

instance : DecidableLT Archetype := fun earlier later =>
  decidable_of_iff (earlier ≤ later ∧ ¬ later ≤ earlier) lt_iff_le_not_ge.symm

/-- Membership in a target's prerequisite set is equivalent to the induced order. -/
theorem prerequisite_iff_le (earlier later : Archetype) :
    earlier ∈ prerequisites later ↔ earlier ≤ later := by
  cases earlier <;> cases later <;> decide

/-- A target is admissible exactly when all strict prerequisites are already present. -/
theorem admissible_iff_prerequisites (environment : Finset Archetype) (target : Archetype) :
    IsAdmissible environment target ↔ (prerequisites target).erase target ⊆ environment := by
  constructor
  · intro admissible earlier membership
    rcases Finset.mem_erase.mp membership with ⟨distinct, ancestor⟩
    exact admissible earlier (lt_of_le_of_ne ((prerequisite_iff_le _ _).mp ancestor) distinct)
  · intro included earlier precedes
    exact included (Finset.mem_erase.mpr
      ⟨ne_of_lt precedes, (prerequisite_iff_le _ _).mpr precedes.le⟩)

/-- Scheduling and proof evidence are incomparable in the declared protocol order. -/
theorem scheduling_and_evidence_incomparable :
    ¬ topologicalSchedule ≤ proofEvidence ∧ ¬ proofEvidence ≤ topologicalSchedule := by
  decide

/-- The initial statement-specification node is ready in the empty environment. -/
theorem specification_admissible_empty : IsReady ∅ statementSpecification := by
  decide

/-- Certified compilation requires both the schedule and proof-evidence branches. -/
theorem compilation_requires_both_branches :
    IsAdmissible {statementSpecification, dependencyOrder, admissibility,
      topologicalSchedule, proofEvidence} certifiedCompilation ∧
    ¬ IsAdmissible {statementSpecification, dependencyOrder, admissibility,
      topologicalSchedule} certifiedCompilation ∧
    ¬ IsAdmissible {statementSpecification, dependencyOrder, admissibility,
      proofEvidence} certifiedCompilation := by
  decide

/-- Canonical valid topological schedule of the six protocol archetypes. -/
def schedule : List Archetype :=
  [statementSpecification, dependencyOrder, admissibility,
    topologicalSchedule, proofEvidence, certifiedCompilation]

/-- Alternate valid topological schedule ordering `proofEvidence` before `dependencyOrder`. -/
def alternateSchedule : List Archetype :=
  [statementSpecification, proofEvidence, dependencyOrder,
    admissibility, topologicalSchedule, certifiedCompilation]

/-- The canonical declared schedule satisfies all prerequisite constraints. -/
theorem schedule_valid : ValidSchedule ∅ schedule := by decide

/-- The alternate schedule also satisfies the prerequisite constraints. -/
theorem alternateSchedule_valid : ValidSchedule ∅ alternateSchedule := by decide

/-- The canonical and alternate schedules each cover the full finite archetype type. -/
theorem schedules_complete :
    schedule.toFinset = Finset.univ ∧ alternateSchedule.toFinset = Finset.univ := by decide

/-- The two valid schedules order the incomparable branches differently. -/
theorem schedules_distinct : schedule ≠ alternateSchedule := by decide

/-- Reversing the canonical schedule compiles to the valid alternate schedule. -/
theorem reversed_protocol_compiles :
    InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅ schedule.reverse =
      some alternateSchedule := by decide

/-- The finite compiler leaves the valid alternate schedule fixed. -/
theorem compiled_protocol_fixed :
    InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅ alternateSchedule =
      some alternateSchedule := by decide

end DeclaredProtocol

section DevelopmentBridge

open InfoGeometry.Causal.ProofDAGRepresentation
open InfoGeometry.Causal.VerifiedDevelopmentState

variable {Node : Type*} (graph : ProofDAG Node) [DecidableEq (AsPoset graph)]

/-- Forgets the proof terms of a `CertifiedState` to form a dependency-closed `VerifiedState`. -/
def toDevelopmentState {statement : AsPoset graph → Prop}
    (state : CertifiedState statement) : VerifiedState graph where
  carrier := (state.environment : Set (AsPoset graph))
  dependency_closed := fun precedes membership => state.dependency_closed precedes membership

omit [DecidableEq (AsPoset graph)] in
/-- Every node admitted to a certified development state satisfies its statement. -/
theorem development_membership_has_proof {statement : AsPoset graph → Prop}
    (state : CertifiedState statement) (target : AsPoset graph)
    (membership : target ∈ (toDevelopmentState graph state).carrier) : statement target := by
  change target ∈ (state.environment : Set (AsPoset graph)) at membership
  exact state.proofs target membership

/-- Admitting a ready proved target extends the verified development state. -/
theorem certified_admission_extends_development {statement : AsPoset graph → Prop}
    (state : CertifiedState statement) (target : AsPoset graph)
    (ready : IsReady state.environment target) (proof : statement target) :
    toDevelopmentState graph state ≤
      toDevelopmentState graph (state.extend target ready proof) := by
  let : DecidableEq Node := inferInstanceAs (DecidableEq (AsPoset graph))
  intro node membership
  exact Finset.mem_insert_of_mem membership

end DevelopmentBridge

/-- A finite proof-rule system admits a complete valid schedule carrying proofs of all nodes. -/
theorem finite_certified_compilation {Node : Type*} [PartialOrder Node]
    [DecidableEq Node] [Fintype Node] (statement : Node → Prop)
    (rules : ProofRules statement) :
    ∃ schedule : List Node, ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧ schedule.length = Fintype.card Node ∧
      schedule.toFinset = Finset.univ ∧ ∀ target, statement target := by
  obtain ⟨schedule, valid, distinct, complete, proofs⟩ :=
    finite_proof_compilation statement rules
  refine ⟨schedule, valid, validSchedule_pairwise valid, distinct, ?_, complete, proofs⟩
  have count := validSchedule_card valid
  simpa [complete] using count.symm

/-- Executing the compiler on a complete duplicate-free pending list yields a certified schedule. -/
theorem executable_certified_compilation {Node : Type*} [PartialOrder Node]
    [DecidableEq Node] [Fintype Node] [DecidableLT Node]
    (statement : Node → Prop) (rules : ProofRules statement)
    (pending : List Node) (distinct : pending.Nodup)
    (coverage : pending.toFinset = Finset.univ) :
    ∃ schedule : List Node,
      InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅ pending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧ schedule.length = Fintype.card Node ∧
      schedule.toFinset = Finset.univ ∧ ∀ target, statement target := by
  obtain ⟨schedule, computed, valid, unique, complete, length⟩ :=
    InfoGeometry.Causal.FiniteDependencyCompiler.compile_full pending distinct coverage
  have initialProofs : HasProofs statement ∅ := by
    intro target membership
    exact False.elim (Finset.notMem_empty _ membership)
  have resultProofs := validSchedule_preserves_proofs rules initialProofs valid
  refine ⟨schedule, computed, valid, validSchedule_pairwise valid, unique,
    length, complete, ?_⟩
  intro target
  apply resultProofs target
  simp [complete]

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Maps each protocol archetype to its Peirce operator witness in `B`. -/
def declaredProtocolOperatorWitness (P A C : B) : DeclaredProtocol.Archetype → B
  | .statementSpecification => P
  | .dependencyOrder => conePlus P A
  | .admissibility => coneMinus P C
  | .topologicalSchedule => genPhi P A C
  | .proofEvidence => genSig P A C
  | .certifiedCompilation => genV P A C

/-- The protocol's operator witnesses instantiate the Peirce nilpotence and product laws. -/
theorem meta_epistemic_compiler_operator_tetraktys
    {P : B} (hP : P * P = P) (A C : B) :
    declaredProtocolOperatorWitness P A C .statementSpecification *
      declaredProtocolOperatorWitness P A C .statementSpecification =
      declaredProtocolOperatorWitness P A C .statementSpecification ∧
    declaredProtocolOperatorWitness P A C .dependencyOrder *
      declaredProtocolOperatorWitness P A C .dependencyOrder = 0 ∧
    declaredProtocolOperatorWitness P A C .admissibility *
      declaredProtocolOperatorWitness P A C .admissibility = 0 ∧
    declaredProtocolOperatorWitness P A C .topologicalSchedule *
      declaredProtocolOperatorWitness P A C .topologicalSchedule =
      declaredProtocolOperatorWitness P A C .certifiedCompilation ∧
    declaredProtocolOperatorWitness P A C .proofEvidence *
      declaredProtocolOperatorWitness P A C .proofEvidence -
      declaredProtocolOperatorWitness P A C .certifiedCompilation *
        declaredProtocolOperatorWitness P A C .certifiedCompilation = 0 := by
  dsimp only [declaredProtocolOperatorWitness]
  refine ⟨hP, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The finite protocol compiler has a schedule fixed point, while the same owner's
Peirce operator interpretation has the exact square-compression defect. The latter's
non-vanishing forces both off-diagonal factors to be nonzero; no converse is asserted. -/
theorem protocol_fixed_point_with_peirce_aporia
    {P : B} (hP : P * P = P) (X : B) :
    InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅ DeclaredProtocol.alternateSchedule =
      some DeclaredProtocol.alternateSchedule ∧
    P * (X * X) * P - (P * X * P) * (P * X * P) =
      conePlus P X * coneMinus P X ∧
    (P * (X * X) * P - (P * X * P) * (P * X * P) ≠ 0 →
      conePlus P X ≠ 0 ∧ coneMinus P X ≠ 0) := by
  have hDefect : P * (X * X) * P - (P * X * P) * (P * X * P) =
      conePlus P X * coneMinus P X := by
    dsimp only [conePlus, coneMinus]
    peirce_nf hP
  refine ⟨DeclaredProtocol.compiled_protocol_fixed, hDefect, ?_⟩
  intro hAporia
  rw [hDefect] at hAporia
  constructor
  · intro hPlus
    apply hAporia
    rw [hPlus, zero_mul]
  · intro hMinus
    apply hAporia
    rw [hMinus, mul_zero]

/-- Typed schedule-to-operator interpretation that extracts the ordered off-diagonal cone stages
(`.dependencyOrder`, `.admissibility`) from a protocol schedule `sched : List DeclaredProtocol.Archetype`
and multiplies their operator witnesses `declaredProtocolOperatorWitness P A C` in `B`. -/
def scheduleConeExcursion (P A C : B) (sched : List DeclaredProtocol.Archetype) : B :=
  ((sched.filter (fun a => a == .dependencyOrder || a == .admissibility)).map
    (declaredProtocolOperatorWitness P A C)).prod

/-- **Schedule-to-Operator Interpretation and Compiler Fixed-Point Peirce Aporia (Rank 4).**
1. The two valid schedules `schedule` and `alternateSchedule` evaluate under `scheduleConeExcursion`
   to the same outward-then-inward product `conePlus P A * coneMinus P C`, which equals the
   thesis-projected certified-compilation witness `P * declaredProtocolOperatorWitness P A C .certifiedCompilation * P`.
2. The uncompiled reversed schedule `schedule.reverse` reverses the off-diagonal stages to
   `coneMinus P C * conePlus P A`, whose thesis-corner projection `P * (...) * P` vanishes (`= 0`),
   and the sum of the valid and reversed excursions equals `declaredProtocolOperatorWitness P A C .certifiedCompilation`.
3. Lifting `scheduleConeExcursion P A C` through `FiniteDependencyCompiler.compile ∅` maps
   `schedule.reverse` to `some (conePlus P A * coneMinus P C)` and leaves `alternateSchedule` fixed.
4. For `A = C = X`, `scheduleConeExcursion P X X DeclaredProtocol.alternateSchedule` equals the
   Peirce square-compression aporia `P * (X * X) * P - (P * X * P) * (P * X * P)`. -/
theorem schedule_cone_excursion_compiler_fixed_point_and_peirce_aporia
    {P : B} (hP : P * P = P) (A C X : B) :
    scheduleConeExcursion P A C DeclaredProtocol.schedule = conePlus P A * coneMinus P C ∧
    scheduleConeExcursion P A C DeclaredProtocol.alternateSchedule = conePlus P A * coneMinus P C ∧
    scheduleConeExcursion P A C DeclaredProtocol.schedule.reverse = coneMinus P C * conePlus P A ∧
    P * scheduleConeExcursion P A C DeclaredProtocol.alternateSchedule * P =
      P * declaredProtocolOperatorWitness P A C .certifiedCompilation * P ∧
    P * scheduleConeExcursion P A C DeclaredProtocol.schedule.reverse * P = 0 ∧
    scheduleConeExcursion P A C DeclaredProtocol.alternateSchedule +
        scheduleConeExcursion P A C DeclaredProtocol.schedule.reverse =
      declaredProtocolOperatorWitness P A C .certifiedCompilation ∧
    (InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅
        DeclaredProtocol.schedule.reverse).map (scheduleConeExcursion P A C) =
      some (conePlus P A * coneMinus P C) ∧
    (InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅
        DeclaredProtocol.alternateSchedule).map (scheduleConeExcursion P A C) =
      some (scheduleConeExcursion P A C DeclaredProtocol.alternateSchedule) ∧
    scheduleConeExcursion P X X DeclaredProtocol.alternateSchedule =
      P * (X * X) * P - (P * X * P) * (P * X * P) := by
  have hSched :
      scheduleConeExcursion P A C DeclaredProtocol.schedule = conePlus P A * coneMinus P C := by
    simp [scheduleConeExcursion, DeclaredProtocol.schedule, declaredProtocolOperatorWitness]
  have hAlt :
      scheduleConeExcursion P A C DeclaredProtocol.alternateSchedule =
        conePlus P A * coneMinus P C := by
    simp [scheduleConeExcursion, DeclaredProtocol.alternateSchedule, declaredProtocolOperatorWitness]
  have hRev :
      scheduleConeExcursion P A C DeclaredProtocol.schedule.reverse =
        coneMinus P C * conePlus P A := by
    simp [scheduleConeExcursion, DeclaredProtocol.schedule, declaredProtocolOperatorWitness]
  have hProjValid :
      P * scheduleConeExcursion P A C DeclaredProtocol.alternateSchedule * P =
        P * declaredProtocolOperatorWitness P A C .certifiedCompilation * P := by
    rw [hAlt]
    dsimp [declaredProtocolOperatorWitness]
    peirce_nf hP
  have hProjRev :
      P * scheduleConeExcursion P A C DeclaredProtocol.schedule.reverse * P = 0 := by
    rw [hRev]
    peirce_nf hP
  have hSum :
      scheduleConeExcursion P A C DeclaredProtocol.alternateSchedule +
          scheduleConeExcursion P A C DeclaredProtocol.schedule.reverse =
        declaredProtocolOperatorWitness P A C .certifiedCompilation := by
    rw [hAlt, hRev]
    rfl
  have hCompRev :
      (InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅
          DeclaredProtocol.schedule.reverse).map (scheduleConeExcursion P A C) =
        some (conePlus P A * coneMinus P C) := by
    rw [DeclaredProtocol.reversed_protocol_compiles]
    simp [hAlt]
  have hCompFixed :
      (InfoGeometry.Causal.FiniteDependencyCompiler.compile ∅
          DeclaredProtocol.alternateSchedule).map (scheduleConeExcursion P A C) =
        some (scheduleConeExcursion P A C DeclaredProtocol.alternateSchedule) := by
    rw [DeclaredProtocol.compiled_protocol_fixed]
    rfl
  have hAporia :
      scheduleConeExcursion P X X DeclaredProtocol.alternateSchedule =
        P * (X * X) * P - (P * X * P) * (P * X * P) := by
    have hAltX :
        scheduleConeExcursion P X X DeclaredProtocol.alternateSchedule =
          conePlus P X * coneMinus P X := by
      simp [scheduleConeExcursion, DeclaredProtocol.alternateSchedule, declaredProtocolOperatorWitness]
    rw [hAltX]
    dsimp only [conePlus, coneMinus]
    peirce_nf hP
  exact ⟨hSched, hAlt, hRev, hProjValid, hProjRev, hSum, hCompRev, hCompFixed, hAporia⟩

end NonCommutativeOperatorRealization

end InfoGeometry.MetaCompiler
