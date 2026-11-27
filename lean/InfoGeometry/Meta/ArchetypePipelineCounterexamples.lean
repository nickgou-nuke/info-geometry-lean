/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchetypePipeline

namespace InfoGeometry.MetaCompiler

/-!
`TypedArchetype Input .proved` certifies `∀ x : Input, claim x`.  This is a
valid universal proposition, but it need not describe any realizable input:
when `Input` is empty, even the constantly-false claim has such evidence.
The witness-indexed promotion theorem below states the stronger contract
available when an actual input is part of the promotion evidence.
-/

/-- A proved status can carry a universally true but uninhabited claim. -/
def emptyInputFalseArchetype : TypedArchetype Empty .proved where
  name := `emptyInputFalse
  phase := 0
  claim := fun _ => False
  evidence := fun impossible => nomatch impossible

/-- The stored evidence is valid, despite there being no input at which to use it. -/
theorem emptyInputFalseArchetype_has_universal_evidence :
    ∀ x : Empty, emptyInputFalseArchetype.claim x :=
  emptyInputFalseArchetype.evidence

/-- The empty carrier has no witness, exposing the vacuity boundary precisely. -/
theorem emptyInput_has_no_witness : ¬ Nonempty Empty := by
  rintro ⟨x⟩
  cases x

/-- If promotion supplies a concrete input, the proved archetype has an inhabited
domain as well as its universal claim evidence. -/
theorem promotion_with_input_witness_has_inhabited_domain
    {Input : Type} {s : Status} (arch : TypedArchetype Input s)
    (input : Input) (proof : ∀ x : Input, arch.claim x) :
    Nonempty Input ∧
      (TypedArchetype.promoteToProved arch proof).claim input := by
  exact ⟨⟨input⟩, proof input⟩

end InfoGeometry.MetaCompiler
