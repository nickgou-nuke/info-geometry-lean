import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import InfoGeometry.Meta.ArchetypePipeline

/-!
# The epistemic compiler chain

**QMS Note: METAPROGRAMMING INFRASTRUCTURE ONLY.**
This file is strictly a Lean 4 meta-programming framework and state-tracker for autonomous agents. It does NOT contain mathematical or physical theorems. The terms "Phase", "Status", and "Archetype" refer exclusively to the internal state machine of the automated proof assistant. Do not evaluate this file for mathematical substance.
-/

namespace InfoGeometry.MetaCompiler

inductive Phase
  | primaMateriaIntake
  | archetypalCausalNormalization
  | typedMathematicalProjection
  | proofCarryingScheduling
  | multiAgentCandidateRepair
  | kernelCertifiedPromotion
  deriving DecidableEq, Repr

namespace Phase
def rank : Phase → Nat
  | primaMateriaIntake => 0
  | archetypalCausalNormalization => 1
  | typedMathematicalProjection => 2
  | proofCarryingScheduling => 3
  | multiAgentCandidateRepair => 4
  | kernelCertifiedPromotion => 5
def precedes (earlier later : Phase) : Prop := rank earlier ≤ rank later
instance : DecidableRel precedes := fun earlier later =>
  inferInstanceAs (Decidable (rank earlier ≤ rank later))
theorem precedes_refl (phase : Phase) : precedes phase phase := Nat.le_refl _
theorem precedes_trans {a b c : Phase} : precedes a b → precedes b c → precedes a c := Nat.le_trans
theorem rank_injective : Function.Injective rank := by intro a b h; cases a <;> cases b <;> simp [rank] at h ⊢
theorem precedes_antisymm {a b : Phase} (hab : precedes a b) (hba : precedes b a) : a = b := by apply rank_injective; exact Nat.le_antisymm hab hba
instance : PartialOrder Phase where
  le := precedes
  le_refl := precedes_refl
  le_trans := @precedes_trans
  le_antisymm := @precedes_antisymm
theorem complete : ∀ phase, Phase.rank phase ≤ 5 := by intro phase; cases phase <;> decide
end Phase

/-! `Status` and `TypedArchetype` are owned by `ArchetypePipeline`. Keeping a
second declaration under the same qualified names made the type-level proof
gate and the audited registration pipeline impossible to compose in one
import graph. This module contributes the ordered workflow phases only. -/

namespace Phase

/-- Encode a compiler phase in the natural-number metadata used by the single
    `TypedArchetype` owner. -/
def toNat (phase : Phase) : Nat := rank phase

@[simp] theorem toNat_injective : Function.Injective toNat := rank_injective

end Phase
end InfoGeometry.MetaCompiler
