import proofs.ChiralConeAlgebraFinality
import proofs.GrandUnifiedTKK
import proofs.ZornAssociatorSplitOctonion

/-!
# Chiral causal cone to TKK grading bridge

This file identifies the chiral operators already present in the repo with the
same split-octonion-style lanes that we want to route into the five TKK grades.

The intent is theorem-honest and finite:

* `SPlus`/`SMinus` are the two chiral projectors and land in grade `g_0`;
* `NPlus`/`NMinus` are the nilpotent lanes and land in grades `g_1`/`g_neg1`;
* the concrete Zorn associator witness is the extremal defect lane and lands
  in grade `g_2`.

Nothing here claims a full operator-algebra embedding. This is the carrier-side
grading interface.
-/

noncomputable section

namespace ChiralCausalConeTKKBridge

open ChiralConeAlgebraFinality
open GrandUnifiedTKK
open ZornAssociatorSplitOctonion

/-- Alias names for the same chiral basis objects. -/
abbrev SPlus : M2C := ChiralConeAlgebraFinality.NPlus
abbrev SMinus : M2C := ChiralConeAlgebraFinality.NMinus
abbrev NPlus : M2C := ChiralConeAlgebraFinality.sPlus
abbrev NMinus : M2C := ChiralConeAlgebraFinality.sMinus

/-- Lane tags for the causal/chiral carrier. -/
inductive ChiralLane where
  | projectorPlus
  | projectorMinus
  | nilUpper
  | nilLower
  | associatorDefect
  deriving DecidableEq, Repr

/-- Mirror involution on lane tags. -/
def laneMirror : ChiralLane → ChiralLane
  | .projectorPlus => .projectorPlus
  | .projectorMinus => .projectorMinus
  | .nilUpper => .nilLower
  | .nilLower => .nilUpper
  | .associatorDefect => .associatorDefect

@[simp]
theorem laneMirror_involutive (s : ChiralLane) :
    laneMirror (laneMirror s) = s := by
  cases s <;> rfl

/-- The TKK grade landing map for the chiral carrier. -/
def laneGrade : ChiralLane → TKK_Grade
  | .projectorPlus => TKK_Grade.g_0
  | .projectorMinus => TKK_Grade.g_0
  | .nilUpper => TKK_Grade.g_1
  | .nilLower => TKK_Grade.g_neg1
  | .associatorDefect => TKK_Grade.g_2

@[simp] theorem laneGrade_projectorPlus : laneGrade ChiralLane.projectorPlus = TKK_Grade.g_0 := rfl
@[simp] theorem laneGrade_projectorMinus : laneGrade ChiralLane.projectorMinus = TKK_Grade.g_0 := rfl
@[simp] theorem laneGrade_nilUpper : laneGrade ChiralLane.nilUpper = TKK_Grade.g_1 := rfl
@[simp] theorem laneGrade_nilLower : laneGrade ChiralLane.nilLower = TKK_Grade.g_neg1 := rfl
@[simp] theorem laneGrade_associatorDefect : laneGrade ChiralLane.associatorDefect = TKK_Grade.g_2 := rfl

/-- The projectors sum to the identity, i.e. the neutral TKK sector. -/
theorem projector_sum :
    SPlus + SMinus = (1 : M2C) := by
  have hComplete := ChiralConeAlgebraFinality.chiral_projector_completeness
  simpa [SPlus, SMinus] using hComplete

/-- The nilpotent source lanes square to zero. -/
theorem nilpotent_source_upper : NPlus * NPlus = 0 :=
  ChiralConeAlgebraFinality.sPlus_sq_zero

theorem nilpotent_source_lower : NMinus * NMinus = 0 :=
  ChiralConeAlgebraFinality.sMinus_sq_zero

theorem nilpotent_source :
    NPlus * NPlus = 0 ∧ NMinus * NMinus = 0 := by
  constructor
  · exact nilpotent_source_upper
  · exact nilpotent_source_lower

/-- The concrete associator witness is nonzero and therefore belongs to the
extremal defect sector. -/
def associatorWitness : ZornAssociatorSplitOctonion.Zorn :=
  ZornAssociatorSplitOctonion.associator (U e₁) (L e₁) (U e₂)

theorem associatorWitness_nonzero : associatorWitness ≠ 0 := by
  simpa [associatorWitness] using ZornAssociatorSplitOctonion.associator_U₁_L₁_U₂_nonzero

/-- The canonical carrier-side routing theorem. -/
theorem chiral_causal_cone_tkk_synthesis :
    laneGrade ChiralLane.projectorPlus = TKK_Grade.g_0 ∧
    laneGrade ChiralLane.projectorMinus = TKK_Grade.g_0 ∧
    laneGrade ChiralLane.nilUpper = TKK_Grade.g_1 ∧
    laneGrade ChiralLane.nilLower = TKK_Grade.g_neg1 ∧
    laneGrade ChiralLane.associatorDefect = TKK_Grade.g_2 ∧
    laneMirror (laneMirror ChiralLane.nilUpper) = ChiralLane.nilUpper ∧
    SPlus + SMinus = (1 : M2C) ∧
    NPlus * NPlus = 0 ∧
    NMinus * NMinus = 0 ∧
    associatorWitness ≠ 0 := by
  have hProjectorPlus : laneGrade ChiralLane.projectorPlus = TKK_Grade.g_0 :=
    laneGrade_projectorPlus
  have hProjectorMinus : laneGrade ChiralLane.projectorMinus = TKK_Grade.g_0 :=
    laneGrade_projectorMinus
  have hNilUpper : laneGrade ChiralLane.nilUpper = TKK_Grade.g_1 :=
    laneGrade_nilUpper
  have hNilLower : laneGrade ChiralLane.nilLower = TKK_Grade.g_neg1 :=
    laneGrade_nilLower
  have hDefect : laneGrade ChiralLane.associatorDefect = TKK_Grade.g_2 :=
    laneGrade_associatorDefect
  have hMirror :
      laneMirror (laneMirror ChiralLane.nilUpper) = ChiralLane.nilUpper :=
    laneMirror_involutive _
  exact ⟨hProjectorPlus, hProjectorMinus, hNilUpper, hNilLower, hDefect, hMirror,
    projector_sum, nilpotent_source_upper, nilpotent_source_lower, associatorWitness_nonzero⟩

end ChiralCausalConeTKKBridge
