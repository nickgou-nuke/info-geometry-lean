import InfoGeometry.Quantum.KitaevChain
import InfoGeometry.Canonical.RNDeterminantConnesChainBridge
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SYKTwoCopyInterface

Strict scaffold for separating:

- current owner theorem surfaces already compiled in this repository,
- formalizable next-owner targets for two-copy coupled SYK-like protocols,
- external interpretation claims that are not yet owner-compiled.

This file does not claim holographic traversability or literal spacetime
realization. It provides boundary-safe interfaces only.
-/

namespace InfoGeometry.Canonical.SYKTwoCopyInterface

open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Canonical.RNDeterminantConnesChainBridge
open InfoGeometry.Volume.ConnesCocycle

section ClaimTier

/-- Claim-status bands for scope-safe protocol language. -/
@[rep_depth transport]
inductive ClaimTier where
  | repoTheorem
  | formalizableNextOwnerTarget
  | externalInterpretation
  deriving DecidableEq, Repr

/--
A proposition indexed by claim-status band.

The proposition is a type parameter rather than an opaque structure field, so
claim classification cannot erase the theorem being classified.
-/
@[rep_depth transport]
def TaggedClaim (statement : Prop) := ClaimTier

namespace TaggedClaim

def tier {P : Prop} (C : TaggedClaim P) : ClaimTier := C

/-- Proposition indexed by a tagged claim, retained under the historical name. -/
@[rep_depth transport]
def statement {P : Prop} (_C : TaggedClaim P) : Prop :=
  P

/-- Predicate: this claim is in the compiled owner theorem band. -/
@[rep_depth transport]
def isRepoTheorem {P : Prop} (C : TaggedClaim P) : Prop :=
  C.tier = ClaimTier.repoTheorem

/-- Predicate: this claim is tagged as a formalizable-next-owner target. -/
@[owner_target_tag]
def isFormalizableNextOwnerTarget {P : Prop} (C : TaggedClaim P) : Prop :=
  C.tier = ClaimTier.formalizableNextOwnerTarget

/-- Predicate: this claim is an external interpretation claim. -/
@[rep_depth transport]
def isExternalInterpretation {P : Prop} (C : TaggedClaim P) : Prop :=
  C.tier = ClaimTier.externalInterpretation

/-- Formalizable-next-owner claims are not repo-theorem claims. -/
@[rep_depth transport]
theorem formalizableNextOwnerTarget_not_repoTheorem
    {P : Prop}
    (C : TaggedClaim P)
    (hTarget : C.isFormalizableNextOwnerTarget) :
    ¬ C.isRepoTheorem := by
  intro hRepo
  unfold isFormalizableNextOwnerTarget at hTarget
  unfold isRepoTheorem at hRepo
  rw [hTarget] at hRepo
  cases hRepo

/-- External-interpretation claims are not repo-theorem claims. -/
@[rep_depth transport]
theorem externalInterpretation_not_repoTheorem
    {P : Prop}
    (C : TaggedClaim P)
    (hExt : C.isExternalInterpretation) :
    ¬ C.isRepoTheorem := by
  intro hRepo
  unfold isExternalInterpretation at hExt
  unfold isRepoTheorem at hRepo
  rw [hExt] at hRepo
  cases hRepo

end TaggedClaim

end ClaimTier

section TwoCopyFinite

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "EndH" => H →L[ℝ] H

/--
Finite two-copy coupled-system scaffold:
left/right generators with a scalar-weighted cross-coupling.
-/
@[rep_depth operator]
structure TwoCopyCoupledSystem where
  H_left : EndH
  H_right : EndH
  couplingLR : EndH
  μ : ℝ

namespace TwoCopyCoupledSystem

variable (S : TwoCopyCoupledSystem (H := H))

/-- Effective cross-coupling operator `μ V`. -/
@[rep_depth operator]
def effectiveCrossCoupling : EndH :=
  S.μ • S.couplingLR

/-- Sign-sensitive open-window predicate (protocol lane). -/
@[rep_depth transport]
def traversableWindowOpen : Prop :=
  S.μ < 0

/-- Complementary closed-window predicate. -/
@[rep_depth transport]
def traversableWindowClosed : Prop :=
  0 ≤ S.μ

 /-- Open window iff the closed-window predicate is false. -/
@[rep_depth transport]
theorem traversableWindowOpen_iff_not_closed :
    S.traversableWindowOpen ↔ ¬ S.traversableWindowClosed := by
  constructor
  · intro hOpen hClosed
    exact (not_le_of_gt hOpen) hClosed
  · intro hNotClosed
    by_cases hClosed : S.traversableWindowClosed
    · exact False.elim (hNotClosed hClosed)
    · exact lt_of_not_ge hClosed

/-- Open and closed windows are incompatible. -/
@[rep_depth transport]
theorem traversableWindowOpen_not_closed
    (hOpen : S.traversableWindowOpen)
    (hClosed : S.traversableWindowClosed) :
    False := by
  exact (not_le_of_gt hOpen) hClosed

/-- Every scalar coupling lies in exactly one sign-side window. -/
@[rep_depth transport]
theorem traversableWindow_side_split :
    S.traversableWindowOpen ∨ S.traversableWindowClosed := by
  unfold traversableWindowOpen traversableWindowClosed
  exact lt_or_ge S.μ 0

/--
TFD-like finite preparation record:
state plus normalization law only; no holographic semantics asserted.
-/
@[rep_depth transport]
structure TFDLikePreparation where
  psi : H
  normalized : ‖psi‖ = 1

/-- Formalizable-next-target protocol claim constructor. -/
@[rep_depth transport]
def traversableProtocolTargetClaim : TaggedClaim S.traversableWindowOpen :=
  ClaimTier.formalizableNextOwnerTarget

/-- The formalizable target claim is explicitly non-repo by tier tag. -/
@[rep_depth transport]
theorem traversableProtocolTargetClaim_not_repo :
    ¬ (traversableProtocolTargetClaim (S := S)).isRepoTheorem := by
  exact TaggedClaim.formalizableNextOwnerTarget_not_repoTheorem
    (C := traversableProtocolTargetClaim (S := S))
    (hTarget := rfl)

/-- External ER=EPR interpretation claim constructor (kept non-owner by type tag). -/
@[rep_depth transport]
def erEprInterpretationClaim : TaggedClaim S.traversableWindowOpen :=
  ClaimTier.externalInterpretation

/-- The ER=EPR interpretation constructor is never tagged as repo theorem. -/
@[rep_depth transport]
theorem erEprInterpretationClaim_not_repo :
    ¬ (erEprInterpretationClaim (S := S)).isRepoTheorem := by
  exact TaggedClaim.externalInterpretation_not_repoTheorem
    (C := erEprInterpretationClaim (S := S))
    (hExt := rfl)

/--
Closed finite protocol property:
normalized preparation plus an explicit open-window proof.
-/
@[rep_depth transport]
structure TraversableProtocolWitness where
  prep : TFDLikePreparation (H := H)
  openWindow : S.traversableWindowOpen

/-- Repo-tier claim materialized from a closed finite protocol property. -/
@[rep_depth transport]
def traversableProtocolRepoClaim (_w : TraversableProtocolWitness (S := S)) :
    TaggedClaim S.traversableWindowOpen :=
  ClaimTier.repoTheorem

/-- Witness-built repo claim is tagged in the repo theorem band. -/
@[rep_depth transport]
theorem traversableProtocolRepoClaim_is_repo
    (w : TraversableProtocolWitness (S := S)) :
    (traversableProtocolRepoClaim (S := S) w).isRepoTheorem := by
  rfl

/-- Witness-built repo claim carries a concrete proof of the open-window statement. -/
@[rep_depth transport]
theorem traversableProtocolRepoClaim_holds
    (w : TraversableProtocolWitness (S := S)) :
    (traversableProtocolRepoClaim (S := S) w).statement := by
  exact w.openWindow

end TwoCopyCoupledSystem

end TwoCopyFinite

section OwnerAnchorWrappers

/--
Owner-anchor wrapper: finite Kitaev `ℤ₂` append law.
This is a compiled owner theorem surface in current repo state.
-/
@[rep_depth transport]
theorem topologicalIndexZ2_append_owner
    (chain₁ chain₂ : List KitaevCell)
    (h₁ : macroscopicVolume chain₁ ≠ 0)
    (h₂ : macroscopicVolume chain₂ ≠ 0) :
    topologicalIndexZ2 (chain₁ ++ chain₂)
      = topologicalIndexZ2 chain₁ + topologicalIndexZ2 chain₂ :=
  topologicalIndexZ2_append_of_macroscopicVolume_ne_zero chain₁ chain₂ h₁ h₂

/-- Tagged repo-tier claim for the finite `ℤ₂` append owner theorem. -/
@[rep_depth transport]
def topologicalIndexZ2_append_owner_claim.{u} :
    TaggedClaim
      (∀ (chain₁ chain₂ : List (InfoGeometry.Quantum.KitaevChain.KitaevCell.{u})),
        macroscopicVolume chain₁ ≠ 0 →
        macroscopicVolume chain₂ ≠ 0 →
        topologicalIndexZ2 (chain₁ ++ chain₂)
          = topologicalIndexZ2 chain₁ + topologicalIndexZ2 chain₂) :=
  ClaimTier.repoTheorem

/-- The finite `ℤ₂` append owner claim is tagged as repo theorem. -/
@[rep_depth transport]
theorem topologicalIndexZ2_append_owner_claim_is_repo.{u} :
    (topologicalIndexZ2_append_owner_claim.{u}).isRepoTheorem := by
  rfl

/-- The finite `ℤ₂` append owner claim is constructively inhabited. -/
@[rep_depth transport]
theorem topologicalIndexZ2_append_owner_claim_holds.{u} :
    (topologicalIndexZ2_append_owner_claim.{u}).statement := by
  intro chain₁ chain₂ h₁ h₂
  exact topologicalIndexZ2_append_owner chain₁ chain₂ h₁ h₂

section Connes

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Owner-anchor wrapper: Connes state-chain law.
This remains the primary chain rule on the noncommutative modular lane.
-/
@[rep_depth transport]
theorem connesCocycle_state_chain_owner
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → AlgebraEnd E)
    (hCocycle : IsConnesCocycle σ u)
    (s t : ℝ) :
    u (s + t) = u s * σ s (u t) :=
  connesCocycle_state_chain (σ := σ) (u := u) hCocycle s t

/-- Tagged repo-tier claim for the Connes cocycle owner chain law. -/
@[rep_depth transport]
def connesCocycle_state_chain_owner_claim :
    TaggedClaim
      (∀ (σ : AdditiveModularFlow (H := E))
        (u : ℝ → AlgebraEnd E),
        IsConnesCocycle σ u →
        ∀ (s t : ℝ),
        u (s + t) = u s * σ s (u t)) :=
  ClaimTier.repoTheorem

/-- The Connes cocycle owner claim is tagged as repo theorem. -/
@[rep_depth transport]
theorem connesCocycle_state_chain_owner_claim_is_repo :
    (connesCocycle_state_chain_owner_claim (E := E)).isRepoTheorem := by
  rfl

/-- The Connes cocycle owner claim is constructively inhabited. -/
@[rep_depth transport]
theorem connesCocycle_state_chain_owner_claim_holds :
    (connesCocycle_state_chain_owner_claim (E := E)).statement := by
  intro σ u hCocycle s t
  exact connesCocycle_state_chain_owner σ u hCocycle s t

end Connes

end OwnerAnchorWrappers

end InfoGeometry.Canonical.SYKTwoCopyInterface
