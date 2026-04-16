import InfoGeometry.Quantum.KitaevChain
import InfoGeometry.Canonical.RNDeterminantConnesChainBridge
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Meta.Architecture

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

/-- A proposition tagged by claim-status band. -/
@[rep_depth transport]
structure TaggedClaim where
  tier : ClaimTier
  statement : Prop

namespace TaggedClaim

/-- Predicate: this claim is in the compiled owner theorem band. -/
@[rep_depth transport]
def isRepoTheorem (C : TaggedClaim) : Prop :=
  C.tier = ClaimTier.repoTheorem

/-- Predicate: this claim is an external interpretation claim. -/
@[rep_depth transport]
def isExternalInterpretation (C : TaggedClaim) : Prop :=
  C.tier = ClaimTier.externalInterpretation

/-- External-interpretation claims are not repo-theorem claims. -/
@[rep_depth transport]
theorem externalInterpretation_not_repoTheorem
    (C : TaggedClaim)
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
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

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
TFD-like preparation interface placeholder:
state plus normalization law only; no holographic semantics asserted.
-/
@[rep_depth transport]
structure TFDLikePreparation where
  psi : H
  normalized : ‖psi‖ = 1

/-- Formalizable-next-target protocol claim constructor. -/
@[rep_depth transport, capstone]
def traversableProtocolTargetClaim : TaggedClaim where
  tier := ClaimTier.formalizableNextOwnerTarget
  statement := S.traversableWindowOpen

/-- External ER=EPR interpretation claim constructor (kept non-owner by type tag). -/
@[rep_depth transport, capstone]
def erEprInterpretationClaim : TaggedClaim where
  tier := ClaimTier.externalInterpretation
  statement := S.traversableWindowOpen

/-- The ER=EPR interpretation constructor is never tagged as repo theorem. -/
@[rep_depth transport]
theorem erEprInterpretationClaim_not_repo :
    ¬ (erEprInterpretationClaim (S := S)).isRepoTheorem := by
  exact TaggedClaim.externalInterpretation_not_repoTheorem
    (C := erEprInterpretationClaim (S := S))
    (hExt := rfl)

end TwoCopyCoupledSystem

end TwoCopyFinite

section OwnerAnchorWrappers

variable {n : ℕ}

/--
Owner-anchor wrapper: finite Kitaev `ℤ₂` append law.
This is a compiled owner theorem surface in current repo state.
-/
@[rep_depth operator]
theorem topologicalIndexZ2_append_owner
    (chain₁ chain₂ : List KitaevCell)
    (h₁ : macroscopicVolume chain₁ ≠ 0)
    (h₂ : macroscopicVolume chain₂ ≠ 0) :
    topologicalIndexZ2 (chain₁ ++ chain₂)
      = topologicalIndexZ2 chain₁ + topologicalIndexZ2 chain₂ :=
  topologicalIndexZ2_append_of_macroscopicVolume_ne_zero chain₁ chain₂ h₁ h₂

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

end Connes

end OwnerAnchorWrappers

end InfoGeometry.Canonical.SYKTwoCopyInterface
