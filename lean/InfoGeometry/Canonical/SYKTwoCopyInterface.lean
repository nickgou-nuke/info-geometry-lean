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

/-!
The finite protocol data is represented directly: a normalized preparation and
a proof that the scalar coupling is on the open side of the sign split.
-/
structure TraversableProtocolData where
  prep : TFDLikePreparation (H := H)
  openWindow : S.traversableWindowOpen

end TwoCopyCoupledSystem

end TwoCopyFinite

section OwnerTheorems

/-!
The following are direct theorem consequences of the existing Kitaev and
Connes owners; no claim-status encoding is involved.
-/
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

end OwnerTheorems

end InfoGeometry.Canonical.SYKTwoCopyInterface
