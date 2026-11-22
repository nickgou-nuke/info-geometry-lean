/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Order
import InfoGeometry.Canonical.CEBKMOnsagerChannelExchange

/-!
# Dependency poset for the finite noncommutative Gibbs--CE--BKM Onsager chain

The labels below track dependencies between the actual finite operator-algebra
theorems imported above. The operator carrier, faithful Gibbs state, CE/Fréchet
readout, centered BKM covariance, dissipative form, curvature probe, channel
exchange parity, and Casimir reciprocity are not identified with one another.
The order records only this finite theorem corridor; it says nothing about
physical time, continuum limits, or analytic completion.

The independent branches are retained: the faithful-state/BKM route and the
CE/Fréchet readout route meet at the two Onsager forms. Dissipation and the
curvature probe remain incomparable until their common parity-system stage.
-/

namespace InfoGeometry.Canonical.CEBKMOnsagerCausalPoset

/-- Proof stages named by the finite noncommutative Gibbs/CE/BKM owner chain. -/
inductive Stage where
  | operatorCarrier
  | faithfulGibbsState
  | frechetCEDirection
  | centeredBKMCovariance
  | familyCEReadout
  | dissipativeBKMForm
  | curvatureProbeForm
  | channelExchange
  | exchangeParity
  | parityOnsagerSystem
  | casimirReciprocity
  deriving DecidableEq, Repr

/-- Prerequisite indices for the source-backed branches. Set inclusion defines
this encoding's order; indices distinguish dependency branches, not operators. -/
def prerequisites : Stage → Finset ℕ
  | .operatorCarrier => {0}
  | .faithfulGibbsState => {0, 1}
  | .frechetCEDirection => {0, 2}
  | .centeredBKMCovariance => {0, 1, 3}
  | .familyCEReadout => {0, 2, 4}
  | .dissipativeBKMForm => {0, 1, 2, 3, 4, 5}
  | .curvatureProbeForm => {0, 1, 2, 3, 4, 6}
  | .channelExchange => {0, 7}
  | .exchangeParity => {0, 1, 2, 3, 4, 5, 6, 7, 8}
  | .parityOnsagerSystem => {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
  | .casimirReciprocity => {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}

theorem prerequisites_injective : Function.Injective prerequisites := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals revert h; decide

/-- The source-dependency order is a genuine partial order and preserves the
incomparability of parallel theorem branches. -/
instance : PartialOrder Stage := PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Stage) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

/-- The finite operator carrier is the root stage. -/
theorem operatorCarrier_precedes_all (s : Stage) : Stage.operatorCarrier ≤ s := by
  cases s <;> decide

/-- Faithful Gibbs normalization and the CE/Fréchet direction are separate
branches above the common noncommutative operator carrier. -/
theorem gibbs_and_CE_branches_incomparable :
    ¬ Stage.faithfulGibbsState ≤ Stage.frechetCEDirection ∧
      ¬ Stage.frechetCEDirection ≤ Stage.faithfulGibbsState := by
  decide

/-- Centered covariance and the family CE readout are separate inputs to the
aggregate dissipative form. -/
theorem covariance_and_readout_branches_incomparable :
    ¬ Stage.centeredBKMCovariance ≤ Stage.familyCEReadout ∧
      ¬ Stage.familyCEReadout ≤ Stage.centeredBKMCovariance := by
  decide

/-- The dissipative and curvature forms are parallel branches; neither is
ordered before the other in this dependency encoding. -/
theorem dissipative_and_curvature_branches_incomparable :
    ¬ Stage.dissipativeBKMForm ≤ Stage.curvatureProbeForm ∧
      ¬ Stage.curvatureProbeForm ≤ Stage.dissipativeBKMForm := by
  decide

theorem dissipative_precedes_exchangeParity :
    Stage.dissipativeBKMForm ≤ Stage.exchangeParity := by decide

theorem curvature_precedes_exchangeParity :
    Stage.curvatureProbeForm ≤ Stage.exchangeParity := by decide

theorem channelExchange_precedes_exchangeParity :
    Stage.channelExchange ≤ Stage.exchangeParity := by decide

theorem exchangeParity_precedes_paritySystem :
    Stage.exchangeParity ≤ Stage.parityOnsagerSystem := by decide

theorem paritySystem_precedes_casimirReciprocity :
    Stage.parityOnsagerSystem ≤ Stage.casimirReciprocity := by decide

end InfoGeometry.Canonical.CEBKMOnsagerCausalPoset
