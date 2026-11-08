import InfoGeometry.Analysis.BipolarPeriodDescent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarLogarithmicRootCharacterRepresentation
import InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
import Mathlib.Tactic

/-!
# Period descent of the bipolar adjoint characters

The full root characters `exp(±W)` are invariant when a local logarithmic
potential is shifted by a period in `2πiℤ`.  Consequently the adjoint weights on
`σPlus` and `σMinus` descend to the logarithmic-potential quotient.

The half-Cartan lift is more refined: an elementary period produces the central
spinorial sign `-I₂`.  That sign is nontrivial on spinors but disappears in the
adjoint action.  This is the exact double-cover correction to the informal claim
that all branching is simply absent.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarPeriodAdjointDescentBridge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
open InfoGeometry.Canonical.BipolarLogarithmicRootCharacterRepresentation
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
open InfoGeometry.Physics.ChiralCausalCone

/-- Quotient class of the chosen principal logarithmic readout. -/
def bipolarLogClass (s : ℂ) : LogPotentialQuotient :=
  Quotient.mk _ (bipolarLog s)

/-- The descended exponential recovers the globally defined canonical Möbius
coordinate on the punctured domain. -/
theorem descendedExp_bipolarLogClass
    {s : ℂ} (hs : s ∈ punctured01) :
    descendedExp (bipolarLogClass s) = crossRatio01 s := by
  rw [bipolarLogClass, descendedExp_mk, exp_bipolarLog hs]

/-- The positive root character is invariant under period equivalence. -/
theorem plusRootCharacter_period_invariant
    {W₁ W₂ : ℂ} (h : PeriodEquivalent W₁ W₂) :
    plusRootCharacter W₁ = plusRootCharacter W₂ := by
  exact exp_eq_of_PeriodEquivalent h

/-- The negative root character is invariant under the same period equivalence. -/
theorem minusRootCharacter_period_invariant
    {W₁ W₂ : ℂ} (h : PeriodEquivalent W₁ W₂) :
    minusRootCharacter W₁ = minusRootCharacter W₂ := by
  rw [minusRootCharacter_eq_inv, minusRootCharacter_eq_inv,
    plusRootCharacter_period_invariant h]

/-- Both scalar root-space actions are independent of the logarithmic branch. -/
theorem rootActions_period_invariant
    {W₁ W₂ : ℂ} (h : PeriodEquivalent W₁ W₂) :
    plusRootCharacter W₁ • σPlus = plusRootCharacter W₂ • σPlus ∧
      minusRootCharacter W₁ • σMinus = minusRootCharacter W₂ • σMinus := by
  exact ⟨by rw [plusRootCharacter_period_invariant h],
    by rw [minusRootCharacter_period_invariant h]⟩

/-- The plus-sheet finite adjoint weight is the descended exponential of the
logarithmic-potential class. -/
theorem finiteAdjointFlow_sigmaPlus_descends
    {s : ℂ} (hs : s ∈ punctured01) :
    finiteAdjointFlow s σPlus =
      descendedExp (bipolarLogClass s) • σPlus := by
  rw [finiteAdjointFlow_sigmaPlus_eq_crossRatio hs,
    descendedExp_bipolarLogClass hs]

/-- The minus-sheet finite adjoint weight is the inverse descended exponential. -/
theorem finiteAdjointFlow_sigmaMinus_descends
    {s : ℂ} (hs : s ∈ punctured01) :
    finiteAdjointFlow s σMinus =
      (descendedExp (bipolarLogClass s))⁻¹ • σMinus := by
  rw [finiteAdjointFlow_sigmaMinus_eq_crossRatio_inv hs,
    descendedExp_bipolarLogClass hs]

/-- Full-character triviality and half-Cartan monodromy coexist: an elementary
period is killed by `exp`, but its half lift is the nontrivial central sign. -/
theorem full_character_half_cartan_distinction
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Complex.exp (circulationPeriod originWinding) = 1 ∧
      spinHolonomy originWinding =
        -(1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      spinHolonomy originWinding * X * spinHolonomy originWinding = X := by
  exact ⟨exp_circulationPeriod originWinding,
    spinHolonomy_origin,
    originHolonomy_adjoint_trivial X⟩

/-- Compact period-to-adjoint descent packet. -/
theorem bipolar_period_adjoint_descent_packet
    {s : ℂ} (hs : s ∈ punctured01)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    descendedExp (bipolarLogClass s) = crossRatio01 s ∧
      finiteAdjointFlow s σPlus =
        descendedExp (bipolarLogClass s) • σPlus ∧
      finiteAdjointFlow s σMinus =
        (descendedExp (bipolarLogClass s))⁻¹ • σMinus ∧
      spinHolonomy originWinding * X * spinHolonomy originWinding = X := by
  exact ⟨descendedExp_bipolarLogClass hs,
    finiteAdjointFlow_sigmaPlus_descends hs,
    finiteAdjointFlow_sigmaMinus_descends hs,
    originHolonomy_adjoint_trivial X⟩

end InfoGeometry.Canonical.BipolarPeriodAdjointDescentBridge

