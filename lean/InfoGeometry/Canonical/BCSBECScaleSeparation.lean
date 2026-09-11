import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# BCS--BEC Scale-Separation Skeleton

Source context: arXiv:2208.01774v5, "When Superconductivity Crosses Over:
From BCS to BEC" (Chen, Wang, Boyack, Yang, Levin), a review published as
Rev. Mod. Phys. 96, 025002 (2024).

The paper-level physics claim used here is deliberately narrow:

* strict BCS identifies pair formation and condensation at the same temperature;
* BCS--BEC crossover separates the two scales, producing a preformed-pair
  window between condensation and pair formation;
* on the BEC side of the BCS-Leggett ground-state discussion, the fermionic
  chemical potential can be negative, unlike the positive/BCS-side readout.

This file does not formalize superconductivity, a microscopic Hamiltonian,
gap equations, t-matrix theory, KMS dynamics, BEC of prime modes, or any zeta/RH
consequence.  It only records the finite real-order skeleton that can be used
as a theorem-safe interface by downstream thermodynamic modules.
-/

namespace InfoGeometry.Canonical.BCSBECScaleSeparation

noncomputable section

/-- Two temperature scales used in a BCS--BEC crossover readout. -/
structure CrossoverScales where
  /-- Temperature at which pairing / the excitation gap opens. -/
  pairFormationTemp : ℝ
  /-- Temperature at which superconducting/superfluid condensation occurs. -/
  condensationTemp : ℝ

namespace CrossoverScales

/-- Strict BCS scale lock: pairing and condensation occur at the same scale. -/
def IsStrictBCS (S : CrossoverScales) : Prop :=
  S.pairFormationTemp = S.condensationTemp

/-- Crossover scale separation: condensation occurs below pair formation. -/
def IsCrossover (S : CrossoverScales) : Prop :=
  S.condensationTemp < S.pairFormationTemp

/-- The open interval in which pairs are present without condensation. -/
def InPreformedPairWindow (S : CrossoverScales) (T : ℝ) : Prop :=
  S.condensationTemp < T ∧ T < S.pairFormationTemp

/-- The midpoint of the preformed-pair window. -/
def midpointTemp (S : CrossoverScales) : ℝ :=
  (S.condensationTemp + S.pairFormationTemp) / 2

/-- A crossover scale separation is incompatible with strict BCS scale locking. -/
theorem crossover_not_strictBCS
    (S : CrossoverScales) (h : S.IsCrossover) :
    ¬ S.IsStrictBCS := by
  intro hlock
  unfold IsStrictBCS at hlock
  unfold IsCrossover at h
  rw [hlock] at h
  exact (lt_irrefl S.condensationTemp) h

/-- If the crossover scales are separated, the preformed-pair window is nonempty. -/
theorem midpointTemp_mem_preformedPairWindow
    (S : CrossoverScales) (h : S.IsCrossover) :
    S.InPreformedPairWindow S.midpointTemp := by
  unfold InPreformedPairWindow midpointTemp IsCrossover at *
  constructor <;> linarith

/-- The midpoint temperature sits strictly between the two crossover scales. -/
theorem midpointTemp_strictly_between
    (S : CrossoverScales) (h : S.IsCrossover) :
    S.condensationTemp < S.midpointTemp ∧ S.midpointTemp < S.pairFormationTemp := by
  unfold midpointTemp IsCrossover at *
  constructor <;> linarith

/-- Explicit existential version of the preformed-pair window nonemptiness. -/
theorem exists_preformedPairWindow
    (S : CrossoverScales) (h : S.IsCrossover) :
    ∃ T : ℝ, S.InPreformedPairWindow T :=
  ⟨S.midpointTemp, S.midpointTemp_mem_preformedPairWindow h⟩

end CrossoverScales

/-! ## Chemical-potential side readouts -/

/-- BCS-side sign readout for a positive fermionic chemical potential. -/
def IsPositiveChemicalPotential (μ : ℝ) : Prop :=
  0 < μ

/-- BEC-side sign readout for a negative fermionic chemical potential. -/
def IsNegativeChemicalPotential (μ : ℝ) : Prop :=
  μ < 0

/-- Positive and negative chemical-potential side readouts are disjoint. -/
theorem chemicalPotential_sign_readouts_disjoint
    {μ : ℝ} (hpos : IsPositiveChemicalPotential μ) (hneg : IsNegativeChemicalPotential μ) :
    False := by
  unfold IsPositiveChemicalPotential IsNegativeChemicalPotential at *
  linarith

/-- A negative chemical potential cannot simultaneously satisfy the positive-side readout. -/
theorem negativeChemicalPotential_not_positive
    {μ : ℝ} (hneg : IsNegativeChemicalPotential μ) :
    ¬ IsPositiveChemicalPotential μ := by
  intro hpos
  exact chemicalPotential_sign_readouts_disjoint hpos hneg

end

end InfoGeometry.Canonical.BCSBECScaleSeparation
