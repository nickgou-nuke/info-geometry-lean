import Mathlib.Tactic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Basic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

Discrete wavelets with quaternion / Clifford coefficients.

Literature owner:
  Peter Fletcher, "Discrete Wavelets with Quaternion and Clifford Coefficients"
  in Advances in Applied Clifford Algebras.

This file owns a theorem-safe interface for:

* an abstract remainder-size model inspired by Hurwitz integers;
* abstract star-ring-valued filter coefficients;
* pointwise low/high branch normalization;
* the resulting pointwise norm-square sum rule;
* cascade realizations carrying explicit convergence, compact-range,
  and reconstruction witnesses.

It does not yet define a genuine polyphase paraunitary matrix, derive perfect
reconstruction from filter identities, prove energy preservation of an
analysis operator, or identify the signal carrier with an `L²` space.
-/

noncomputable section

namespace InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

/-- Abstract remainder-size packet inspired by the Hurwitz integer lattice. -/
@[rep_depth operator]
structure HurwitzIntegerModel where
  Point : Type
  [instZero : Zero Point]
  [instAdd : Add Point]
  [instMul : Mul Point]
  [instInv : Inv Point]
  normSq : Point → ℝ
  divisionWithRemainder :
    ∀ a b : Point, b ≠ 0 →
      ∃ q r : Point, a = q * b + r ∧ normSq r < normSq b

attribute [instance] HurwitzIntegerModel.instZero
attribute [instance] HurwitzIntegerModel.instAdd
attribute [instance] HurwitzIntegerModel.instMul
attribute [instance] HurwitzIntegerModel.instInv

/-- The owner packet carries a full quotient-remainder witness. -/
@[rep_depth operator]
theorem HurwitzIntegerModel.exists_division_remainder (h : HurwitzIntegerModel)
    (a b : h.Point) (hb : b ≠ 0) :
    ∃ q r : h.Point, a = q * b + r ∧ h.normSq r < h.normSq b :=
  h.divisionWithRemainder a b hb

/-- Corollary: the owner packet exposes a bounded remainder readout. -/
@[rep_depth operator]
theorem HurwitzIntegerModel.exists_bounded_remainder (h : HurwitzIntegerModel)
    (b : h.Point) (hb : b ≠ 0) :
    ∃ r : h.Point, h.normSq r < h.normSq b := by
  rcases h.exists_division_remainder 0 b hb with ⟨_q, r, _h_eq, h_lt⟩
  exact ⟨r, h_lt⟩

/-- Abstract quaternion / Clifford coefficient model. -/
@[rep_depth operator]
structure CliffordCoefficientModel where
  Coeff : Type
  [instRing : Ring Coeff]
  [instStarRing : StarRing Coeff]
  normSq : Coeff → ℝ

attribute [instance] CliffordCoefficientModel.instRing
attribute [instance] CliffordCoefficientModel.instStarRing

/-- Abstract discrete filter index set. -/
@[rep_depth operator]
abbrev DiscreteFilterIndex := Type

namespace DiscreteFilterIndex

abbrev Index (I : DiscreteFilterIndex) : Type := I

end DiscreteFilterIndex

/-- Two-channel quaternion / Clifford filter-bank packet. -/
@[rep_depth operator]
structure ParaunitaryCliffordFilterBank where
  lattice : HurwitzIntegerModel
  coeffs : CliffordCoefficientModel
  index : DiscreteFilterIndex
  lowPass : index.Index → coeffs.Coeff
  highPass : index.Index → coeffs.Coeff

/-- Pointwise low/high branch normalization. -/
@[rep_depth operator]
def normalizedBranches (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/-- Backward-compatible alias for the historical name. -/
@[rep_depth operator]
def paraunitary (F : ParaunitaryCliffordFilterBank) : Prop :=
  normalizedBranches F

/--
Pointwise sum readout: for each index `i`, the low-pass and high-pass
coefficient norm-squares add to `1`.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.sum_normSq_eq_one
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  ∀ i : F.index.Index,
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i) = (1 : ℝ)

/-- Convert branch normalization to the pointwise sum readout. -/
@[rep_depth operator]
theorem ParaunitaryCliffordFilterBank.sum_normSq_eq_one_of_normalizedBranches
    (F : ParaunitaryCliffordFilterBank)
    (h : normalizedBranches F) :
    F.sum_normSq_eq_one := by
  rcases h with ⟨hl, hh⟩
  intro i
  calc
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i)
        = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
      rw [hl i, hh i]
    _ = (1 : ℝ) := by ring

/-- Backward-compatible alias from the historical name. -/
@[rep_depth operator]
theorem sum_normSq_eq_one_of_paraunitary (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches h

/-- Historical compatibility alias: this owner does not prove perfect reconstruction. -/
@[rep_depth operator]
theorem perfectReconstruction_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  sum_normSq_eq_one_of_paraunitary F h

/-- Historical compatibility alias: this owner does not prove an energy isometry. -/
@[rep_depth operator]
theorem energyPreservation_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  sum_normSq_eq_one_of_paraunitary F h

/-- Discrete cascade realization attached to a normalized two-channel filter bank. -/
@[rep_depth operator]
structure CliffordCascadeSystem
    (F : ParaunitaryCliffordFilterBank) where
  Signal : Type*
  [signalNorm : NormedAddCommGroup Signal]
  [signalComplete : CompleteSpace Signal]
  scalingApproximation : ℕ → Signal
  waveletDetail : ℕ → Signal
  branchNormalization : normalizedBranches F
  cascadeLimit : Signal
  cascadeConverges : Filter.Tendsto scalingApproximation Filter.atTop (nhds cascadeLimit)
  compactRange : IsCompact (Set.range scalingApproximation)
  analysis : Signal → Signal
  synthesis : Signal → Signal
  reconstruction_leftInverse : Function.LeftInverse synthesis analysis

namespace CliffordCascadeSystem

variable {F : ParaunitaryCliffordFilterBank}

/-- The normalized branches supply the pointwise sum rule. -/
def sumRuleWitness (C : CliffordCascadeSystem F) : F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches C.branchNormalization

/-- The explicit convergence witness carried by the cascade packet. -/
def convergenceWitness (C : CliffordCascadeSystem F) : Prop :=
  letI := C.signalNorm
  Filter.Tendsto C.scalingApproximation Filter.atTop (nhds C.cascadeLimit)

/-- Compatibility alias for the old over-strong name. -/
def regularityWitness (C : CliffordCascadeSystem F) : Prop :=
  C.convergenceWitness

/-- Convergence in the owned signal norm. -/
def cascadeConvergesInSignalNorm (C : CliffordCascadeSystem F) : Prop :=
  C.convergenceWitness

/-- Compatibility alias for the old `L²`-sounding name. -/
def cascadeConvergesL2 (C : CliffordCascadeSystem F) : Prop :=
  C.cascadeConvergesInSignalNorm

/-- Compactness of the scaling-approximation image. -/
def scalingApproximation_range_compact (C : CliffordCascadeSystem F) : Prop :=
  letI := C.signalNorm
  IsCompact (Set.range C.scalingApproximation)

/-- Compatibility alias for the old compact-uniform name. -/
def compactUniformUpgrade (C : CliffordCascadeSystem F) : Prop :=
  C.scalingApproximation_range_compact

/-- Reconstruction exists because the owner carries a concrete left inverse. -/
def reconstructionWitnessExists (C : CliffordCascadeSystem F) : Prop :=
  ∃ R : C.Signal → C.Signal, ∀ s, R (C.analysis s) = s

/-- Compatibility alias for the old existential name. -/
def reconstructionExists (C : CliffordCascadeSystem F) : Prop :=
  C.reconstructionWitnessExists

theorem reconstruction_exists (C : CliffordCascadeSystem F) :
    C.reconstructionWitnessExists := by
  exact ⟨C.synthesis, C.reconstruction_leftInverse⟩

theorem reconstructed_signal (C : CliffordCascadeSystem F) (s : C.Signal) :
    C.synthesis (C.analysis s) = s :=
  C.reconstruction_leftInverse s

end CliffordCascadeSystem

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
