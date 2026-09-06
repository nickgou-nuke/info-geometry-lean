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

/-- The owner packet carries a full quotient-remainder property. -/
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

/-- Historical compatibility alias: this owner exposes only the normalized
sum-rule readout, not a perfect-reconstruction theorem. -/
@[rep_depth operator]
theorem sumRule_of_paraunitary_legacy
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  sum_normSq_eq_one_of_paraunitary F h

/-- Historical compatibility alias: this owner exposes only the normalized
sum-rule readout, not an energy-isometry theorem. -/
@[rep_depth operator]
theorem sumRule_of_paraunitary_energy_legacy
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
theorem sumRule_of_cascade (C : CliffordCascadeSystem F) : F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches C.branchNormalization

theorem cascade_converges (C : CliffordCascadeSystem F) :
    letI := C.signalNorm
    Filter.Tendsto C.scalingApproximation Filter.atTop (nhds C.cascadeLimit) :=
  C.cascadeConverges

theorem scalingApproximation_range_isCompact (C : CliffordCascadeSystem F) :
    letI := C.signalNorm
    IsCompact (Set.range C.scalingApproximation) :=
  C.compactRange

theorem reconstructed_signal (C : CliffordCascadeSystem F) (s : C.Signal) :
    C.synthesis (C.analysis s) = s :=
  C.reconstruction_leftInverse s

/- The reconstruction theorem above is the direct left-inverse fact; no
   existential reconstruction interface is needed. -/
end CliffordCascadeSystem

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
