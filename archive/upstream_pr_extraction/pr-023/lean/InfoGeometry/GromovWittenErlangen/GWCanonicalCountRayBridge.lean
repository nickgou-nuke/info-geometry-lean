import InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration
import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Canonical.RelativeSurprisalOperatorLift
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.GromovWittenErlangen.GWCanonicalCountRayBridge

Finite canonical count-ray bridge for the GW/Erlangen localization lane.

This module connects the GW projective-count calibration surface to the
repo-owned finite count-ray implementation in
`Canonical.RelativePotentialCountBridge`.

The point is deliberately narrow:

* GW localization supplies a count shadow;
* a finite positive count carrier supplies the canonical `countRay`;
* projective count Hamiltonians and log-generators are the existing
  relative-modular-potential readouts of that ray.

No virtual localization theorem, Drazin theorem, Frobenius theorem,
Atiyah-Singer theorem, or probability-first interpretation is asserted here.
-/

noncomputable section

namespace InfoGeometry.GromovWittenErlangen

open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.RelativePotentialDiscreteBridge
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeSurprisalOperatorLift
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

/--
Canonical finite count-ray realization of a GW projective-count calibration.

`projectiveCounts` owns the GW localization/count-shadow side.  The finite
`counts` and `ref` profiles are the repo-native positive count profiles whose
projective rays carry the relative modular/count Hamiltonian readout.
-/
@[rep_depth projective]
structure GWCanonicalCountRayBridge
    (n : ℕ) [Nonempty (Fin n)]
    (G T Target Coeff : Type*) where
  /-- GW localization count-shadow calibration. -/
  projectiveCounts :
    GWProjectiveCountCalibration G T Target Coeff

  /-- Positive finite count profile for the localized state. -/
  counts :
    RelativeCounts n

  /-- Positive finite reference count profile. -/
  ref :
    RelativeCounts n

  /-- Positivity witness for the localized count profile. -/
  counts_pos :
    ∀ i : Fin n, 0 < counts i

  /-- Positivity witness for the reference count profile. -/
  ref_pos :
    ∀ i : Fin n, 0 < ref i

  /--
  Model-supplied law saying this finite count carrier realizes the same
  projective count shadow as the GW localization packet.
  -/
  finiteCarrierShadowLaw :
    Prop

  /-- Certificate for the finite-carrier shadow law. -/
  finiteCarrierShadow_valid :
    finiteCarrierShadowLaw

namespace GWCanonicalCountRayBridge

variable {n : ℕ} [Nonempty (Fin n)]
variable {G T Target Coeff : Type*}
variable (B : GWCanonicalCountRayBridge n G T Target Coeff)

/-- The GW localization-to-count shadow law is available. -/
theorem countShadow_holds :
    B.projectiveCounts.countShadowLaw :=
  B.projectiveCounts.countShadow_valid

/-- The finite carrier realizes the supplied GW projective count shadow. -/
theorem finiteCarrierShadow_holds :
    B.finiteCarrierShadowLaw :=
  B.finiteCarrierShadow_valid

/-- Canonical positive count ray of the localized finite count profile. -/
def stateRay : PositiveRay (Fin n) :=
  countRay B.counts B.counts_pos

/-- Canonical positive count ray of the finite reference count profile. -/
def referenceRay : PositiveRay (Fin n) :=
  countRay B.ref B.ref_pos

/-- Probability gauge section of the localized count ray. -/
def stateFinProb : InfoGeometry.FinProb (Fin n) :=
  gaugeSectionFinProb (α := Fin n) B.stateRay

/-- Probability gauge section of the reference count ray. -/
def referenceFinProb : InfoGeometry.FinProb (Fin n) :=
  gaugeSectionFinProb (α := Fin n) B.referenceRay

/-- Gauge section of the localized count ray is normalized by count mass. -/
theorem gaugeSection_stateRay_apply
    (i : Fin n) :
    gaugeSection (α := Fin n) B.stateRay i =
      B.counts i / countMass B.counts B.counts_pos := by
  exact gaugeSection_countRay_apply
    (n := n) (counts := B.counts) (hcounts := B.counts_pos) i

/-- Gauge section of the reference count ray is normalized by count mass. -/
theorem gaugeSection_referenceRay_apply
    (i : Fin n) :
    gaugeSection (α := Fin n) B.referenceRay i =
      B.ref i / countMass B.ref B.ref_pos := by
  exact gaugeSection_countRay_apply
    (n := n) (counts := B.ref) (hcounts := B.ref_pos) i

/--
The probability gauge section of the localized count ray has real mass equal to
the normalized positive count profile.
-/
theorem stateFinProb_apply_toReal
    (i : Fin n) :
    (B.stateFinProb i).toReal =
      B.counts i / countMass B.counts B.counts_pos := by
  exact gaugeSectionFinProb_countRay_apply_toReal
    (n := n) (counts := B.counts) (hcounts := B.counts_pos) i

/--
The probability gauge section of the reference count ray has real mass equal to
the normalized positive reference profile.
-/
theorem referenceFinProb_apply_toReal
    (i : Fin n) :
    (B.referenceFinProb i).toReal =
      B.ref i / countMass B.ref B.ref_pos := by
  exact gaugeSectionFinProb_countRay_apply_toReal
    (n := n) (counts := B.ref) (hcounts := B.ref_pos) i

/-- First-quantized density matrix of the probability gauge of the count ray. -/
def stateDensityMatrix : FinMat n :=
  densityMatrixOfFinProb B.stateFinProb

/-- First-quantized surprisal operator of the probability gauge of the count ray. -/
def stateSurprisalOperator : FinMat n :=
  surprisalOperator B.stateFinProb

/-- Diagonal density entries are the normalized count masses. -/
theorem stateDensityMatrix_diag
    (i : Fin n) :
    B.stateDensityMatrix i i =
      B.counts i / countMass B.counts B.counts_pos := by
  rw [stateDensityMatrix, densityMatrixOfFinProb_diag]
  exact B.stateFinProb_apply_toReal i

/-- Entropy of the probability gauge is the expectation of the surprisal operator. -/
theorem entropy_eq_diagonalExpectation_stateSurprisalOperator :
    InfoGeometry.entropy B.stateFinProb =
      diagonalExpectation B.stateFinProb B.stateSurprisalOperator := by
  rw [stateSurprisalOperator]
  exact entropy_eq_diagonalExpectation_surprisalOperator B.stateFinProb

/-- Projective relative density of the count rays as a repo-owned count readout. -/
def projectiveDelta : Fin n → ℝ :=
  projectiveCountDelta B.counts B.ref B.counts_pos B.ref_pos

/-- Projective logarithmic relative density of the count rays. -/
def projectiveLogDelta : Fin n → ℝ :=
  projectiveCountLogDelta B.counts B.ref B.counts_pos B.ref_pos

/-- Projective count Hamiltonian profile of the localized/reference pair. -/
def projectiveHamiltonianProfile : Fin n → ℝ :=
  projectiveCountHamiltonianProfile B.counts B.ref B.counts_pos B.ref_pos

/--
The projective count Hamiltonian is exactly the relative modular potential of
the canonical count rays.
-/
@[rep_depth projective]
theorem projectiveHamiltonianProfile_eq_relativeModularPotential
    (i : Fin n) :
    B.projectiveHamiltonianProfile i =
      relativeModularPotential (α := Fin n) B.stateRay B.referenceRay i := by
  exact projectiveCountHamiltonianProfile_eq_relativeModularPotential_countRay
    (n := n) (counts := B.counts) (ref := B.ref)
    (hcounts := B.counts_pos) (href := B.ref_pos) i

/--
The projective count Hamiltonian differs from the raw count Hamiltonian by the
repo-owned scalar mass-shift term.
-/
theorem projectiveHamiltonianProfile_eq_raw_sub_massShift
    (i : Fin n) :
    B.projectiveHamiltonianProfile i =
      rawCountHamiltonianProfile n B.counts B.ref i -
        countMassShift B.counts B.ref B.counts_pos B.ref_pos := by
  exact projectiveCountHamiltonianProfile_eq_rawCountHamiltonianProfile_sub_massShift
    (n := n) (counts := B.counts) (ref := B.ref)
    (hcounts := B.counts_pos) (href := B.ref_pos) i

/-- The projective count density is the exponential of minus the Hamiltonian. -/
theorem projectiveDelta_eq_exp_neg_projectiveHamiltonianProfile
    (i : Fin n) :
    B.projectiveDelta i =
      Real.exp (-(B.projectiveHamiltonianProfile i)) := by
  change
    projectiveCountDelta B.counts B.ref B.counts_pos B.ref_pos i =
      Real.exp
        (-(projectiveCountHamiltonianProfile
            B.counts B.ref B.counts_pos B.ref_pos i))
  rw [projectiveCountHamiltonianProfile]
  exact projectiveCountDelta_eq_exp_neg_projectiveCountModularProfile
    (n := n) (counts := B.counts) (ref := B.ref)
    (hcounts := B.counts_pos) (href := B.ref_pos) i

/-- The self-relative projective count density is one. -/
theorem projectiveDelta_self
    (i : Fin n) :
    projectiveCountDelta B.counts B.counts B.counts_pos B.counts_pos i = 1 :=
  projectiveCountDelta_self
    (n := n) (counts := B.counts) (hcounts := B.counts_pos) i

/-- The self-relative projective count Hamiltonian vanishes. -/
theorem projectiveHamiltonianProfile_self
    (i : Fin n) :
    projectiveCountHamiltonianProfile
        B.counts B.counts B.counts_pos B.counts_pos i = 0 :=
  projectiveCountHamiltonianProfile_self
    (n := n) (counts := B.counts) (hcounts := B.counts_pos) i

end GWCanonicalCountRayBridge

end InfoGeometry.GromovWittenErlangen
