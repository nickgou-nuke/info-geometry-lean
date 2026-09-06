import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Information.RelativeOrientation

def relativeDensityActualOverReference (actual reference : ℝ) : ℝ :=
  actual / reference

def relativeInformationGenerator (actual reference : ℝ) : ℝ :=
  Real.log (relativeDensityActualOverReference actual reference)

def relativeBoltzmannGenerator (actual reference : ℝ) : ℝ :=
  -Real.log (relativeDensityActualOverReference actual reference)

def arakiRelativeEntropyGenerator (actual reference : ℝ) : ℝ :=
  -Real.log (relativeDensityActualOverReference reference actual)

theorem relativeInformationGenerator_eq_neg_relativeBoltzmannGenerator
    (actual reference : ℝ) :
    relativeInformationGenerator actual reference =
      -relativeBoltzmannGenerator actual reference := by
  simp [relativeInformationGenerator, relativeBoltzmannGenerator]

theorem relativeBoltzmannGenerator_eq_neg_relativeInformationGenerator
    (actual reference : ℝ) :
    relativeBoltzmannGenerator actual reference =
      -relativeInformationGenerator actual reference := by
  simp [relativeInformationGenerator, relativeBoltzmannGenerator]

theorem arakiRelativeEntropyGenerator_eq_relativeInformationGenerator
    (actual reference : ℝ)
    (hactual : 0 < actual)
    (hreference : 0 < reference) :
    arakiRelativeEntropyGenerator actual reference =
      relativeInformationGenerator actual reference := by
  rw [arakiRelativeEntropyGenerator, relativeInformationGenerator,
    relativeDensityActualOverReference, relativeDensityActualOverReference,
    Real.log_div hreference.ne' hactual.ne',
    Real.log_div hactual.ne' hreference.ne']
  ring

theorem relativeBoltzmannGenerator_reversed
    (actual reference : ℝ)
    (hactual : 0 < actual)
    (hreference : 0 < reference) :
    relativeBoltzmannGenerator reference actual =
      relativeInformationGenerator actual reference := by
  exact arakiRelativeEntropyGenerator_eq_relativeInformationGenerator
    actual reference hactual hreference

def finiteReadout
    {n : ℕ} (actual : Fin n → ℝ) (field : Fin n → ℝ) : ℝ :=
  ∑ i, actual i * field i

def finiteRelativeInformation
    {n : ℕ} (actual reference : Fin n → ℝ) : ℝ :=
  finiteReadout actual
    (fun i => relativeInformationGenerator (actual i) (reference i))

def finiteRelativeBoltzmannReadout
    {n : ℕ} (actual reference : Fin n → ℝ) : ℝ :=
  finiteReadout actual
    (fun i => relativeBoltzmannGenerator (actual i) (reference i))

theorem finiteRelativeBoltzmannReadout_eq_neg_relativeInformation
    {n : ℕ} (actual reference : Fin n → ℝ) :
    finiteRelativeBoltzmannReadout actual reference =
      -finiteRelativeInformation actual reference := by
  rw [finiteRelativeBoltzmannReadout, finiteRelativeInformation, finiteReadout,
    finiteReadout, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [relativeBoltzmannGenerator_eq_neg_relativeInformationGenerator]
  ring

def normalizedMicrocanonicalDensity (volume : ℝ) : ℝ :=
  volume⁻¹

def relativeMacroentropy (actualVolume referenceVolume : ℝ) : ℝ :=
  Real.log (actualVolume / referenceVolume)

theorem normalizedMicrocanonicalDensity_ratio
    (actualVolume referenceVolume : ℝ)
    (hactual : 0 < actualVolume)
    (hreference : 0 < referenceVolume) :
    relativeDensityActualOverReference
        (normalizedMicrocanonicalDensity actualVolume)
        (normalizedMicrocanonicalDensity referenceVolume) =
      referenceVolume / actualVolume := by
  rw [relativeDensityActualOverReference, normalizedMicrocanonicalDensity,
    normalizedMicrocanonicalDensity]
  field_simp [hactual.ne', hreference.ne']

theorem relativeBoltzmannGenerator_microcanonical
    (actualVolume referenceVolume : ℝ)
    (hactual : 0 < actualVolume)
    (hreference : 0 < referenceVolume) :
    relativeBoltzmannGenerator
        (normalizedMicrocanonicalDensity actualVolume)
        (normalizedMicrocanonicalDensity referenceVolume) =
      relativeMacroentropy actualVolume referenceVolume := by
  rw [relativeBoltzmannGenerator, relativeMacroentropy,
    normalizedMicrocanonicalDensity_ratio actualVolume referenceVolume hactual hreference,
    Real.log_div hreference.ne' hactual.ne',
    Real.log_div hactual.ne' hreference.ne']
  ring

theorem relativeInformationGenerator_microcanonical
    (actualVolume referenceVolume : ℝ)
    (hactual : 0 < actualVolume)
    (hreference : 0 < referenceVolume) :
    relativeInformationGenerator
        (normalizedMicrocanonicalDensity actualVolume)
        (normalizedMicrocanonicalDensity referenceVolume) =
      -relativeMacroentropy actualVolume referenceVolume := by
  rw [relativeInformationGenerator_eq_neg_relativeBoltzmannGenerator,
    relativeBoltzmannGenerator_microcanonical actualVolume referenceVolume
      hactual hreference]

end InfoGeometry.Information.RelativeOrientation
