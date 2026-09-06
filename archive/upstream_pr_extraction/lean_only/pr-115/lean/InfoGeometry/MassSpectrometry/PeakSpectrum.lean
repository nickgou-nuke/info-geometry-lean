import Mathlib

/-!
# Finite peak spectra

A minimal, theorem-safe carrier for centroided mass-spectrometry peaks.
The serialization layer uses Mathlib's native `FreeMonoid`; ordering is an
explicit predicate rather than an assumption about acquisition order.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open scoped BigOperators

/-- A centroided spectral peak with positive mass and nonnegative intensity. -/
structure Peak where
  mass : ℝ
  intensity : ℝ
  mass_pos : 0 < mass
  intensity_nonneg : 0 ≤ intensity

/-- A finite indexed spectrum. -/
abbrev Spectrum (n : ℕ) := Fin n → Peak

/-- Total recorded intensity. -/
def totalIntensity {n : ℕ} (S : Spectrum n) : ℝ :=
  ∑ i, (S i).intensity

/-- First intensity-weighted mass moment. -/
def firstMassMoment {n : ℕ} (S : Spectrum n) : ℝ :=
  ∑ i, (S i).intensity * (S i).mass

theorem totalIntensity_nonneg {n : ℕ} (S : Spectrum n) :
    0 ≤ totalIntensity S := by
  unfold totalIntensity
  exact Finset.sum_nonneg fun i _ => (S i).intensity_nonneg

theorem firstMassMoment_nonneg {n : ℕ} (S : Spectrum n) :
    0 ≤ firstMassMoment S := by
  unfold firstMassMoment
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (S i).intensity_nonneg (le_of_lt (S i).mass_pos)

/-- Free-monoid carrier for a serialized peak sequence. -/
abbrev SpectralSentence := FreeMonoid Peak

/-- Canonical injection of a concrete list into the free monoid. -/
def peakWord (xs : List Peak) : SpectralSentence :=
  FreeMonoid.ofList xs

@[simp] theorem peakWord_toList (xs : List Peak) :
    FreeMonoid.toList (peakWord xs) = xs := by
  simp [peakWord]

/-- Nondecreasing mass order for a chosen serialization. -/
def IsMassSorted (xs : List Peak) : Prop :=
  xs.Pairwise fun p q => p.mass ≤ q.mass

@[simp] theorem isMassSorted_nil : IsMassSorted [] := by
  simp [IsMassSorted]

@[simp] theorem isMassSorted_singleton (p : Peak) : IsMassSorted [p] := by
  simp [IsMassSorted]

/-- A proof-carrying mass-sorted serialization. -/
structure CanonicalSpectrum where
  peaks : List Peak
  sorted : IsMassSorted peaks

/-- List representation of all indexed peaks before imposing an order. -/
def Spectrum.toPeakList {n : ℕ} (S : Spectrum n) : List Peak :=
  List.ofFn S

/-- Deterministic nondecreasing-mass serialization of an indexed spectrum. -/
def Spectrum.canonicalize {n : ℕ} (S : Spectrum n) : CanonicalSpectrum where
  peaks := (S.toPeakList).mergeSort (fun p q => p.mass ≤ q.mass)
  sorted := by
    letI : IsTrans Peak (fun p q : Peak => p.mass ≤ q.mass) :=
      ⟨fun _ _ _ hpq hqr => le_trans hpq hqr⟩
    letI : Std.Total (fun p q : Peak => p.mass ≤ q.mass) :=
      ⟨fun p q => le_total p.mass q.mass⟩
    simpa [IsMassSorted, Spectrum.toPeakList] using
      (List.pairwise_mergeSort'
        (r := fun p q : Peak => p.mass ≤ q.mass)
        (List.ofFn S))

/-- Canonicalization only reorders peaks; it does not create or delete them. -/
theorem Spectrum.canonicalize_perm {n : ℕ} (S : Spectrum n) :
    List.Perm S.canonicalize.peaks S.toPeakList := by
  exact List.mergeSort_perm _ _

/-- Canonicalization preserves the number of indexed peaks. -/
theorem Spectrum.canonicalize_length {n : ℕ} (S : Spectrum n) :
    S.canonicalize.peaks.length = n := by
  calc
    S.canonicalize.peaks.length = S.toPeakList.length :=
      (S.canonicalize_perm).length_eq
    _ = n := by simp [Spectrum.toPeakList, List.length_ofFn]

/-- A canonical spectrum maps to the same native free-monoid carrier. -/
def CanonicalSpectrum.toSentence (S : CanonicalSpectrum) : SpectralSentence :=
  peakWord S.peaks

@[simp] theorem CanonicalSpectrum.toSentence_toList (S : CanonicalSpectrum) :
    FreeMonoid.toList S.toSentence = S.peaks := by
  simp [CanonicalSpectrum.toSentence]

/-- Indexed spectra therefore admit a certified mass-sorted free-monoid serialization. -/
def Spectrum.toSentence {n : ℕ} (S : Spectrum n) : SpectralSentence :=
  S.canonicalize.toSentence

@[simp] theorem Spectrum.toSentence_length {n : ℕ} (S : Spectrum n) :
    (FreeMonoid.toList S.toSentence).length = n := by
  rw [Spectrum.toSentence, CanonicalSpectrum.toSentence_toList,
    Spectrum.canonicalize_length]

end InfoGeometry.MassSpectrometry
