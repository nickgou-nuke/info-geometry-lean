import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Routing.PermutationPerfectMatching
import InfoGeometry.MassSpectrometry.FragmentationDAG
import InfoGeometry.MassSpectrometry.PeakSpectrum
import InfoGeometry.MassSpectrometry.PeakFragmentMatching
import InfoGeometry.MassSpectrometry.MellinMassEncoding

/-!
# Finite mass-spectrometry core

The carrier is deliberately finite and separates verified combinatorics from
instrument-specific interpretation.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

structure IsDoublyStochastic {n : ℕ} (A : AssignmentMatrix n) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  row_sum : ∀ i, ∑ j, A i j = 1
  col_sum : ∀ j, ∑ i, A i j = 1

theorem identity_isDoublyStochastic (n : ℕ) :
    IsDoublyStochastic (1 : AssignmentMatrix n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · intro i
    simp [Matrix.one_apply]
  · intro j
    simp [Matrix.one_apply]

end InfoGeometry.MassSpectrometry
