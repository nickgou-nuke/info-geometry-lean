import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannHypothesisProjectiveFormulation

open Complex
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/--
A Riemann-zeta zero in the open critical strip.

This definition selects exactly the zero locus relevant to the projective
critical-line formulation below; no RH assertion is built into it.
-/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- The nontrivial zero locus in the open critical strip. -/
def nontrivialZeroSet : Set ℂ :=
  {s | IsNontrivialZero s}

/--
Critical-line formulation of RH on the selected nontrivial zero locus.
-/
def RiemannHypothesisCriticalLine : Prop :=
  ∀ s ∈ nontrivialZeroSet, OnCriticalLine s

/--
Projective/Cayley formulation: every selected zeta zero is sent to the
distinguished unit circle.
-/
def RiemannHypothesisProjectiveCircle : Prop :=
  ∀ s ∈ nontrivialZeroSet,
    OnLeeYangCircle (cayleyToFugacity s)

/-! The set-theoretic forms below are the native `Set.image` and predicate
formulations of the same Cayley equivalence. -/

def cayleyImage (A : Set ℂ) : Set ℂ :=
  cayleyToFugacity '' A

def unitCircleSet : Set ℂ :=
  {z | OnLeeYangCircle z}

theorem subset_cayley_unitCircle_iff_subset_criticalLine (A : Set ℂ) :
    (A ⊆ {s | OnCriticalLine s}) ↔
      (cayleyImage A ⊆ {z | OnLeeYangCircle z}) := by
  constructor
  · intro h z hz
    rcases hz with ⟨s, hs, rfl⟩
    exact cayleyToFugacity_mem_unitCircle_of_criticalLine s (h hs)
  · intro h s hs
    exact (criticalLine_iff_cayley_unitCircle s).mpr (h ⟨s, hs, rfl⟩)

theorem cayleyImage_subset_unitCircle_iff (A : Set ℂ) :
    cayleyImage A ⊆ {z | OnLeeYangCircle z} ↔
      A ⊆ {s | OnCriticalLine s} := by
  exact (subset_cayley_unitCircle_iff_subset_criticalLine A).symm

theorem cayleyImage_subset_unitCircleSet_iff (A : Set ℂ) :
    cayleyImage A ⊆ unitCircleSet ↔
      A ⊆ {s | OnCriticalLine s} := by
  exact cayleyImage_subset_unitCircle_iff A

/--
The critical-line and projective-circle formulations are exactly equivalent.

This theorem is purely the Cayley/Möbius reformulation of the zero locus.
It does not prove that either equivalent proposition holds.
-/
theorem riemannHypothesisCriticalLine_iff_projectiveCircle :
    RiemannHypothesisCriticalLine ↔
      RiemannHypothesisProjectiveCircle := by
  simpa [RiemannHypothesisCriticalLine, RiemannHypothesisProjectiveCircle] using
    (subset_cayley_unitCircle_iff_subset_criticalLine nontrivialZeroSet).symm

/--
The image of the nontrivial zero locus under the Cayley coordinate chart.
-/
def cayleyNontrivialZeroSet : Set ℂ :=
  cayleyImage nontrivialZeroSet

/--
Exact set-theoretic formulation of the projective geometry.
RH holds if and only if the entire Cayley image of the nontrivial zero locus
is contained within the Lee-Yang invariant circle.
-/
theorem riemannHypothesisCriticalLine_iff_cayleyImageSubset :
    RiemannHypothesisCriticalLine ↔
      cayleyNontrivialZeroSet ⊆ { z | OnLeeYangCircle z } := by
  exact
    (cayleyImage_subset_unitCircle_iff nontrivialZeroSet).symm

theorem riemannHypothesisCriticalLine_iff_cayleyZeroImage_subset_unitCircle :
    RiemannHypothesisCriticalLine ↔
      cayleyNontrivialZeroSet ⊆ unitCircleSet := by
  exact
    (cayleyImage_subset_unitCircleSet_iff nontrivialZeroSet).symm

end InfoGeometry.Arithmetic.RiemannHypothesisProjectiveFormulation
