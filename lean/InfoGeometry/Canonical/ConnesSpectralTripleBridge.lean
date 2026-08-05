import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Tactic.Linarith

/-!
# Native noncommutative spectral-triple algebra

The commutator seminorm is derived from an actual Dirac element in a normed
noncommutative algebra.  No independently supplied norm field or certificate
is accepted as a substitute for the commutator.
-/

noncomputable section

namespace ConnesSpectral

variable {A : Type*} [NormedRing A]

abbrev SpectralTriple (A : Type*) [NormedRing A] := A

namespace SpectralTriple

variable (ST : SpectralTriple A)

/-- Compatibility accessor for the native Dirac-element carrier. -/
abbrev dirac : A := ST

def commutator (f : A) : A := ST.dirac * f - f * ST.dirac

def commutatorNorm (f : A) : ℝ := ‖ST.commutator f‖

theorem commutatorNorm_nonneg (f : A) :
    0 ≤ ST.commutatorNorm f :=
  norm_nonneg _

def LipschitzFunction (f : A) : Prop :=
  ST.commutatorNorm f ≤ 1

abbrev StateDistanceBound (p q : A → ℝ) (d : ℝ) : Prop :=
  (∀ f : A, ST.LipschitzFunction f → |p f - q f| ≤ d) ∧ 0 ≤ d

theorem distance_bound_symmetry (p q : A → ℝ) (d : ℝ)
    (h : ST.StateDistanceBound p q d) :
    ST.StateDistanceBound q p d := by
  refine ⟨fun f hf => ?_, h.2⟩
  simpa [abs_sub_comm] using h.1 f hf

theorem distance_bound_triangle (p q r : A → ℝ) (d1 d2 : ℝ)
    (h1 : ST.StateDistanceBound p q d1)
    (h2 : ST.StateDistanceBound q r d2) :
    ST.StateDistanceBound p r (d1 + d2) := by
  refine ⟨fun f hf => ?_, by linarith [h1.2, h2.2]⟩
  have htri := abs_sub_le (p f) (q f) (r f)
  linarith [h1.1 f hf, h2.1 f hf]

end SpectralTriple

end ConnesSpectral
