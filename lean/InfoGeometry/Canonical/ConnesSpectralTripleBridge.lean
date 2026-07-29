import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real

namespace ConnesSpectral

/-- A Non-Commutative Spectral Triple (A, H, D) with bounded commutator norm condition. -/
structure SpectralTriple (A : Type*) where
  commutatorNorm : A → ℝ        -- ||[D, a]|| operator norm of the Dirac commutator
  norm_nonneg : ∀ a, 0 ≤ commutatorNorm a

namespace SpectralTriple

variable {A : Type*} (ST : SpectralTriple A)

/-- Lipschitz ball of non-commutative functions with ||[D, f]|| ≤ 1. -/
def LipschitzFunction (f : A) : Prop :=
  ST.commutatorNorm f ≤ 1

/-- Connes Spectral Distance Supremum Bound: |p(f) - q(f)| ≤ d for all Lip(f) ≤ 1. -/
abbrev StateDistanceBound (p q : A → ℝ) (d : ℝ) : Prop :=
  (∀ f : A, ST.LipschitzFunction f → |p f - q f| ≤ d) ∧ 0 ≤ d

/-- **Theorem**: Connes Spectral Distance Symmetry: |p(f) - q(f)| = |q(f) - p(f)|. -/
theorem distance_bound_symmetry (p q : A → ℝ) (d : ℝ) (h : ST.StateDistanceBound p q d) :
    ST.StateDistanceBound q p d := by
  refine ⟨?_, h.2⟩
  intro f hf
  rw [abs_sub_comm]
  exact h.1 f hf

/-- **Theorem**: Connes Spectral Distance Triangle Inequality:
    If d(p, q) ≤ d1 and d(q, r) ≤ d2, then d(p, r) ≤ d1 + d2. -/
theorem distance_bound_triangle (p q r : A → ℝ) (d1 d2 : ℝ)
    (h1 : ST.StateDistanceBound p q d1)
    (h2 : ST.StateDistanceBound q r d2) :
    ST.StateDistanceBound p r (d1 + d2) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    have h_tri := abs_sub_le (p f) (q f) (r f)
    have h_p := h1.1 f hf
    have h_q := h2.1 f hf
    linarith
  · linarith [h1.2, h2.2]

end SpectralTriple

end ConnesSpectral
