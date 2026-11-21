/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Native noncommutative spectral-triple algebra

The commutator seminorm is derived from an actual Dirac element in a normed
noncommutative algebra. No independently supplied norm field or certificate
is accepted as a substitute for the commutator.

The commutator obeys the Leibniz rule, its norm obeys the corresponding
Leibniz bound, and both maps are Lipschitz with constant `2 * ‖dirac‖₊`.
For a real normed algebra, the norm is bundled as a native Mathlib `Seminorm`.
The kernel is exactly the centralizer of the chosen Dirac element.

This bounded algebraic interface does not assert compact resolvent, construct
an unbounded Dirac operator, or establish finiteness of a spectral distance.
-/

noncomputable section

namespace ConnesSpectral

variable {A : Type*} [NormedRing A]

structure SpectralTriple (A : Type*) [NormedRing A] where
  dirac : A

/-- The zero Dirac element gives a concrete member of this bounded algebraic
interface. The estimates below hold for every chosen Dirac element. -/
instance instInhabitedSpectralTriple : Inhabited (SpectralTriple A) := ⟨⟨0⟩⟩

namespace SpectralTriple

variable (ST : SpectralTriple A)

def commutator (f : A) : A := ST.dirac * f - f * ST.dirac

def commutatorNorm (f : A) : ℝ := ‖ST.commutator f‖

theorem commutatorNorm_nonneg (f : A) :
    0 ≤ ST.commutatorNorm f :=
  norm_nonneg _

/-- The inner derivation is additive in the observable. -/
theorem commutator_add (a b : A) :
    ST.commutator (a + b) = ST.commutator a + ST.commutator b := by
  unfold commutator
  noncomm_ring

/-- The inner derivation respects differences of observables. -/
theorem commutator_sub (a b : A) :
    ST.commutator (a - b) = ST.commutator a - ST.commutator b := by
  unfold commutator
  noncomm_ring

/-- The Leibniz rule holds without commutativity of the observable algebra. -/
theorem commutator_mul (a b : A) :
    ST.commutator (a * b) = ST.commutator a * b + a * ST.commutator b := by
  unfold commutator
  noncomm_ring

/-- The commutator seminorm vanishes precisely on the centralizer of `dirac`. -/
theorem commutatorNorm_eq_zero_iff_commute (a : A) :
    ST.commutatorNorm a = 0 ↔ Commute ST.dirac a := by
  simp only [commutatorNorm, commutator, norm_eq_zero, sub_eq_zero, commute_iff_eq]

/-- The operator-norm estimate for a bounded inner derivation. -/
theorem commutatorNorm_le (a : A) :
    ST.commutatorNorm a ≤ 2 * ‖ST.dirac‖ * ‖a‖ := by
  calc
    ST.commutatorNorm a = ‖ST.dirac * a - a * ST.dirac‖ := rfl
    _ ≤ ‖ST.dirac * a‖ + ‖a * ST.dirac‖ := norm_sub_le _ _
    _ ≤ ‖ST.dirac‖ * ‖a‖ + ‖a‖ * ‖ST.dirac‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖ST.dirac‖ * ‖a‖ := by ring

/-- Subadditivity of the commutator norm. -/
theorem commutatorNorm_add_le (a b : A) :
    ST.commutatorNorm (a + b) ≤ ST.commutatorNorm a + ST.commutatorNorm b := by
  simpa only [commutatorNorm, commutator_add] using
    norm_add_le (ST.commutator a) (ST.commutator b)

/-- The Leibniz estimate inherited from the inner derivation. -/
theorem commutatorNorm_mul_le (a b : A) :
    ST.commutatorNorm (a * b) ≤
      ST.commutatorNorm a * ‖b‖ + ‖a‖ * ST.commutatorNorm b := by
  unfold commutatorNorm
  rw [commutator_mul]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

/-- The inner derivation is globally Lipschitz in the ambient norm. -/
theorem lipschitzWith_commutator :
    LipschitzWith (2 * ‖ST.dirac‖₊) ST.commutator := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa [commutatorNorm, commutator_sub, dist_eq_norm] using
    ST.commutatorNorm_le (a - b)

/-- The commutator norm is globally Lipschitz with the same bound. -/
theorem lipschitzWith_commutatorNorm :
    LipschitzWith (2 * ‖ST.dirac‖₊) ST.commutatorNorm := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  calc
    dist (ST.commutatorNorm a) (ST.commutatorNorm b)
        = dist ‖ST.commutator a‖ ‖ST.commutator b‖ := rfl
    _ ≤ ‖ST.commutator a - ST.commutator b‖ := dist_norm_norm_le _ _
    _ = dist (ST.commutator a) (ST.commutator b) := (dist_eq_norm _ _).symm
    _ ≤ ((2 * ‖ST.dirac‖₊ : NNReal) : ℝ) * dist a b :=
      ST.lipschitzWith_commutator.dist_le_mul a b

section RealAlgebra

variable [NormedAlgebra ℝ A]

/-- Real scalar compatibility of the inner derivation. -/
theorem commutator_smul (c : ℝ) (a : A) :
    ST.commutator (c • a) = c • ST.commutator a := by
  simp only [commutator, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- Absolute homogeneity of the commutator norm. -/
theorem commutatorNorm_smul (c : ℝ) (a : A) :
    ST.commutatorNorm (c • a) = ‖c‖ * ST.commutatorNorm a := by
  simp only [commutatorNorm, commutator_smul, norm_smul]

/-- The commutator norm as a native Mathlib real seminorm. -/
def commutatorSeminorm : Seminorm ℝ A :=
  Seminorm.of ST.commutatorNorm ST.commutatorNorm_add_le ST.commutatorNorm_smul

@[simp] theorem commutatorSeminorm_apply (a : A) :
    ST.commutatorSeminorm a = ST.commutatorNorm a := rfl

end RealAlgebra

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
