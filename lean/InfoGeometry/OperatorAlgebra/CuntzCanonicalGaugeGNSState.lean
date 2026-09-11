import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliKMSState
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Algebra.CuntzGNSRepresentation

/-!
# Canonical Gauge-Word Kernel and Pre-GNS Quadratic Form Packet

This owner records the canonical gauge-invariant **word kernel**
$\varphi(S_\mu S_\nu^\dagger) = \delta_{\mu\nu} 2^{-|\mu|}$, its
finite-support positive quadratic-form packet, and its algebraic pre-GNS
readouts. It does not yet construct a positive linear map on the completed
concrete C*-algebra, a quotient Hilbert space, or a Tomita--Takesaki modular
datum. Those completion obligations remain downstream of this finite word
kernel.

It also records the distinction between the spatial Bernoulli vector
functional and the gauge-word kernel, together with an algebraic witness
candidate for the non-separating property of the spatial vector.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState

open Complex
open ContinuousLinearMap
open scoped BigOperators
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzGNSRepresentation
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSState

abbrev BoundedL2Operator := InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.BoundedL2Operator

/-- The canonical gauge-invariant word-kernel value on binary words. -/
def gaugeStateWord (u v : List Bool) : ℂ :=
  if u = v then (1 / 2 : ℂ) ^ u.length else 0

/-- φ(1) = 1 on the identity word. -/
@[simp] theorem gaugeStateWord_nil :
    gaugeStateWord [] [] = 1 := by
  dsimp [gaugeStateWord]
  simp

/-- φ(S_b S_b†) = 1/2 for single bit words. -/
theorem gaugeStateWord_single_diag (b : Bool) :
    gaugeStateWord [b] [b] = 1 / 2 := by
  dsimp [gaugeStateWord]
  simp

/-- φ(S_false S_true†) = 0 (cross terms vanish). -/
theorem gaugeStateWord_single_cross :
    gaugeStateWord [false] [true] = 0 := by
  dsimp [gaugeStateWord]

/-- Basic numerical nonvanishing fact: 1/2 ≠ 0 in ℂ. -/
theorem half_ne_zero_complex :
    (1 / 2 : ℂ) ≠ 0 := by
  norm_num

/-- Core inequivalence readout: the off-diagonal coefficient 1/2 is nonzero,
    while the gauge word kernel assigns the cross word zero. -/
theorem gaugeStateWord_cross_ne_half :
    gaugeStateWord [false] [true] ≠ (1 / 2 : ℂ) := by
  rw [gaugeStateWord_single_cross]
  norm_num

/-- Candidate non-separating witness operator. Its annihilation of the
    constant Bernoulli vector is a separate Hilbert-level theorem. -/
def spatialAnnihilator : BoundedL2Operator :=
  (star (cantorL2CuntzFamily.S false)) - (star (cantorL2CuntzFamily.S true))

/-- The candidate pre-inner-product kernel on binary words used by later GNS constructions. -/
def gnsWordInner (u v : List Bool) : ℂ :=
  gaugeStateWord u v

/-! The following finite-support form is the exact positive kernel packet that
precedes, but does not replace, a positive functional on the completed
operator algebra. -/

def gaugeKernelQuadratic (c : List Bool →₀ ℂ) : ℂ :=
  ∑ u ∈ c.support, ∑ v ∈ c.support,
    star (c u) * gaugeStateWord u v * c v

theorem gaugeKernelQuadratic_eq_diag_sum (c : List Bool →₀ ℂ) :
    gaugeKernelQuadratic c =
      ∑ u ∈ c.support,
        star (c u) * ((1 / 2 : ℂ) ^ u.length) * c u := by
  classical
  unfold gaugeKernelQuadratic
  apply Finset.sum_congr rfl
  intro u hu
  have hcu : c u ≠ 0 := Finsupp.mem_support_iff.mp hu
  simp [gaugeStateWord, hcu]

theorem gaugeKernelQuadratic_eq_normSq_sum (c : List Bool →₀ ℂ) :
    gaugeKernelQuadratic c =
      ∑ u ∈ c.support,
        (((1 / 2 : ℝ) ^ u.length) * Complex.normSq (c u) : ℂ) := by
  rw [gaugeKernelQuadratic_eq_diag_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  push_cast
  ring

theorem gaugeKernelQuadratic_eq_ofReal_normSq_sum (c : List Bool →₀ ℂ) :
    gaugeKernelQuadratic c =
      ((∑ u ∈ c.support,
        (1 / 2 : ℝ) ^ u.length * Complex.normSq (c u) : ℝ) : ℂ) := by
  rw [gaugeKernelQuadratic_eq_normSq_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro u hu
  push_cast
  ring

/-- 🏆 THEOREM: Nonnegativity of the real part of the gauge quadratic form. -/
theorem gaugeKernelQuadratic_real_nonneg (c : List Bool →₀ ℂ) :
    0 ≤ (gaugeKernelQuadratic c).re := by
  rw [gaugeKernelQuadratic_eq_ofReal_normSq_sum]
  simp only [Complex.ofReal_re]
  apply Finset.sum_nonneg
  intro u _
  exact mul_nonneg (pow_nonneg (by norm_num) _) (Complex.normSq_nonneg _)

/-- 🏆 THEOREM: Imaginary part of the gauge quadratic form vanishes identically. -/
theorem gaugeKernelQuadratic_im_zero (c : List Bool →₀ ℂ) :
    (gaugeKernelQuadratic c).im = 0 := by
  rw [gaugeKernelQuadratic_eq_ofReal_normSq_sum]
  exact Complex.ofReal_im _

/-- 🏆 THEOREM: Strict positive definiteness / faithfulness of the gauge word quadratic form. -/
theorem gaugeKernelQuadratic_re_eq_zero_iff (c : List Bool →₀ ℂ) :
    (gaugeKernelQuadratic c).re = 0 ↔ c = 0 := by
  constructor
  · intro hzero
    rw [gaugeKernelQuadratic_eq_ofReal_normSq_sum, Complex.ofReal_re] at hzero
    have h_nonneg : ∀ u ∈ c.support, 0 ≤ (1 / 2 : ℝ) ^ u.length * Complex.normSq (c u) := by
      intro u _
      exact mul_nonneg (pow_nonneg (by norm_num) _) (Complex.normSq_nonneg _)
    have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp hzero
    ext u
    by_cases hu : u ∈ c.support
    · have hu_zero := h_all_zero u hu
      have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ u.length := by positivity
      have h_normSq_zero : Complex.normSq (c u) = 0 := by
        nlinarith
      exact Complex.normSq_eq_zero.mp h_normSq_zero
    · have hcu := Finsupp.mem_support_iff.not.mp hu
      exact not_not.mp hcu
  · intro hc
    subst hc
    simp [gaugeKernelQuadratic]

/-- 🏆 THEOREM: Strict positivity for non-zero finite coefficient packets. -/
theorem gaugeKernelQuadratic_pos_of_ne_zero {c : List Bool →₀ ℂ} (hc : c ≠ 0) :
    0 < (gaugeKernelQuadratic c).re := by
  have hnonneg := gaugeKernelQuadratic_real_nonneg c
  have hne : (gaugeKernelQuadratic c).re ≠ 0 := by
    intro hzero
    exact hc ((gaugeKernelQuadratic_re_eq_zero_iff c).mp hzero)
  exact lt_of_le_of_ne hnonneg hne.symm

/-- Word-kernel readouts with distinct lengths vanish. -/
theorem gnsWordInner_orthogonal_of_ne_length {u v : List Bool} (h : u.length ≠ v.length) :
    gnsWordInner u v = 0 := by
  dsimp [gnsWordInner, gaugeStateWord]
  split_ifs with heq
  · subst heq
    contradiction
  · rfl

/-- The diagonal word-kernel value decays exponentially: 2^{-|w|}. -/
theorem gnsWordInner_self (w : List Bool) :
    gnsWordInner w w = (1 / 2 : ℂ) ^ w.length := by
  dsimp [gnsWordInner, gaugeStateWord]
  simp

/-- Partition of unity on GNS word projections at length 1. -/
theorem gnsWord_length_one_partition :
    gnsWordInner [false] [false] + gnsWordInner [true] [true] = 1 := by
  rw [gnsWordInner_self, gnsWordInner_self]
  dsimp [List.length]
  ring

end InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState
