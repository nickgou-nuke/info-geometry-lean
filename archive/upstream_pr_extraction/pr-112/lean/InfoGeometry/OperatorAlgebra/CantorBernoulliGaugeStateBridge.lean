import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState
import InfoGeometry.Algebra.CuntzNativeGNSBridge
import InfoGeometry.Algebra.CuntzKMSCondition

/-!
# Cantor-Bernoulli Canonical Gauge-Word Kernel Bridge

This file formalizes the finite word-kernel portion of Step 4.  It does not
yet construct a state on the completed concrete Cuntz algebra
$A_C \subset \mathcal{B}(L^2(\mathcal{C}, \mu_C))$.  It records the exact
candidate word formula:
$$\varphi(S_\mu S_\nu^\dagger) = \delta_{\mu\nu} 2^{-|\mu|}.$$

The finite-support quadratic form is proved positive and faithful on its
word-packet carrier.  Positivity/boundedness extension to $A_C$, a concrete
GNS state, and Tomita--Takesaki data remain separate obligations.

## Key verified finite theorems:
1. `canonicalGaugeState_word`: the exact word-kernel formula.
2. `canonicalGaugeState_gaugeInvariant`: phase invariance of the word kernel.
3. `canonicalGaugeState_faithful_core`: faithfulness on finite word packets.
-/

noncomputable section

open Complex
open scoped BigOperators Topology
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-- The canonical gauge state value on word pairs $(u, v) \in \text{List Bool} \times \text{List Bool}$. -/
def canonicalGaugeState (u v : List Bool) : ℂ :=
  gaugeStateWord u v

/-- $\varphi(1) = \varphi(S_\emptyset S_\emptyset^\dagger) = 1$. -/
@[simp] theorem canonicalGaugeState_one :
    canonicalGaugeState [] [] = 1 :=
  gaugeStateWord_nil

/-- The fundamental word formula: $\varphi(S_u S_v^\dagger) = \delta_{uv} 2^{-|u|}$. -/
theorem canonicalGaugeState_word (u v : List Bool) :
    canonicalGaugeState u v = if u = v then (1 / 2 : ℂ) ^ u.length else 0 :=
  rfl

/-- Word projector values: $\varphi(P_w) = 2^{-|w|}$. -/
theorem canonicalGaugeState_proj (w : List Bool) :
    canonicalGaugeState w w = (1 / 2 : ℂ) ^ w.length := by
  rw [canonicalGaugeState_word]
  simp

/-- Single bit projector values: $\varphi(P_b) = 1/2$. -/
theorem canonicalGaugeState_single_proj (b : Bool) :
    canonicalGaugeState [b] [b] = 1 / 2 :=
  gaugeStateWord_single_diag b

/-- Off-diagonal word cross terms vanish: $\varphi(S_u S_v^\dagger) = 0$ for $u \neq v$. -/
theorem canonicalGaugeState_cross {u v : List Bool} (h : u ≠ v) :
    canonicalGaugeState u v = 0 := by
  rw [canonicalGaugeState_word, if_neg h]

/-!
### 1. Gauge Invariance under U(1) / Real Phase Rotations
-/

/-- Gauge rotation of a word pair by phase angle $\theta \in \mathbb{R}$:
$S_u \mapsto e^{i |u| \theta} S_u$, $S_v^\dagger \mapsto e^{-i |v| \theta} S_v^\dagger$. -/
def gaugeRotateWord (θ : ℝ) (u v : List Bool) : ℂ :=
  Complex.exp (I * ((u.length : ℂ) - (v.length : ℂ)) * (θ : ℂ)) * canonicalGaugeState u v

/-- The canonical state is strictly invariant under $U(1)$ gauge rotations. -/
theorem canonicalGaugeState_gaugeInvariant (θ : ℝ) (u v : List Bool) :
    gaugeRotateWord θ u v = canonicalGaugeState u v := by
  dsimp [gaugeRotateWord]
  by_cases heq : u = v
  · subst heq
    simp
  · rw [canonicalGaugeState_cross heq, mul_zero]

/-!
### 2. Positivity on finite word coefficient packets
-/

/-- The quadratic expectation on a finite word packet $c : \text{List Bool} \to_0 \mathbb{C}$. -/
def wordPacketQuadratic (c : List Bool →₀ ℂ) : ℂ :=
  gaugeKernelQuadratic c

theorem wordPacketQuadratic_eq_ofReal_sum (c : List Bool →₀ ℂ) :
    wordPacketQuadratic c =
      ((∑ u ∈ c.support, (1 / 2 : ℝ) ^ u.length * Complex.normSq (c u) : ℝ) : ℂ) :=
  gaugeKernelQuadratic_eq_ofReal_normSq_sum c

/-- Strict positivity on finite word coefficient packets.  This is not yet
    faithfulness of a `PositiveLinearMap` on the completed `CantorCStar`. -/
theorem canonicalGaugeState_faithful_core (c : List Bool →₀ ℂ)
    (h_zero : (wordPacketQuadratic c).re = 0) :
    c = 0 := by
  rw [wordPacketQuadratic_eq_ofReal_sum] at h_zero
  simp only [Complex.ofReal_re] at h_zero
  have h_terms_zero : ∀ u ∈ c.support, (1 / 2 : ℝ) ^ u.length * Complex.normSq (c u) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg _).mp h_zero
    intro u _
    have hpow : 0 ≤ (1 / 2 : ℝ) ^ u.length := pow_nonneg (by norm_num) _
    have hnorm : 0 ≤ Complex.normSq (c u) := Complex.normSq_nonneg (c u)
    exact mul_nonneg hpow hnorm
  ext u
  by_cases hu : u ∈ c.support
  · have h_u := h_terms_zero u hu
    have hpow_pos : (1 / 2 : ℝ) ^ u.length ≠ 0 := ne_of_gt (pow_pos (by norm_num) _)
    have hnorm_zero : Complex.normSq (c u) = 0 := by
      cases mul_eq_zero.mp h_u with
      | inl h1 => contradiction
      | inr h2 => exact h2
    simp [Complex.normSq_eq_zero.mp hnorm_zero]
  · rw [Finsupp.mem_support_iff, not_not] at hu
    exact hu

/-- Generator-level Boltzmann relation. -/
theorem canonicalGaugeState_generator_boltzmann (b : Bool) :
    canonicalGaugeState [b] [b] =
      (1 / 2 : ℂ) * canonicalGaugeState [] [] := by
  rw [canonicalGaugeState_single_proj, canonicalGaugeState_one, mul_one]

/-!
### 3. Equal-depth scalar KMS readout (not an algebraic KMS theorem)
-/

/-- The modular scaling factor at imaginary time z = i on word monomials:
    $\sigma_i(S_u S_v^\dagger) = 2^{|v| - |u|} S_u S_v^\dagger$. -/
def modularScalingFactorImag (u v : List Bool) : ℂ :=
  (1 / 2 : ℂ) ^ u.length * (2 : ℂ) ^ v.length

/-- Product evaluation $\varphi(ab)$ for word monomials $a = S_u S_v^\dagger, b = S_x S_y^\dagger$
    under equal inner lengths $|v| = |x|$. -/
def wordPairExpectation (u v x y : List Bool) : ℂ :=
  if v = x then canonicalGaugeState u y else 0

/-- Modular KMS twisted product evaluation $\varphi(b \sigma_i(a))$:
    $\varphi(S_x S_y^\dagger \sigma_i(S_u S_v^\dagger)) = 2^{|v|-|u|} \delta_{yu} \varphi(S_x S_v^\dagger)$. -/
def wordPairTwistedExpectation (u v x y : List Bool) : ℂ :=
  modularScalingFactorImag u v * (if y = u then canonicalGaugeState x v else 0)

/-- 🏆 THEOREM: Generic scalar twisted identity for word readouts.
    This compares the two displayed scalar expressions.  It does not identify
    them with a product in a Cuntz quotient or with an independently defined
    complex-time dynamics. -/
theorem wordPair_scalar_twisted_identity
    (u v x y : List Bool) :
    wordPairExpectation u v x y = wordPairTwistedExpectation u v x y := by
  dsimp [wordPairExpectation, wordPairTwistedExpectation, modularScalingFactorImag]
  rw [canonicalGaugeState_word, canonicalGaugeState_word]
  by_cases h_vx : v = x
  · subst h_vx
    by_cases h_uy : u = y
    · subst h_uy
      simp only [if_true]
      have hpow : (2 : ℂ) ^ v.length * (1 / 2 : ℂ) ^ v.length = 1 := by
        rw [← mul_pow]
        have : (2 : ℂ) * (1 / 2 : ℂ) = 1 := by ring
        rw [this, one_pow]
      calc
        (1 / 2 : ℂ) ^ u.length = (1 / 2 : ℂ) ^ u.length * 1 := by ring
        _ = (1 / 2 : ℂ) ^ u.length * ((2 : ℂ) ^ v.length * (1 / 2 : ℂ) ^ v.length) := by rw [hpow]
        _ = (1 / 2 : ℂ) ^ u.length * (2 : ℂ) ^ v.length * (1 / 2 : ℂ) ^ v.length := by ring
    · have h_yu : y ≠ u := ne_comm.mp h_uy
      simp [if_neg h_uy, if_neg h_yu]
  · have h_xv : x ≠ v := ne_comm.mp h_vx
    simp [if_neg h_vx, if_neg h_xv]

/-- Equal-depth compatibility wrapper for the scalar identity.
    The length hypotheses record the intended matrix-unit sector; the scalar
    proof itself is independent of them.  This is not an algebraic KMS
    theorem without separate product and dynamics bridge lemmas. -/
theorem wordPairExpectation_eq_twisted
    (u v x y : List Bool)
    (_h_inner : v.length = x.length)
    (_h_outer : y.length = u.length) :
    wordPairExpectation u v x y = wordPairTwistedExpectation u v x y := by
  exact wordPair_scalar_twisted_identity u v x y

end InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
