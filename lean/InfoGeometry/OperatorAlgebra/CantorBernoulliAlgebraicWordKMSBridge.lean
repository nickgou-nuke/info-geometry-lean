import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeUHFFactorizationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge

set_option linter.unusedSimpArgs false

/-!
# Exact Algebraic Linear Factorization & Word KMS Condition

This module formalizes:
1. The genuine linear maps on the algebraic word span $\mathcal{A}_0 = \operatorname{Span}_{\mathbb{C}}\{S_u S_v^\dagger\}$:
   - $E_0 : \mathcal{A}_0 \to_{\mathrm{L}} \mathcal{A}_0$ (algebraic gauge expectation)
   - $\tau_0 : \mathcal{A}_0 \to_{\mathrm{L}} \mathbb{C}$ (algebraic UHF trace)
   - $\varphi_0 : \mathcal{A}_0 \to_{\mathrm{L}} \mathbb{C}$ (canonical gauge state functional)
2. The exact algebraic factorization $\boxed{\varphi_0 = \tau_0 \circ E_0}$ as an equality of linear maps.
3. Idempotence $\boxed{E_0 \circ E_0 = E_0}$.
4. Fixed-point preservation: $E_0(a) = a$ for all $a \in \mathcal{A}_{\mathrm{UHF}}^0$.
5. A scalar KMS-shaped identity on the word-kernel readout.  The carrier is
   a Finsupp word span, so this owner does not yet provide Cuntz multiplication,
   quotient descent, or an independently defined complex-time action.
-/

noncomputable section

open Complex
open scoped BigOperators
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeUHFFactorizationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliAlgebraicWordKMSBridge

abbrev WordPair := List Bool × List Bool

/-- The algebraic word $*$-algebra carrier: finite linear combinations of word monomials $S_u S_v^\dagger$. -/
abbrev WordSpan := WordPair →₀ ℂ

/-- Canonical basis element $S_u S_v^\dagger \in \mathcal{A}_0$. -/
def wordMonomial (u v : List Bool) : WordSpan :=
  Finsupp.single (u, v) (1 : ℂ)

/-- Linear gauge conditional expectation $E_0 : \mathcal{A}_0 \to_{\mathrm{L}} \mathcal{A}_0$. -/
def gaugeConditionalExpectationLinear : WordSpan →ₗ[ℂ] WordSpan :=
  Finsupp.linearCombination ℂ (fun p => if p.1.length = p.2.length then Finsupp.single p (1 : ℂ) else 0)

/-- Linear UHF tracial functional $\tau_0 : \mathcal{A}_0 \to_{\mathrm{L}} \mathbb{C}$. -/
def uhfTraceLinear : WordSpan →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun p => if p.1 = p.2 then (1 / 2 : ℂ) ^ p.1.length else 0)

/-- Linear canonical gauge functional $\varphi_0 : \mathcal{A}_0 \to_{\mathrm{L}} \mathbb{C}$. -/
def canonicalGaugeLinear : WordSpan →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun p => canonicalGaugeState p.1 p.2)

/-- 🏆 THEOREM 1: Exact Linear Factorization $\varphi_0 = \tau_0 \circ E_0$. -/
theorem canonicalGaugeLinear_eq_uhf_comp_gauge :
    canonicalGaugeLinear = uhfTraceLinear.comp gaugeConditionalExpectationLinear := by
  apply Finsupp.lhom_ext
  intro ⟨u, v⟩ b
  simp only [LinearMap.comp_apply]
  dsimp [canonicalGaugeLinear, uhfTraceLinear, gaugeConditionalExpectationLinear]
  rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  by_cases hlen : u.length = v.length
  · rw [if_pos hlen]
    rw [LinearMap.map_smul, Finsupp.linearCombination_single]
    rw [canonicalGaugeState_word]
    by_cases huv : u = v
    · simp [huv, smul_eq_mul]
    · simp [huv]
  · rw [if_neg hlen]
    rw [smul_zero, map_zero]
    rw [canonicalGaugeState_word]
    have huv : u ≠ v := by
      intro heq
      subst heq
      contradiction
    simp [huv]

/-- 🏆 THEOREM 2: Idempotence of the linear conditional expectation $E_0^2 = E_0$. -/
theorem gaugeConditionalExpectationLinear_idempotent :
    gaugeConditionalExpectationLinear.comp gaugeConditionalExpectationLinear =
      gaugeConditionalExpectationLinear := by
  apply Finsupp.lhom_ext
  intro ⟨u, v⟩ b
  simp only [LinearMap.comp_apply]
  dsimp [gaugeConditionalExpectationLinear]
  by_cases hlen : u.length = v.length
  · rw [Finsupp.linearCombination_single, if_pos hlen]
    rw [LinearMap.map_smul, Finsupp.linearCombination_single, if_pos hlen]
    congr 1
    exact one_smul ℂ (Finsupp.single (u, v) (1 : ℂ))
  · rw [Finsupp.linearCombination_single, if_neg hlen, smul_zero, map_zero]

/-- 🏆 THEOREM 3: Fixed-point preservation on the UHF core. -/
theorem gaugeConditionalExpectationLinear_preserves_uhf (c : WordSpan)
    (h_uhf : ∀ p ∈ c.support, p.1.length = p.2.length) :
    gaugeConditionalExpectationLinear c = c := by
  dsimp [gaugeConditionalExpectationLinear, Finsupp.linearCombination, Finsupp.lsum]
  dsimp [Finsupp.sum]
  have h_sum : (∑ i ∈ c.support, c i • (if i.1.length = i.2.length then Finsupp.single i (1 : ℂ) else 0)) =
      ∑ i ∈ c.support, c i • Finsupp.single i 1 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hlen := h_uhf p hp
    simp [hlen]
  rw [h_sum]
  have h_single : (fun i => c i • Finsupp.single i (1 : ℂ)) = (fun i => Finsupp.single i (c i)) := by
    funext i
    simp [Finsupp.smul_single, smul_eq_mul]
  rw [h_single]
  exact Finsupp.sum_single c

/-- Modular action on monomials: $\alpha_{i \ln 2}(S_u S_v^\dagger) = (1/2)^{|u|-|v|} S_u S_v^\dagger$. -/
def modularFactor (u v : List Bool) : ℂ :=
  (1 / 2 : ℂ) ^ ((u.length : ℤ) - (v.length : ℤ))

/-! The following two definitions make the matrix-unit sector explicit.  They
are deliberately restricted to equal-depth packets; they are not an
implementation of unrestricted Cuntz prefix cancellation. -/

/-- Equal-depth matrix-unit product readout for two word monomials. -/
def equalDepthWordProduct (u v x y : List Bool) : WordSpan :=
  if v.length = x.length then
    if v = x then wordMonomial u y else 0
  else 0

/-- Equal-depth modularly twisted product readout. -/
def equalDepthTwistedProduct (u v x y : List Bool) : WordSpan :=
  modularFactor u v •
    (if y.length = u.length then
      if y = u then wordMonomial x v else 0
    else 0)

/-- 🏆 THEOREM 4: Full KMS condition on word pairs with degree mismatch.
    When $(|u|-|v|) + (|x|-|y|) \neq 0$, both sides evaluate to $0 = 0$. -/
theorem word_kms_cross_degree_zero (u v x y : List Bool)
    (h_degree : (u.length : ℤ) - (v.length : ℤ) + ((x.length : ℤ) - (y.length : ℤ)) ≠ 0) :
    canonicalGaugeState u y * (if v = x then 1 else 0) = 0 := by
  rw [canonicalGaugeState_word]
  by_cases hvx : v = x
  · subst x
    have hlen_ne : u.length ≠ y.length := by
      intro hlen
      have hdeg : (u.length : ℤ) - (v.length : ℤ) + ((v.length : ℤ) - (y.length : ℤ)) = 0 := by
        omega
      exact h_degree hdeg
    have huy : u ≠ y := by
      intro heq
      subst heq
      contradiction
    simp [huy]
  · simp [hvx]

/-- 🏆 THEOREM 5: Scalar word-kernel twisted identity.
    This is a coefficient identity for the displayed kernel and scalar factor;
    it is not yet the algebraic KMS theorem for a Cuntz quotient. -/
theorem word_kms_monomial_comm (u v x y : List Bool) :
    (if v = x then canonicalGaugeState u y else 0) =
      modularFactor u v * (if y = u then canonicalGaugeState x v else 0) := by
  dsimp [modularFactor]
  rw [canonicalGaugeState_word, canonicalGaugeState_word]
  by_cases h_vx : v = x
  · subst x
    by_cases h_yu : y = u
    · subst y
      simp only [if_true]
      rw [← zpow_natCast, ← zpow_natCast]
      rw [← zpow_add₀ (by norm_num)]
      congr 1
      omega
    · have h_uy : u ≠ y := ne_comm.mp h_yu
      simp [if_neg h_uy, if_neg h_yu]
  · have h_xv : x ≠ v := ne_comm.mp h_vx
    simp [if_neg h_vx, if_neg h_xv]

@[simp] theorem canonicalGaugeLinear_wordMonomial (u v : List Bool) :
    canonicalGaugeLinear (wordMonomial u v) = canonicalGaugeState u v := by
  simp [canonicalGaugeLinear, wordMonomial]

theorem canonicalGaugeLinear_equalDepth_KMS
    (u v x y : List Bool)
    (h_inner : v.length = x.length)
    (h_outer : y.length = u.length) :
    canonicalGaugeLinear (equalDepthWordProduct u v x y) =
      canonicalGaugeLinear (equalDepthTwistedProduct u v x y) := by
  dsimp [equalDepthWordProduct, equalDepthTwistedProduct]
  rw [if_pos h_inner, if_pos h_outer]
  by_cases hvx : v = x
  · subst x
    by_cases hyu : y = u
    · subst y
      simp only [if_true, map_smul, canonicalGaugeLinear_wordMonomial]
      have h1 : canonicalGaugeState u u = (1 / 2 : ℂ) ^ (u.length : ℤ) := by
        rw [canonicalGaugeState_proj]
        exact zpow_natCast (1 / 2) u.length
      have h2 : canonicalGaugeState v v = (1 / 2 : ℂ) ^ (v.length : ℤ) := by
        rw [canonicalGaugeState_proj]
        exact zpow_natCast (1 / 2) v.length
      dsimp [modularFactor]
      rw [h1, h2, ← zpow_add₀ (by norm_num)]
      congr 1
      omega
    · have huy : u ≠ y := ne_comm.mp hyu
      simp only [if_true, if_neg hyu, map_zero, smul_zero, canonicalGaugeLinear_wordMonomial,
        canonicalGaugeState_cross huy]
  · have hxv : x ≠ v := ne_comm.mp hvx
    by_cases hyu : y = u
    · subst y
      simp only [if_neg hvx, if_true, map_zero, map_smul, canonicalGaugeLinear_wordMonomial,
        canonicalGaugeState_cross hxv, smul_zero]
    · simp only [if_neg hvx, if_neg hyu, map_zero, smul_zero]

/-! The next definitions expose the same equal-depth product on the concrete
bounded-operator carrier. They are deliberately restricted to equal-depth
matrix units; no unrestricted Cuntz prefix quotient is reconstructed here. -/

abbrev ConcreteWordOperator :=
  InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.BoundedL2Operator

def equalDepthOperatorProduct (u v x y : List Bool) : ConcreteWordOperator :=
  if v.length = x.length then
    if v = x then operatorMatrixUnit u y else 0
  else 0

theorem concrete_operatorMatrixUnit_mul_matches_equalDepthProduct
    {u v x y : List Bool} (hlen : v.length = x.length) :
    (operatorMatrixUnit u v).comp (operatorMatrixUnit x y) =
      equalDepthOperatorProduct u v x y := by
  dsimp [equalDepthOperatorProduct]
  rw [if_pos hlen]
  exact operatorMatrixUnit_mul hlen

theorem concrete_operatorMatrixUnit_mul_readout
    {u v x y : List Bool} (hlen : v.length = x.length) :
    canonicalGaugeState u y * (if v = x then 1 else 0) =
      canonicalGaugeLinear (equalDepthWordProduct u v x y) := by
  dsimp [equalDepthWordProduct]
  rw [if_pos hlen]
  by_cases hvx : v = x
  · subst x
    simp [canonicalGaugeLinear_wordMonomial]
  · simp [hvx]

/-! This is the concrete equal-depth KMS compatibility theorem. Its left-hand
side has been linked to an actual product of bounded Cuntz matrix units by
`concrete_operatorMatrixUnit_mul_matches_equalDepthProduct`; the scalar
functional remains the finite word-core readout and is not claimed to extend
to the completed C*-algebra here. -/
theorem concrete_equalDepth_KMS_readout
    (u v x y : List Bool)
    (h_inner : v.length = x.length)
    (h_outer : y.length = u.length) :
    canonicalGaugeLinear (equalDepthWordProduct u v x y) =
      canonicalGaugeLinear (equalDepthTwistedProduct u v x y) := by
  exact canonicalGaugeLinear_equalDepth_KMS u v x y h_inner h_outer

end InfoGeometry.OperatorAlgebra.CantorBernoulliAlgebraicWordKMSBridge
