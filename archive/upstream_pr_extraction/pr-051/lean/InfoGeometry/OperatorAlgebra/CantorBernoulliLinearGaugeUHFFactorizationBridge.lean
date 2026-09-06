import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeUHFFactorizationBridge
import InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge
import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState

/-!
# Linear-Map Factorization of the Canonical Gauge Functional

This module formalizes the exact structural factorization of the canonical gauge
linear functional $\varphi_0$ on the algebraic word $*$-core $\mathcal{A}_{\mathrm{word}}$
into the $\mathbb{C}$-linear gauge conditional expectation $E_0$ and the $\mathbb{C}$-linear
UHF trace functional $\tau_0$:

$$\boxed{\varphi_0 = \tau_0 \circ E_0 : \mathcal{A}_{\mathrm{word}} \to_{\mathbb{C}} \mathbb{C}}$$

Key Theorems:
1. `phi0_monomial`: $\varphi_0(S_u S_v^\dagger) = \delta_{uv} 2^{-|u|}$.
2. `E0_monomial`: $E_0(S_u S_v^\dagger) = \begin{cases} S_u S_v^\dagger, & |u| = |v| \\ 0, & |u| \neq |v| \end{cases}$.
3. `tau0_monomial`: $\tau_0(S_u S_v^\dagger) = \delta_{uv} 2^{-|u|}$.
4. `phi0_eq_tau0_comp_E0`: $\varphi_0 = \tau_0 \circ E_0$ as an identity of $\mathbb{C}$-linear maps.
5. `E0_idempotent`: $E_0 \circ E_0 = E_0$.
6. `phi0_star_monomial`: $\varphi_0((S_u S_v^\dagger)^*) = \overline{\varphi_0(S_u S_v^\dagger)}$.
7. `E0_star_monomial`: $E_0$ commutes with monomial adjoints.
-/

noncomputable section

open Complex
open scoped ComplexOrder
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeUHFFactorizationBridge
open InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge

/-- The algebraic word $*$-core $\mathcal{A}_{\mathrm{word}} = \operatorname{span}_{\mathbb{C}} \{S_u S_v^\dagger\}$.
    Represented as finitely supported functions on pairs of binary words $(u, v)$. -/
abbrev WordCore := (List Bool × List Bool) →₀ ℂ

/-- Single monomial generator $S_u S_v^\dagger$. -/
def wordMonomial (u v : List Bool) : WordCore :=
  Finsupp.single (u, v) (1 : ℂ)

/-- The canonical gauge linear functional $\varphi_0 : \mathcal{A}_{\mathrm{word}} \to_{\mathbb{C}} \mathbb{C}$. -/
def phi0 : WordCore →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun p => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (canonicalGaugeState p.1 p.2))

/-- 🏆 Evaluation of $\varphi_0$ on single monomials $S_u S_v^\dagger$. -/
@[simp] theorem phi0_monomial (u v : List Bool) :
    phi0 (wordMonomial u v) = canonicalGaugeState u v := by
  change (Finsupp.lsum ℂ (fun p => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (canonicalGaugeState p.1 p.2)))
      (Finsupp.single (u, v) (1 : ℂ)) = canonicalGaugeState u v
  rw [Finsupp.lsum_single]
  simp

/-- The gauge conditional expectation $E_0 : \mathcal{A}_{\mathrm{word}} \to_{\mathbb{C}} \mathcal{A}_{\mathrm{word}}$
    as a $\mathbb{C}$-linear degree-projection map. -/
def E0 : WordCore →ₗ[ℂ] WordCore :=
  Finsupp.lsum ℂ (fun p =>
    if p.1.length = p.2.length then
      LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (Finsupp.single p (1 : ℂ))
    else
      0)

/-- 🏆 Evaluation of $E_0$ on single monomials $S_u S_v^\dagger$. -/
@[simp] theorem E0_monomial (u v : List Bool) :
    E0 (wordMonomial u v) =
      if u.length = v.length then wordMonomial u v else 0 := by
  change (Finsupp.lsum ℂ (fun p =>
    if p.1.length = p.2.length then
      LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (Finsupp.single p (1 : ℂ))
    else
      0)) (Finsupp.single (u, v) (1 : ℂ)) =
      if u.length = v.length then wordMonomial u v else 0
  rw [Finsupp.lsum_single]
  by_cases hlen : u.length = v.length
  · rw [if_pos hlen, if_pos hlen]
    simp [wordMonomial]
  · rw [if_neg hlen, if_neg hlen]
    simp

/-- The $\mathbb{C}$-linear UHF trace functional $\tau_0 : \mathcal{A}_{\mathrm{word}} \to_{\mathbb{C}} \mathbb{C}$. -/
def tau0 : WordCore →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun p => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (uhfTracialStateWord p.1 p.2))

/-! The following is an honest algebraic boundedness statement.  The norm is
the finitely supported `ℓ¹` coefficient norm; this is deliberately not yet
the norm of the completed concrete C*-algebra. -/

def wordCoreL1Norm (c : WordCore) : ℝ :=
  ∑ p ∈ c.support, ‖c p‖

theorem canonicalGaugeState_norm_le_one (u v : List Bool) :
    ‖canonicalGaugeState u v‖ ≤ 1 := by
  rw [canonicalGaugeState_word]
  split_ifs with huv
  · subst huv
    rw [norm_pow]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  · simp

theorem phi0_norm_le_wordCoreL1Norm (c : WordCore) :
    ‖phi0 c‖ ≤ wordCoreL1Norm c := by
  classical
  change ‖∑ p ∈ c.support, c p * canonicalGaugeState p.1 p.2‖ ≤
    ∑ p ∈ c.support, ‖c p‖
  calc
    ‖∑ p ∈ c.support, c p * canonicalGaugeState p.1 p.2‖
        ≤ ∑ p ∈ c.support, ‖c p * canonicalGaugeState p.1 p.2‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ p ∈ c.support, ‖c p‖ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      have hstate := canonicalGaugeState_norm_le_one p.1 p.2
      nlinarith [norm_nonneg (c p)]

theorem uhfTracialStateWord_norm_le_one (u v : List Bool) :
    ‖uhfTracialStateWord u v‖ ≤ 1 := by
  rw [uhfTracialStateWord]
  split_ifs with huv
  · subst huv
    rw [norm_pow]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  · simp

theorem tau0_norm_le_wordCoreL1Norm (c : WordCore) :
    ‖tau0 c‖ ≤ wordCoreL1Norm c := by
  classical
  change ‖∑ p ∈ c.support, c p * uhfTracialStateWord p.1 p.2‖ ≤
    ∑ p ∈ c.support, ‖c p‖
  calc
    ‖∑ p ∈ c.support, c p * uhfTracialStateWord p.1 p.2‖
        ≤ ∑ p ∈ c.support, ‖c p * uhfTracialStateWord p.1 p.2‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ p ∈ c.support, ‖c p‖ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      have hstate := uhfTracialStateWord_norm_le_one p.1 p.2
      nlinarith [norm_nonneg (c p)]

/-! Compatibility with the already constructed finite C⋆ matrix trace states.
This is the concrete finite-stage descent datum used by any later completion
construction; it does not assert an infinite C⋆ state. -/

theorem phi0_bitWord_monomial_eq_matrixTraceState
    (n : ℕ) (u v : BitWord n) :
    phi0 (wordMonomial (List.ofFn u) (List.ofFn v)) =
      matrixTraceState n
        (Matrix.single (bitWordIndexEquiv n u) (bitWordIndexEquiv n v) 1) := by
  rw [phi0_monomial]
  exact (matrixTraceState_bitWordUnit_eq_canonicalGaugeState n u v).symm

/-! The preceding finite-stage identity also agrees with the existing
topological-colimit readout.  This is a readout compatibility theorem only:
it does not construct an infinite C⋆ completion or a completed gauge state. -/

theorem phi0_bitWord_monomial_eq_topologicalColimitTrace
    (n : ℕ) (u v : BitWord n) :
    cstarMatrixTraceStateTopologicalColimitMap
        (topologicalInjection
          InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState.CStarMatrixStage
          InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState.cstarMatrixInductiveSystem n
          (Matrix.single (bitWordIndexEquiv n u) (bitWordIndexEquiv n v) 1)) =
      ULift.up (phi0 (wordMonomial (List.ofFn u) (List.ofFn v))) := by
  rw [cstarMatrixTraceStateTopologicalColimitMap_inclusion]
  rw [phi0_bitWord_monomial_eq_matrixTraceState]
  rfl

/-- 🏆 Evaluation of $\tau_0$ on single monomials $S_u S_v^\dagger$. -/
@[simp] theorem tau0_monomial (u v : List Bool) :
    tau0 (wordMonomial u v) = uhfTracialStateWord u v := by
  change (Finsupp.lsum ℂ (fun p => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (uhfTracialStateWord p.1 p.2)))
      (Finsupp.single (u, v) (1 : ℂ)) = uhfTracialStateWord u v
  rw [Finsupp.lsum_single]
  simp

/-- 🏆 THEOREM: Exact $\mathbb{C}$-linear Factorization $\varphi_0 = \tau_0 \circ E_0$. -/
theorem phi0_eq_tau0_comp_E0 : phi0 = tau0.comp E0 := by
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext_ring
  change phi0 (wordMonomial p.1 p.2) = tau0 (E0 (wordMonomial p.1 p.2))
  rw [phi0_monomial, E0_monomial]
  by_cases hlen : p.1.length = p.2.length
  · rw [if_pos hlen, tau0_monomial]
    rw [CantorBernoulliGaugeUHFFactorizationBridge.canonicalGaugeState_word_factorization]
    dsimp [gaugeConditionalExpectationWord]
    rw [if_pos hlen]
  · rw [if_neg hlen, map_zero]
    rw [CantorBernoulliGaugeUHFFactorizationBridge.canonicalGaugeState_word_factorization]
    dsimp [gaugeConditionalExpectationWord]
    rw [if_neg hlen]

/-- 🏆 THEOREM: Idempotence of the linear conditional expectation $E_0 \circ E_0 = E_0$. -/
theorem E0_idempotent : E0.comp E0 = E0 := by
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext_ring
  change E0 (E0 (wordMonomial p.1 p.2)) = E0 (wordMonomial p.1 p.2)
  rw [E0_monomial]
  by_cases hlen : p.1.length = p.2.length
  · rw [if_pos hlen, E0_monomial, if_pos hlen]
  · rw [if_neg hlen, map_zero]

/-- 🏆 THEOREM: Involutive symmetry of $\varphi_0$ on monomial adjoints $(S_u S_v^\dagger)^* = S_v S_u^\dagger$. -/
theorem phi0_star_monomial (u v : List Bool) :
    phi0 (wordMonomial v u) = star (phi0 (wordMonomial u v)) := by
  rw [phi0_monomial, phi0_monomial]
  rw [canonicalGaugeState_word, canonicalGaugeState_word]
  by_cases huv : u = v
  · subst huv
    simp
  · have hvu : v ≠ u := ne_comm.mp huv
    simp [if_neg huv, if_neg hvu]

/-- 🏆 THEOREM: $E_0$ commutes with monomial adjoints $(S_u S_v^\dagger)^* = S_v S_u^\dagger$. -/
theorem E0_star_monomial (u v : List Bool) :
    E0 (wordMonomial v u) =
      if u.length = v.length then wordMonomial v u else 0 := by
  rw [E0_monomial]
  by_cases hlen : u.length = v.length
  · have hlen' : v.length = u.length := hlen.symm
    rw [if_pos hlen, if_pos hlen']
  · have hlen' : v.length ≠ u.length := ne_comm.mp hlen
    rw [if_neg hlen, if_neg hlen']

end InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge
