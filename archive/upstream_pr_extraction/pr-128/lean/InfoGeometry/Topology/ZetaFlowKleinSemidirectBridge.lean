import InfoGeometry.Topology.ZetaCenteredCoordinateBridge
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Klein Four-Group Semidirect Action on Zeta Flow & Height Character

This module formalizes the canonical Klein Four-Group $V_4 \simeq \mathbb{Z}_2 \times \mathbb{Z}_2$
action on the 2D centered zeta flow space, and proves the unified semidirect flow conjugation:
$$g \cdot \Phi_t(p) = \Phi_{\chi_h(g) t}(g \cdot p) \qquad (\forall g \in V_4)$$
where $\chi_h : V_4 \to \{+1, -1\}$ is the height character.
-/

noncomputable section

namespace InfoGeometry.Topology.ZetaFlowKleinSemidirect

open InfoGeometry.Topology.ZetaCenteredCoordinate
open InfoGeometry.Topology.ZetaCenteredCoordinate.ZetaFlowPoint

/-- Canonical Klein Four-Group V₄ ≃ ℤ₂ × ℤ₂ -/
abbrev ZetaKlein4 := ZMod 2 × ZMod 2

namespace ZetaKlein4

def identity : ZetaKlein4 := (0, 0)
def sigma : ZetaKlein4 := (1, 0)
def gamma : ZetaKlein4 := (0, 1)
def tau : ZetaKlein4 := (1, 1)

/-- Height character χ_h : V₄ → ℝ giving the sign of vertical time inversion:
    - χ_h(id) = +1
    - χ_h(γ)  = +1 (antiunitary critical reflection preserves vertical flow direction)
    - χ_h(σ)  = -1 (Schwarz conjugation reverses vertical time)
    - χ_h(τ)  = -1 (functional reflection reverses vertical time)
    Equivalently: χ_h(g) = +1 if g.1 = 0 else -1. -/
def heightCharacter (g : ZetaKlein4) : ℝ :=
  if g.1 = 0 then 1 else -1

/-- Action of V₄ on ZetaFlowPoint -/
def act (g : ZetaKlein4) (p : ZetaFlowPoint) : ZetaFlowPoint :=
  if g = (0, 0) then p
  else if g = (1, 0) then sigmaReflect p
  else if g = (0, 1) then gammaReflect p
  else tauReflect p

/-- Vertical flow on centered coordinates: Φ_t(u, tau) = (u, tau + t) -/
def verticalFlow (t : ℝ) (p : ZetaFlowPoint) : ZetaFlowPoint :=
  ⟨p.u, p.tau + t⟩

/-- 🏆 THEOREM 1: Group law for vertical flow: Φ_{t1 + t2} = Φ_{t1} ∘ Φ_{t2} -/
theorem verticalFlow_add (t1 t2 : ℝ) (p : ZetaFlowPoint) :
    verticalFlow (t1 + t2) p = verticalFlow t1 (verticalFlow t2 p) := by
  dsimp [verticalFlow]
  ext
  · rfl
  · ring

/-- 🏆 THEOREM 2: UNIFIED FLOW CONJUGATION THEOREM:
    $$g \cdot \Phi_t(p) = \Phi_{\chi_h(g) t}(g \cdot p)$$
    for all elements g ∈ V₄, establishing the semidirect product flow ℝ ⋊_{χ_h} V₄. -/
theorem flow_conjugation_unified (g : ZetaKlein4) (t : ℝ) (p : ZetaFlowPoint) :
    act g (verticalFlow t p) = verticalFlow (heightCharacter g * t) (act g p) := by
  rcases g with ⟨g1, g2⟩
  fin_cases g1 <;> fin_cases g2
  · -- (0, 0) = identity
    dsimp [act, heightCharacter, verticalFlow]
    ext <;> ring
  · -- (0, 1) = gamma
    dsimp [act, heightCharacter, verticalFlow, gammaReflect]
    ext <;> ring
  · -- (1, 0) = sigma
    dsimp [act, heightCharacter, verticalFlow, sigmaReflect]
    ext <;> ring
  · -- (1, 1) = tau
    dsimp [act, heightCharacter, verticalFlow, tauReflect]
    ext <;> ring

/-- 🏆 THEOREM 3: Height Character Values on the Canonical Elements -/
theorem heightCharacter_values :
    (heightCharacter (0, 0) = 1) ∧
    (heightCharacter (0, 1) = 1) ∧
    (heightCharacter (1, 0) = -1) ∧
    (heightCharacter (1, 1) = -1) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- 🏆 THEOREM 4: Height Character Multiplicative Homomorphism Law:
    $$\chi_h(g_1 + g_2) = \chi_h(g_1) \cdot \chi_h(g_2)$$ -/
theorem heightCharacter_mul (g1 g2 : ZetaKlein4) :
    heightCharacter (g1 + g2) = heightCharacter g1 * heightCharacter g2 := by
  have h_scalar : ∀ a b : ZMod 2,
      (if (a + b) = 0 then (1 : ℝ) else -1) =
      (if a = 0 then 1 else -1) * (if b = 0 then 1 else -1) := by
    intro a b
    fin_cases a <;> fin_cases b
    · simp
    · simp
    · simp
    · have h : (1 : ZMod 2) + 1 = 0 := rfl
      simp [h]
  exact h_scalar g1.1 g2.1

end ZetaKlein4

end InfoGeometry.Topology.ZetaFlowKleinSemidirect
