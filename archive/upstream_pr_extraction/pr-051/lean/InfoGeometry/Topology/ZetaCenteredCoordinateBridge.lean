import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

/-!
# Zeta Centered Coordinate Bridge & Complete Klein Four-Group $V_4$ Orbit

This module formalizes the flow-adapted centered coordinate representation:
$$s = \left(\frac{1}{2} + u\right) + i\tau \longleftrightarrow (u, \tau) \in \mathbb{R}^2$$
establishing the exact bijective isomorphism `ZetaFlowPoint ≃ ℂ`,
its fixed locus on the critical line $u = 0$, and character parity under $V_4$.
-/

noncomputable section

namespace InfoGeometry.Topology.ZetaCenteredCoordinate

open Complex

/-- Flow-adapted 2D centered coordinate point representing s = 1/2 + u + i*tau -/
@[ext]
structure ZetaFlowPoint where
  u : ℝ
  tau : ℝ
  deriving DecidableEq

namespace ZetaFlowPoint

/-- Map from ZetaFlowPoint to Complex -/
def toComplex (p : ZetaFlowPoint) : ℂ :=
  ⟨1 / 2 + p.u, p.tau⟩

/-- Map from Complex to ZetaFlowPoint -/
def ofComplex (s : ℂ) : ZetaFlowPoint :=
  ⟨s.re - 1 / 2, s.im⟩

@[simp] theorem ofComplex_toComplex (p : ZetaFlowPoint) :
    ofComplex (toComplex p) = p := by
  dsimp [ofComplex, toComplex]
  ext
  · ring
  · rfl

@[simp] theorem toComplex_ofComplex (s : ℂ) :
    toComplex (ofComplex s) = s := by
  dsimp [ofComplex, toComplex]
  rw [Complex.ext_iff]
  refine ⟨by ring, rfl⟩

/-- 🏆 THEOREM 1: Exact Bidirectional Equivalence between ZetaFlowPoint and ℂ -/
def zetaFlowPointEquivComplex : ZetaFlowPoint ≃ ℂ where
  toFun := toComplex
  invFun := ofComplex
  left_inv := ofComplex_toComplex
  right_inv := toComplex_ofComplex

/-! ## 2. V₄ Involutions on Centered Coordinates -/

/-- Functional reflection τ: (u, tau) ↦ (-u, -tau) -/
def tauReflect (p : ZetaFlowPoint) : ZetaFlowPoint :=
  ⟨-p.u, -p.tau⟩

/-- Schwarz conjugation σ: (u, tau) ↦ (u, -tau) -/
def sigmaReflect (p : ZetaFlowPoint) : ZetaFlowPoint :=
  ⟨p.u, -p.tau⟩

/-- Antiunitary critical reflection γ: (u, tau) ↦ (-u, tau) -/
def gammaReflect (p : ZetaFlowPoint) : ZetaFlowPoint :=
  ⟨-p.u, p.tau⟩

/-- 🏆 THEOREM 2: Involutive and Composition Laws of V₄ -/
theorem v4_orbit_relations (p : ZetaFlowPoint) :
    (tauReflect (tauReflect p) = p) ∧
    (sigmaReflect (sigmaReflect p) = p) ∧
    (gammaReflect (gammaReflect p) = p) ∧
    (gammaReflect p = tauReflect (sigmaReflect p)) ∧
    (gammaReflect p = sigmaReflect (tauReflect p)) := by
  dsimp [tauReflect, sigmaReflect, gammaReflect]
  refine ⟨by ext <;> ring, by ext <;> ring, by ext <;> ring, by ext <;> ring, by ext <;> ring⟩

/-- 🏆 THEOREM 3: Critical Line Fixed Locus Equivalence:
    $$\gamma(p) = p \iff p.u = 0$$ -/
theorem critical_line_fixed_locus_iff (p : ZetaFlowPoint) :
    gammaReflect p = p ↔ p.u = 0 := by
  dsimp [gammaReflect]
  constructor
  · intro h
    have hu : -p.u = p.u := by
      exact (congr_arg ZetaFlowPoint.u h)
    linarith
  · intro hu
    ext
    · rw [hu]; ring
    · rfl

/-- 🏆 THEOREM 4: Coordinate-Level Compatibility with Complex Plane Reflections -/
theorem toComplex_reflections (p : ZetaFlowPoint) :
    (toComplex (tauReflect p) = 1 - toComplex p) ∧
    (toComplex (sigmaReflect p) = star (toComplex p)) ∧
    (toComplex (gammaReflect p) = 1 - star (toComplex p)) := by
  dsimp [toComplex, tauReflect, sigmaReflect, gammaReflect]
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.ext_iff]; simp; ring
  · rw [Complex.ext_iff]; simp
  · rw [Complex.ext_iff]; simp; ring

end ZetaFlowPoint

end InfoGeometry.Topology.ZetaCenteredCoordinate
