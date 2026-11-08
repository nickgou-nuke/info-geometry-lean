/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Real.Basic

/-!
# Projective Hessian-Metriplectic Bridge

This module formalizes the compatible geometric triple $(g, J, \Omega)$ and the
metriplectic generator decomposition $\mathcal{L} = \mathcal{J}_{\text{ham}} + \mathcal{M}_{\text{diss}}$:

1. **Kähler-Type Compatible Triple**:
   - Complex structure $J : V \to V$ with $J^2 = -I$.
   - Symplectic form $\Omega : V \times V \to \mathbb{R}$ (antisymmetric, $J$-invariant).
   - Hessian metric $g : V \times V \to \mathbb{R}$ (symmetric, positive semidefinite).
   - Compatibility: $g(u, v) = \Omega(u, J v)$ and $\Omega(J u, J v) = \Omega(u, v)$.

2. **Metriplectic Dynamical Bracket**:
   - Reversible Poisson bracket $\langle\langle F, G \rangle\rangle = -\langle\langle G, F \rangle\rangle$.
   - Dissipative metric bracket $(F, G) = (G, F)$ with $(F, F) \ge 0$.
   - Casimir degeneracy conditions:
     * $(dH, F) = 0$ (Hamiltonian is a Casimir of dissipation).
     * $\langle\langle dS, F \rangle\rangle = 0$ (Entropy is a Casimir of the Poisson flow).

3. **Thermodynamic Laws**:
   - **First Law (Energy Conservation)**: $\frac{dH}{dt} = \langle\langle dH, dH \rangle\rangle + (dH, dS) = 0$.
   - **Second Law (Entropy Production)**: $\frac{dS}{dt} = \langle\langle dS, dH \rangle\rangle + (dS, dS) = (dS, dS) \ge 0$.
-/

noncomputable section

namespace InfoGeometry.Geometry.ProjectiveHessianMetriplecticBridge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Kähler-type compatible triple `(g, J, Ω)` on a real vector space `V`. -/
structure KahlerCompatibleTriple (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Complex structure endomorphism `J`. -/
  J : V →ₗ[ℝ] V
  /-- `J² = -I`. -/
  J_sq : ∀ v, J (J v) = -v
  /-- Symplectic form `Ω`. -/
  omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  /-- `Ω` is antisymmetric. -/
  omega_antisymm : ∀ u v, omega u v = - omega v u
  /-- Hessian / Riemannian metric `g`. -/
  g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  /-- `g` is symmetric. -/
  g_symm : ∀ u v, g u v = g v u
  /-- `g` is positive semi-definite. -/
  g_nonneg : ∀ u, 0 ≤ g u u
  /-- Compatibility: `g(u, v) = Ω(u, J v)`. -/
  compatibility : ∀ u v, g u v = omega u (J v)

/-- Symplectic form vanishes on the diagonal: `Ω(u, u) = 0`. -/
theorem omega_self_zero (triple : KahlerCompatibleTriple V) (u : V) :
    triple.omega u u = 0 := by
  have h := triple.omega_antisymm u u
  linarith

/-- `Ω` is invariant under `J`: `Ω(J u, J v) = Ω(u, v)`. -/
theorem omega_J_invariant (triple : KahlerCompatibleTriple V) (u v : V) :
    triple.omega (triple.J u) (triple.J v) = triple.omega u v := by
  have hg1 : triple.g (triple.J u) v = triple.omega (triple.J u) (triple.J v) :=
    triple.compatibility (triple.J u) v
  have hg2 : triple.g (triple.J u) v = triple.g v (triple.J u) :=
    triple.g_symm (triple.J u) v
  have hg3 : triple.g v (triple.J u) = triple.omega v (triple.J (triple.J u)) :=
    triple.compatibility v (triple.J u)
  rw [triple.J_sq u] at hg3
  have hlin : triple.omega v (-u) = - triple.omega v u := by
    rw [map_neg]
  have hanti : - triple.omega v u = triple.omega u v := by
    have h := triple.omega_antisymm u v
    linarith
  rw [← hg1, hg2, hg3, hlin, hanti]

/-- Metriplectic dynamical bracket and generators on `V`. -/
structure MetriplecticBracket (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Poisson / Reversible bilinear bracket `⟨⟨·, ·⟩⟩_ham`. -/
  poisson : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  /-- Metric / Dissipative bilinear bracket `(·, ·)_diss`. -/
  dissipative : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  /-- Poisson bracket is antisymmetric: `⟨⟨F, G⟩⟩ = - ⟨⟨G, F⟩⟩`. -/
  poisson_antisymm : ∀ F G, poisson F G = - poisson G F
  /-- Metric bracket is symmetric: `(F, G) = (G, F)`. -/
  dissipative_symm : ∀ F G, dissipative F G = dissipative G F
  /-- Metric bracket is positive semidefinite: `(F, F) ≥ 0`. -/
  dissipative_nonneg : ∀ F, 0 ≤ dissipative F F
  /-- Specific system observables: Hamiltonian gradient `dH` and Entropy gradient `dS`. -/
  dH : V
  dS : V
  /-- Hamiltonian is a Casimir of dissipation: `(dH, F) = 0` for all `F`. -/
  dissipative_dH : ∀ F, dissipative dH F = 0
  /-- Entropy is a Casimir of the Poisson bracket: `⟨⟨dS, F⟩⟩ = 0` for all `F`. -/
  poisson_dS : ∀ F, poisson dS F = 0

/-- Total metriplectic rate of change of an observable `F`:
    `dF/dt = ⟨⟨F, dH⟩⟩ + (F, dS)`. -/
def metriplecticFlow (sys : MetriplecticBracket V) (dF : V) : ℝ :=
  sys.poisson dF sys.dH + sys.dissipative dF sys.dS

/-- 🏆 MASTER THEOREM (First Law of Thermodynamics / Energy Conservation):
    `dH/dt = ⟨⟨dH, dH⟩⟩ + (dH, dS) = 0 + 0 = 0`. -/
theorem first_law_energy_conservation (sys : MetriplecticBracket V) :
    metriplecticFlow sys sys.dH = 0 := by
  dsimp [metriplecticFlow]
  have h_ham : sys.poisson sys.dH sys.dH = 0 := by
    have h := sys.poisson_antisymm sys.dH sys.dH
    linarith
  have h_diss : sys.dissipative sys.dH sys.dS = 0 :=
    sys.dissipative_dH sys.dS
  rw [h_ham, h_diss, add_zero]

/-- 🏆 MASTER THEOREM (Second Law of Thermodynamics / Entropy Production):
    `dS/dt = ⟨⟨dS, dH⟩⟩ + (dS, dS) = 0 + (dS, dS) ≥ 0`. -/
theorem second_law_entropy_production (sys : MetriplecticBracket V) :
    0 ≤ metriplecticFlow sys sys.dS := by
  dsimp [metriplecticFlow]
  have h_ham : sys.poisson sys.dS sys.dH = 0 :=
    sys.poisson_dS sys.dH
  have h_diss : 0 ≤ sys.dissipative sys.dS sys.dS :=
    sys.dissipative_nonneg sys.dS
  rw [h_ham, zero_add]
  exact h_diss

end InfoGeometry.Geometry.ProjectiveHessianMetriplecticBridge
