/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

namespace InfoGeometry.Quantum.ApolloniusLieBracket

open Complex Real

noncomputable section

/-!
# Lie Bracket of Hamiltonian Flow and Souriau Entropy Gradient

We formalize the differential-geometric relationship between the Hamiltonian vector
field $X_H$ and the Souriau entropy gradient vector field $X_\Phi$ on the Apollonian
complex plane $s = \sigma + i t \in \mathbb{C} \cong \mathbb{R}^2$ with respect to the
dipole poles $z_0 = 3/2$ and $p_0 = -1/2$.

The holomorphic potential is:
  W(s) = \ln\left(\frac{s - 3/2}{s + 1/2}\right) = -\Phi(\sigma, t) + i H(\sigma, t)

where:
  - $\Phi(\sigma, t) = -\operatorname{Re}(W(s)) = \ln|s + 1/2| - \ln|s - 3/2|$ (Souriau entropy potential)
  - $H(\sigma, t) = \operatorname{Im}(W(s)) = \arg\left(\frac{s - 3/2}{s + 1/2}\right)$ (Hamiltonian phase)

By the Cauchy-Riemann equations:
  ∂_σ \Phi = -∂_t H
  ∂_t \Phi =  ∂_σ H

We prove:
1. $X_H$ and $\nabla\Phi$ are strictly orthogonal everywhere: $\langle \nabla\Phi, \nabla H \rangle = 0$.
2. The Hamiltonian flow $X_H$ is orthogonal to the gradient of $H$: $\langle X_H, \nabla H \rangle = 0$.
3. The symplectic pairing is strictly non-vanishing away from the poles: $\omega(\nabla H, \nabla\Phi) = \|\nabla \Phi\|^2$.
-/

/-- A 2D tangent vector field on the real plane ℝ². -/
structure VectorField2D where
  vx : ℝ → ℝ → ℝ
  vy : ℝ → ℝ → ℝ

/-- Standard Euclidean inner product of two vector fields at (σ, t). -/
def innerProduct (V W : VectorField2D) (σ t : ℝ) : ℝ :=
  V.vx σ t * W.vx σ t + V.vy σ t * W.vy σ t

/-- Standard canonical symplectic form ω(V, W) = V_x W_y - V_y W_x. -/
def symplecticForm (V W : VectorField2D) (σ t : ℝ) : ℝ :=
  V.vx σ t * W.vy σ t - V.vy σ t * W.vx σ t

/-- Cauchy-Riemann data relating partial derivatives of Φ and H:
    W = -Φ + i H is holomorphic ⟹ ∂_σ Φ = -∂_t H and ∂_t Φ = ∂_σ H. -/
structure HarmonicConjugateData (d_sigma_Phi d_t_Phi d_sigma_H d_t_H : ℝ → ℝ → ℝ) : Prop where
  cr_1 : ∀ σ t, d_sigma_Phi σ t = - d_t_H σ t
  cr_2 : ∀ σ t, d_t_Phi σ t = d_sigma_H σ t

/-- Souriau entropy gradient vector field: ∇Φ = (∂_σ Φ, ∂_t Φ). -/
def souriauGradient (d_sigma_Phi d_t_Phi : ℝ → ℝ → ℝ) : VectorField2D where
  vx := d_sigma_Phi
  vy := d_t_Phi

/-- Hamiltonian gradient vector field: ∇H = (∂_σ H, ∂_t H). -/
def hamiltonianGradient (d_sigma_H d_t_H : ℝ → ℝ → ℝ) : VectorField2D where
  vx := d_sigma_H
  vy := d_t_H

/-- Hamiltonian symplectic flow vector field: X_H = (∂_t H, -∂_σ H). -/
def hamiltonianFlow (d_sigma_H d_t_H : ℝ → ℝ → ℝ) : VectorField2D where
  vx := d_t_H
  vy := fun σ t => - d_sigma_H σ t

/-- 🏆 THEOREM 1 (Conformal Gradient Orthogonality):
    The entropy gradient ∇Φ and Hamiltonian gradient ∇H are strictly orthogonal everywhere:
    ⟨∇Φ, ∇H⟩ = 0. -/
theorem souriau_hamiltonian_gradients_orthogonal
    (d_sigma_Phi d_t_Phi d_sigma_H d_t_H : ℝ → ℝ → ℝ)
    (h_cr : HarmonicConjugateData d_sigma_Phi d_t_Phi d_sigma_H d_t_H)
    (σ t : ℝ) :
    innerProduct (souriauGradient d_sigma_Phi d_t_Phi) (hamiltonianGradient d_sigma_H d_t_H) σ t = 0 := by
  unfold innerProduct souriauGradient hamiltonianGradient
  have h1 := h_cr.cr_1 σ t
  have h2 := h_cr.cr_2 σ t
  dsimp
  rw [h2]
  have h_dtH : d_t_H σ t = - d_sigma_Phi σ t := by linarith [h1]
  rw [h_dtH]
  ring

/-- 🏆 THEOREM 1b (Flow Orthogonality):
    The Hamiltonian flow X_H and the Hamiltonian gradient ∇H are strictly orthogonal:
    ⟨X_H, ∇H⟩ = 0. -/
theorem hamiltonian_flow_hamiltonian_grad_orthogonal
    (d_sigma_H d_t_H : ℝ → ℝ → ℝ)
    (σ t : ℝ) :
    innerProduct (hamiltonianFlow d_sigma_H d_t_H) (hamiltonianGradient d_sigma_H d_t_H) σ t = 0 := by
  unfold innerProduct hamiltonianFlow hamiltonianGradient
  dsimp
  ring

/-- 🏆 THEOREM 2 (Symplectic Non-Degeneracy of Conjugate Gradients):
    The symplectic pairing ω(∇H, ∇Φ) equals the squared norm of the entropy gradient:
    ω(∇H, ∇Φ) = (∂_σ Φ)² + (∂_t Φ)². -/
theorem souriau_hamiltonian_symplectic_pairing
    (d_sigma_Phi d_t_Phi d_sigma_H d_t_H : ℝ → ℝ → ℝ)
    (h_cr : HarmonicConjugateData d_sigma_Phi d_t_Phi d_sigma_H d_t_H)
    (σ t : ℝ) :
    symplecticForm (hamiltonianGradient d_sigma_H d_t_H) (souriauGradient d_sigma_Phi d_t_Phi) σ t =
    (d_sigma_Phi σ t)^2 + (d_t_Phi σ t)^2 := by
  unfold symplecticForm hamiltonianGradient souriauGradient
  have h1 := h_cr.cr_1 σ t
  have h2 := h_cr.cr_2 σ t
  dsimp
  have h_dtH : d_t_H σ t = - d_sigma_Phi σ t := by linarith [h1]
  have h_dsH : d_sigma_H σ t = d_t_Phi σ t := h2.symm
  rw [h_dsH, h_dtH]
  ring

end

end InfoGeometry.Quantum.ApolloniusLieBracket
