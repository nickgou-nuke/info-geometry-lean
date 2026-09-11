import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix

noncomputable section

namespace InfoGeometry.Canonical.ConcreteKitaevBdGMatrix

/-!
# Concrete 4×4 Kitaev BdG Matrix, Particle-Hole Charge Conjugation & Majorana Zero Modes

This module formalizes the concrete 2-site Kitaev p-wave superconducting Bogoliubov-de Gennes
Hamiltonian matrix $H_{\text{BdG}}(\mu, t, \Delta) \in M_4(\mathbb{C})$ with physical parameters $\mu, t, \Delta \in \mathbb{R}$,
the particle-hole charge conjugation operator $\mathcal{C} = \tau_x \otimes I_2 \in M_4(\mathbb{C})$, and
boundary Majorana zero mode eigenvectors $\gamma_1, \gamma_4 \in \mathbb{C}^4$:

Proved Theorems:
1. Particle-Hole Involutivity: $\mathcal{C}^2 = I_4$ (Class BDI $\mathcal{C}^2 = +1$)
2. Self-Adjointness: $H_{\text{BdG}}^* = H_{\text{BdG}}$
3. BdG Anti-Symmetry: $\mathcal{C} H_{\text{BdG}}^* \mathcal{C} = - H_{\text{BdG}}$
4. Left Boundary Majorana Zero Mode: $H_{\text{sweet}} \gamma_1 = 0$
5. Right Boundary Majorana Zero Mode: $H_{\text{sweet}} \gamma_4 = 0$.
-/

abbrev Mat4C := InfoGeometry.Algebra.FiniteSpin.Mat4C
abbrev Vec4C := InfoGeometry.Algebra.FiniteSpin.Vec4C

/-- Particle-hole charge conjugation operator C = τ_x ⊗ I₂ in 4×4 Nambu space. -/
def particleHole4 : Mat4C :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Concrete 2-site Kitaev BdG Hamiltonian matrix with physical parameters μ, t, Δ ∈ ℝ. -/
def kitaevBdG4 (mu t delta : ℝ) : Mat4C :=
  !![-(mu : ℂ), -(t : ℂ), 0, (delta : ℂ);
     -(t : ℂ), -(mu : ℂ), -(delta : ℂ), 0;
     0, -(delta : ℂ), (mu : ℂ), (t : ℂ);
     (delta : ℂ), 0, (t : ℂ), (mu : ℂ)]

/-- Sweet-spot topological Kitaev BdG Hamiltonian (μ = 0, Δ = t). -/
def kitaevSweetSpot4 (t : ℝ) : Mat4C :=
  !![0, -(t : ℂ), 0, (t : ℂ);
     -(t : ℂ), 0, -(t : ℂ), 0;
     0, -(t : ℂ), 0, (t : ℂ);
     (t : ℂ), 0, (t : ℂ), 0]

/-- Left boundary Majorana zero mode state vector: γ₁ = (1, 0, -1, 0)ᵀ. -/
def majoranaZeroModeLeft : Vec4C :=
  ![1, 0, -1, 0]

/-- Right boundary Majorana zero mode state vector: γ₄ = (0, 1, 0, 1)ᵀ. -/
def majoranaZeroModeRight : Vec4C :=
  ![0, 1, 0, 1]

/-- **Theorem**: Particle-Hole Charge Conjugation Involutivity: C² = I₄. -/
theorem particleHole4_square : particleHole4 * particleHole4 = 1 := by
  dsimp [particleHole4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four]

/-- **Theorem**: Self-Adjointness of BdG Hamiltonian H_BdG* = H_BdG for real physical parameters. -/
theorem kitaevBdG4_self_adjoint (mu t delta : ℝ) :
    (kitaevBdG4 mu t delta).conjTranspose = kitaevBdG4 mu t delta := by
  dsimp [kitaevBdG4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTranspose_apply]

/-- **Theorem**: Exact BdG Particle-Hole Anti-Symmetry Constraint:
    C H_BdG(μ, t, Δ)* C = - H_BdG(μ, t, Δ). -/
theorem kitaevBdG4_particle_hole_symmetry (mu t delta : ℝ) :
    particleHole4 * (kitaevBdG4 mu t delta).conjTranspose * particleHole4 = - kitaevBdG4 mu t delta := by
  rw [kitaevBdG4_self_adjoint]
  dsimp [particleHole4, kitaevBdG4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four]

/-- The finite BdG Hamiltonian has cancelling particle and hole diagonal trace. -/
theorem kitaevBdG4_trace_zero (mu t delta : ℝ) :
    Matrix.trace (kitaevBdG4 mu t delta) = 0 := by
  simp [kitaevBdG4, Matrix.trace, Fin.sum_univ_four]

/-- **Theorem**: Left Boundary Majorana Zero Mode Energy Eigenvalue: H_sweet · γ₁ = 0. -/
theorem left_majorana_zero_mode_energy (t : ℝ) :
    (kitaevSweetSpot4 t).mulVec majoranaZeroModeLeft = 0 := by
  dsimp [kitaevSweetSpot4, majoranaZeroModeLeft]
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]

/-- **Theorem**: Right Boundary Majorana Zero Mode Energy Eigenvalue: H_sweet · γ₄ = 0. -/
theorem right_majorana_zero_mode_energy (t : ℝ) :
    (kitaevSweetSpot4 t).mulVec majoranaZeroModeRight = 0 := by
  dsimp [kitaevSweetSpot4, majoranaZeroModeRight]
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four]

end InfoGeometry.Canonical.ConcreteKitaevBdGMatrix
