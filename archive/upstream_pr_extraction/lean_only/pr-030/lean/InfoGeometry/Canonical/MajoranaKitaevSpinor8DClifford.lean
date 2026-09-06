import Mathlib.Tactic

open Matrix

noncomputable section

namespace InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford

/-!
# Nambu-Gor'kov 8D Spinor Charge Conjugation in Cl(3,3) & Kitaev BdG Hamiltonian

This module formalizes the concrete 8×8 Nambu-Gor'kov Bogoliubov-de Gennes (BdG) Hamiltonian
matrix $H_{\text{BdG8}}(\mu, t, \Delta) \in M_8(\mathbb{R})$ for a 4-site p-wave superconductor,
the 8D particle-hole charge conjugation operator $\mathcal{C}_8 = \tau_x \otimes I_4 \in M_8(\mathbb{R})$ in $\text{Cl}(3,3) \cong M_8(\mathbb{R})$,
and 8D boundary Majorana zero mode eigenvectors $\gamma_1, \gamma_8 \in \mathbb{R}^8$:

Proved Theorems:
1. 8D Particle-Hole Involutivity: $\mathcal{C}_8^2 = I_8$ (Class BDI $\mathcal{C}_8^2 = +1$ in 8D Nambu space)
2. Real Matrix Symmetry: $H_{\text{BdG8}}^T = H_{\text{BdG8}}$
3. 8D BdG Particle-Hole Anti-Symmetry Constraint: $\mathcal{C}_8 H_{\text{BdG8}}^T \mathcal{C}_8 = - H_{\text{BdG8}}$
4. Left Boundary 8D Majorana Zero Mode: $H_{\text{sweet8}} \cdot \gamma_1 = 0$
5. Right Boundary 8D Majorana Zero Mode: $H_{\text{sweet8}} \cdot \gamma_8 = 0$.
-/

abbrev Mat8R := Matrix (Fin 8) (Fin 8) ℝ
abbrev Vec8R := Fin 8 → ℝ

/-- Particle-hole charge conjugation operator C₈ = τ_x ⊗ I₄ in 8×8 real Nambu space. -/
def particleHole8 : Mat8R :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0]

/-- Concrete 4-site Kitaev BdG Hamiltonian matrix with physical parameters μ, t, Δ ∈ ℝ in 8×8 real space. -/
def kitaevBdG8 (mu t delta : ℝ) : Mat8R :=
  !![-mu, -t, 0, 0, 0, delta, 0, 0;
     -t, -mu, -t, 0, -delta, 0, delta, 0;
     0, -t, -mu, -t, 0, -delta, 0, delta;
     0, 0, -t, -mu, 0, 0, -delta, 0;
     0, -delta, 0, 0, mu, t, 0, 0;
     delta, 0, -delta, 0, t, mu, t, 0;
     0, delta, 0, -delta, 0, t, mu, t;
     0, 0, delta, 0, 0, 0, t, mu]

/-- Sweet-spot 4-site Kitaev BdG Hamiltonian (μ = 0, Δ = t). -/
def kitaevSweetSpot8 (t : ℝ) : Mat8R :=
  !![0, -t, 0, 0, 0, t, 0, 0;
     -t, 0, -t, 0, -t, 0, t, 0;
     0, -t, 0, -t, 0, -t, 0, t;
     0, 0, -t, 0, 0, 0, -t, 0;
     0, -t, 0, 0, 0, t, 0, 0;
     t, 0, -t, 0, t, 0, t, 0;
     0, t, 0, -t, 0, t, 0, t;
     0, 0, t, 0, 0, 0, t, 0]

/-- Left boundary Majorana zero mode vector in 8D: γ₁ = (1, 0, 0, 0, -1, 0, 0, 0)ᵀ. -/
def majoranaZeroModeLeft8 : Vec8R :=
  ![1, 0, 0, 0, -1, 0, 0, 0]

/-- Right boundary Majorana zero mode vector in 8D: γ₈ = (0, 0, 0, 1, 0, 0, 0, 1)ᵀ. -/
def majoranaZeroModeRight8 : Vec8R :=
  ![0, 0, 0, 1, 0, 0, 0, 1]

/-- **Theorem**: Particle-Hole Charge Conjugation Involutivity in 8D: C₈² = I₈ (Class BDI C₈² = +1). -/
theorem particleHole8_square : particleHole8 * particleHole8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [particleHole8, mul_apply, Fin.sum_univ_eight]

/-- **Theorem**: Symmetry of 8D BdG Hamiltonian H_BdG8ᵀ = H_BdG8 for real parameters. -/
theorem kitaevBdG8_symmetric (mu t delta : ℝ) :
    (kitaevBdG8 mu t delta).transpose = kitaevBdG8 mu t delta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kitaevBdG8, transpose_apply]

/-- **Theorem**: Exact 8D BdG Particle-Hole Anti-Symmetry Constraint:
    C₈ H_BdG8ᵀ C₈ = - H_BdG8. -/
theorem kitaevBdG8_particle_hole_symmetry (mu t delta : ℝ) :
    particleHole8 * (kitaevBdG8 mu t delta).transpose * particleHole8 = - kitaevBdG8 mu t delta := by
  rw [kitaevBdG8_symmetric]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [particleHole8, kitaevBdG8, mul_apply, neg_apply, Fin.sum_univ_eight]

/-- **Theorem**: Left Boundary 8D Majorana Zero Mode Energy Eigenvalue: H_sweet8 · γ₁ = 0. -/
theorem left_majorana_zero_mode_energy8 (t : ℝ) :
    (kitaevSweetSpot8 t).mulVec majoranaZeroModeLeft8 = 0 := by
  dsimp [kitaevSweetSpot8, majoranaZeroModeLeft8]
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_eight]

/-- **Theorem**: Right Boundary 8D Majorana Zero Mode Energy Eigenvalue: H_sweet8 · γ₈ = 0. -/
theorem right_majorana_zero_mode_energy8 (t : ℝ) :
    (kitaevSweetSpot8 t).mulVec majoranaZeroModeRight8 = 0 := by
  dsimp [kitaevSweetSpot8, majoranaZeroModeRight8]
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_eight]

end InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford
