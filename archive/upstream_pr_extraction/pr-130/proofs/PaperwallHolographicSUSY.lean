import Mathlib

/-!
# Paperwall holography SUSY algebra

This module formalizes the algebraic stepping stone in the prompt:

* Cuntz-boundary fermionization gives an odd operator `c` with `c²=0` and
  `{c,c†}=1`;
* a paperwall/glide operator `G` is an invertible geometric symmetry;
* coupling them gives a supercharge `Q = cG` with `Q²=0` and Hamiltonian
  `{Q,Q†}=1` under flat/topological glide covariance;
* non-symmorphic glide symmetry has `glide² = translation`.
-/

noncomputable section

namespace PaperwallHolographicSUSY

/-! ## 1. Cuntz/Cantor boundary fermionization coupled to a glide -/

variable {R : Type*} [Ring R]
variable (c cdag G Ginv : R)

/-- The paperwall supercharge `Q = cG`. -/
def supercharge : R := c * G

/-- The adjoint/superpartner `Q† = G⁻¹ c†`. -/
def superchargeDag : R := Ginv * cdag

/-- Supercharge nilpotency: `Q²=0`, i.e. Pauli exclusion transported by glide. -/
theorem supercharge_sq_zero (c_sq : c * c = 0) (c_comm_G : c * G = G * c) :
    supercharge c G * supercharge c G = 0 := by
  unfold supercharge
  calc
    (c * G) * (c * G) = c * (G * c) * G := by noncomm_ring
    _ = c * (c * G) * G := by rw [← c_comm_G]
    _ = (c * c) * (G * G) := by noncomm_ring
    _ = 0 := by rw [c_sq, zero_mul]

/-- The SUSY Hamiltonian `{Q,Q†}`. -/
def susyHamiltonian : R :=
  supercharge c G * superchargeDag cdag Ginv + superchargeDag cdag Ginv * supercharge c G

/-- Flat/topological paperwall SUSY: `{Q,Q†}=1`. -/
theorem susyHamiltonian_eq_one
    (fermion_anticomm : c * cdag + cdag * c = 1)
    (G_right_inv : G * Ginv = 1)
    (even_covariant : Ginv * (cdag * c) * G = cdag * c) :
    susyHamiltonian c cdag G Ginv = 1 := by
  unfold susyHamiltonian supercharge superchargeDag
  calc
    (c * G) * (Ginv * cdag) + (Ginv * cdag) * (c * G)
        = c * (G * Ginv) * cdag + Ginv * (cdag * c) * G := by noncomm_ring
    _ = c * 1 * cdag + cdag * c := by rw [G_right_inv, even_covariant]
    _ = c * cdag + cdag * c := by rw [mul_one]
    _ = 1 := fermion_anticomm

/-- Synthesis theorem for the Cuntz/glide SUSY construction. -/
theorem paperwall_susy_synthesis
    (c_sq : c * c = 0)
    (c_comm_G : c * G = G * c)
    (fermion_anticomm : c * cdag + cdag * c = 1)
    (G_right_inv : G * Ginv = 1)
    (even_covariant : Ginv * (cdag * c) * G = cdag * c) :
    supercharge c G * supercharge c G = 0 ∧ susyHamiltonian c cdag G Ginv = 1 := by
  constructor
  · exact supercharge_sq_zero c G c_sq c_comm_G
  · exact susyHamiltonian_eq_one c cdag G Ginv
      fermion_anticomm G_right_inv even_covariant

/-! ## 2. Non-symmorphic glide -/

variable {Γ : Type*} [Group Γ]
variable (tx ty glide : Γ)

/-- Two glide periods give two lattice translations. -/
theorem glide_fourth_translation_sq (glide_sq : glide ^ 2 = tx) :
    glide ^ 4 = tx ^ 2 := by
  rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, glide_sq]
  simp [pow_two]

/-- Package the genuinely proven paperwall/Klein-bottle facts used by the holographic construction. -/
theorem klein_glide_synthesis (glide_sq : glide ^ 2 = tx) :
    glide ^ 4 = tx ^ 2 := by
  exact glide_fourth_translation_sq tx glide glide_sq

end PaperwallHolographicSUSY
