import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real Complex

noncomputable section

namespace InfoGeometry.Physics.ApolloniusCayleyScattering

/-!
# Apollonius Bipolar Strip Geometry, Cayley Transform & Boundary Scattering
-/

/-- The Apollonian ratio mapping $s \in \mathbb{C}$ to $s / (1 - s)$. -/
def apollonianRatio (s : ℂ) : ℂ :=
  s / (1 - s)

/-- The 1-body boundary scattering amplitude $S(t) = (1/2 + it) / (1/2 - it)$. -/
def boundarySMatrix (t : ℝ) : ℂ :=
  (1 / 2 + Complex.I * (t : ℂ)) / (1 / 2 - Complex.I * (t : ℂ))

/-- 🏆 THEOREM 1: The denominator $1/2 - it$ is the complex conjugate of $1/2 + it$. -/
theorem conj_denom (t : ℝ) :
    starRingEnd ℂ (1 / 2 + Complex.I * (t : ℂ)) = 1 / 2 - Complex.I * (t : ℂ) := by
  simp only [map_add, map_div₀, map_ofNat, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- 🏆 THEOREM 2: The norm of $1/2 + it$ equals the norm of $1/2 - it$. -/
theorem norm_numerator_eq_norm_denom (t : ℝ) :
    ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ = ‖(1 / 2 : ℂ) - Complex.I * (t : ℂ)‖ := by
  have h := Complex.norm_conj ((1 / 2 : ℂ) + Complex.I * (t : ℂ))
  rw [conj_denom] at h
  exact h.symm

/-- 🏆 THEOREM 3: The denominator $1/2 - it$ is never zero for any $t \in \mathbb{R}$. -/
theorem denom_ne_zero (t : ℝ) :
    (1 / 2 : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
  intro h
  have h_re := congr_arg Complex.re h
  simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
    sub_zero, zero_re] at h_re
  norm_num at h_re

/-- 🏆 THEOREM 4: Unitarity of the boundary S-matrix along the critical line:
    $$\|S(t)\| = 1$$ -/
theorem boundary_s_matrix_unitary (t : ℝ) :
    ‖boundarySMatrix t‖ = 1 := by
  dsimp [boundarySMatrix]
  rw [norm_div]
  rw [norm_numerator_eq_norm_denom]
  exact div_self (norm_ne_zero_iff.mpr (denom_ne_zero t))

/-- 🏆 THEOREM 5: Identity scattering at the throat ground state $t = 0$: $S(0) = 1$. -/
theorem boundary_s_matrix_zero :
    boundarySMatrix 0 = 1 := by
  dsimp [boundarySMatrix]
  simp

/-- 🏆 THEOREM 6: $\mathcal{PT}$ / Time-reversal unitarity: $S(-t) = (S(t))^*$. -/
theorem boundary_s_matrix_neg (t : ℝ) :
    boundarySMatrix (-t) = starRingEnd ℂ (boundarySMatrix t) := by
  dsimp [boundarySMatrix]
  rw [map_div₀]
  have h1 : starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = (1 / 2 : ℂ) - Complex.I * (t : ℂ) :=
    conj_denom t
  have h2 : starRingEnd ℂ ((1 / 2 : ℂ) - Complex.I * (t : ℂ)) = (1 / 2 : ℂ) + Complex.I * (t : ℂ) := by
    simp only [map_sub, map_div₀, map_ofNat, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [h1, h2]
  push_cast
  ring

/-- 🏆 THEOREM 7: Unitarity product: $S(t) \cdot S(-t) = 1$. -/
theorem boundary_s_matrix_mul_neg (t : ℝ) :
    boundarySMatrix t * boundarySMatrix (-t) = 1 := by
  dsimp [boundarySMatrix]
  have h_denom := denom_ne_zero t
  have h_num : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    have h_conj := denom_ne_zero (-t)
    have h_eq : (1 / 2 : ℂ) - Complex.I * ((-t : ℝ) : ℂ) = (1 / 2 : ℂ) + Complex.I * (t : ℂ) := by
      push_cast; ring
    rw [h_eq] at h_conj
    exact h_conj
  have h_neg1 : (1 : ℂ) / 2 + Complex.I * ((-t : ℝ) : ℂ) = 1 / 2 - Complex.I * (t : ℂ) := by
    push_cast; ring
  have h_neg2 : (1 : ℂ) / 2 - Complex.I * ((-t : ℝ) : ℂ) = 1 / 2 + Complex.I * (t : ℂ) := by
    push_cast; ring
  rw [h_neg1, h_neg2]
  rw [div_mul_div_comm]
  rw [mul_comm ((1 / 2 : ℂ) - Complex.I * (t : ℂ)) ((1 / 2 : ℂ) + Complex.I * (t : ℂ))]
  exact div_self (mul_ne_zero h_num h_denom)

/-- 🏆 THEOREM 8: Apollonian ratio on the critical line coincides with the boundary S-matrix:
    $$\rho(1/2 + it) = S(t)$$ -/
theorem apollonian_ratio_critical_line (t : ℝ) :
    apollonianRatio (1 / 2 + Complex.I * (t : ℂ)) = boundarySMatrix t := by
  dsimp [apollonianRatio, boundarySMatrix]
  have h_sub : 1 - ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 1 / 2 - Complex.I * (t : ℂ) := by ring
  rw [h_sub]

/-- 🏆 THEOREM 9: Unitarity of the Apollonian ratio on the critical line:
    $$\|\rho(1/2 + it)\| = 1$$ -/
theorem apollonian_ratio_critical_line_norm (t : ℝ) :
    ‖apollonianRatio (1 / 2 + Complex.I * (t : ℂ))‖ = 1 := by
  rw [apollonian_ratio_critical_line t]
  exact boundary_s_matrix_unitary t

/-- 🏆 THEOREM 10: Equidistance degeneracy:
    For $s = \sigma + it$, $\|s\|^2 = \|1 - s\|^2 \iff \sigma = 1/2$. -/
theorem normSq_eq_normSq_iff_re_half (sigma t : ℝ) :
    let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
    Complex.normSq s = Complex.normSq (1 - s) ↔ sigma = 1 / 2 := by
  intro s
  dsimp [s]
  have h1 : Complex.normSq ((sigma : ℂ) + Complex.I * (t : ℂ)) = sigma ^ 2 + t ^ 2 := by
    have h_comm : (sigma : ℂ) + Complex.I * (t : ℂ) = (sigma : ℂ) + (t : ℂ) * Complex.I := by
      rw [mul_comm Complex.I]
    rw [h_comm, Complex.normSq_add_mul_I]
  have h_one_sub : (1 : ℂ) - ((sigma : ℂ) + Complex.I * (t : ℂ)) = ((1 - sigma : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h_one_sub]
  have h2 : Complex.normSq (((1 - sigma : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) = (1 - sigma) ^ 2 + t ^ 2 := by
    rw [Complex.normSq_add_mul_I]
    ring
  rw [h1, h2]
  constructor
  · intro h
    have h_sub : (sigma ^ 2 + t ^ 2) - ((1 - sigma) ^ 2 + t ^ 2) = 0 := by linarith
    have h_alg : (sigma ^ 2 + t ^ 2) - ((1 - sigma) ^ 2 + t ^ 2) = 2 * sigma - 1 := by ring
    rw [h_alg] at h_sub
    linarith
  · intro h
    rw [h]
    ring

/-- 🏆 MASTER CONJUNCTION: Certified Apollonius Bipolar Strip & Cayley Scattering Synthesis. -/
theorem certified_apollonius_cayley_scattering_synthesis (t : ℝ) :
    (‖boundarySMatrix t‖ = 1) ∧
    (boundarySMatrix 0 = 1) ∧
    (boundarySMatrix (-t) = starRingEnd ℂ (boundarySMatrix t)) ∧
    (boundarySMatrix t * boundarySMatrix (-t) = 1) ∧
    (apollonianRatio (1 / 2 + Complex.I * (t : ℂ)) = boundarySMatrix t) ∧
    (‖apollonianRatio (1 / 2 + Complex.I * (t : ℂ))‖ = 1) ∧
    (∀ sigma : ℝ, Complex.normSq ((sigma : ℂ) + Complex.I * (t : ℂ)) =
      Complex.normSq (1 - ((sigma : ℂ) + Complex.I * (t : ℂ))) ↔ sigma = 1 / 2) :=
  ⟨boundary_s_matrix_unitary t,
   boundary_s_matrix_zero,
   boundary_s_matrix_neg t,
   boundary_s_matrix_mul_neg t,
   apollonian_ratio_critical_line t,
   apollonian_ratio_critical_line_norm t,
   fun sigma => normSq_eq_normSq_iff_re_half sigma t⟩

#print axioms certified_apollonius_cayley_scattering_synthesis

end InfoGeometry.Physics.ApolloniusCayleyScattering
