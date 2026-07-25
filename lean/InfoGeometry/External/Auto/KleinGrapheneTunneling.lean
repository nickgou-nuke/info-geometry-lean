import Mathlib.Tactic

/-!
# Klein paradox and graphene Klein tunneling

Digest source: `/home/goutev/Desktop/symmetry/par/klein1.pdf`,
Hua Chen, *Klein Paradox and Graphene*.

The paper reviews:

* the corrected single-particle Dirac step-potential calculation, where current
  conservation gives `R+T=1` but the infinite-barrier limit still has nonzero
  transmission;
* graphene low-energy carriers obeying a 2+1D massless Dirac/Weyl equation;
* graphene barrier transmission with perfect normal-incidence Klein tunneling.

This file formalizes the algebraic cores and keeps interpretive physics in comments.
-/

noncomputable section

namespace KleinGrapheneTunneling

open Matrix

/-! ## 1D Klein step coefficients -/

/-- Corrected infinite-barrier reflection coefficient of the 1D Dirac step. -/
def RstepInf (E p : ℝ) : ℝ := (E - p) / (E + p)

/-- Corrected infinite-barrier transmission coefficient of the 1D Dirac step. -/
def TstepInf (E p : ℝ) : ℝ := (2 * p) / (E + p)

/-- Current conservation in the corrected step calculation. -/
theorem RstepInf_add_TstepInf (E p : ℝ) (h : E + p ≠ 0) :
    RstepInf E p + TstepInf E p = 1 := by
  unfold RstepInf TstepInf
  field_simp [h]
  ring

/-- Nonzero Klein transmission in the infinite-barrier limit, for nonzero momentum. -/
theorem TstepInf_nonzero (E p : ℝ) (hp : p ≠ 0) (hden : E + p ≠ 0) :
    TstepInf E p ≠ 0 := by
  unfold TstepInf
  exact div_ne_zero (mul_ne_zero two_ne_zero hp) hden

/-! ## Graphene massless Dirac cone -/

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

def σx : M2C := !![0, 1; 1, 0]
def σy : M2C := !![0, -Complex.I; Complex.I, 0]

/-- Graphene Weyl Hamiltonian `v_F(k_x σ_x+k_y σ_y)`. -/
def grapheneH (vF kx ky : ℂ) : M2C := vF • (kx • σx + ky • σy)

/-- Pauli cone determinant: `det(H)=-v_F²(k_x²+k_y²)`. -/
theorem grapheneH_det (vF kx ky : ℂ) :
    (grapheneH vF kx ky).det = -(vF^2 * (kx^2 + ky^2)) := by
  simp [grapheneH, σx, σy, Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The shifted characteristic determinant is `λ²-v_F²|k|²`. -/
theorem grapheneH_char_det (lam vF kx ky : ℂ) :
    ((lam • (1 : M2C)) - grapheneH vF kx ky).det = lam^2 - vF^2 * (kx^2 + ky^2) := by
  simp [grapheneH, σx, σy, Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Barrier transmission algebra -/

/-- Graphene barrier transmission written in scalar trigonometric variables.
`C=cos(Dq_x)`, `S=sin(Dq_x)`, and `cφ=cos φ`, `sφ=sin φ`, etc. -/
def Tgraphene (cθ cφ sθ sφ C S : ℝ) : ℝ :=
  (cθ^2 * cφ^2) / (C^2 * cφ^2 * cθ^2 + S^2 * (1 + sφ * sθ)^2)

/-- Normal incidence reduces the formula to `1/(C²+S²)`. -/
theorem Tgraphene_normal_form (C S : ℝ) :
    Tgraphene 1 1 0 0 C S = 1 / (C^2 + S^2) := by
  unfold Tgraphene
  ring_nf

/-- With the trig identity `C²+S²=1`, normal incidence is perfectly transmitting. -/
theorem Tgraphene_normal_perfect (C S : ℝ) (htrig : C^2 + S^2 = 1) :
    Tgraphene 1 1 0 0 C S = 1 := by
  rw [Tgraphene_normal_form, htrig]
  norm_num

/-- Resonance `sin(Dq_x)=0`, `cos(Dq_x)^2=1` gives perfect transmission away from zero numerator. -/
theorem Tgraphene_resonance_perfect
    (cθ cφ sθ sφ C : ℝ) (hC : C^2 = 1) (hn : cθ * cφ ≠ 0) :
    Tgraphene cθ cφ sθ sφ C 0 = 1 := by
  have hcθ : cθ ≠ 0 := by
    intro h
    apply hn
    simp [h]
  have hcφ : cφ ≠ 0 := by
    intro h
    apply hn
    simp [h]
  unfold Tgraphene
  simp [hC]
  field_simp [hcθ, hcφ]

/-- Infinite-barrier expression from the review. -/
def TgrapheneInf (cφ sφ C : ℝ) : ℝ := cφ^2 / (1 - C^2 * sφ^2)

/-- Infinite-barrier graphene formula is perfectly transmitting at normal incidence. -/
theorem TgrapheneInf_normal (C : ℝ) : TgrapheneInf 1 0 C = 1 := by
  unfold TgrapheneInf
  norm_num

/-- Infinite-barrier resonant case is perfectly transmitting using `cos²φ+sin²φ=1`. -/
theorem TgrapheneInf_resonance
    (cφ sφ C : ℝ) (hC : C^2 = 1) (hφ : cφ^2 + sφ^2 = 1) (hden : 1 - C^2 * sφ^2 ≠ 0) :
    TgrapheneInf cφ sφ C = 1 := by
  unfold TgrapheneInf
  have hden' : 1 - sφ^2 ≠ 0 := by simpa [hC] using hden
  rw [hC]
  have hc : cφ^2 = 1 - sφ^2 := by linarith
  rw [hc]
  convert div_self hden' using 1
  ring

#check RstepInf_add_TstepInf
#check grapheneH_char_det
#check Tgraphene_normal_perfect

end KleinGrapheneTunneling
