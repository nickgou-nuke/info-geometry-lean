import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Complex

/-!
# Zeta Beta-Coordinate, Cayley Reflection, and Half-Period Klein Glide

This file formalizes the algebraic dictionary connecting:
1. The Klein four-group on the β = 2s coordinate:
   - F(β) = 2 - β (functional reflection)
   - C(β) = conj(β) (complex conjugation)
   - R(β) = 2 - conj(β) (critical-line reflection, fixed locus Re(β) = 1).
2. The Cayley transform z = β / (2 - β):
   - F(z) = 1 / z
   - C(z) = conj(z)
   - R(z) = 1 / conj(z) (fixed locus |z| = 1, the unit circle / critical line).
3. The half-period twisted glide reflection τ(z) = -1 / conj(z):
   - Involutive: τ² = id
   - Free (strictly fixed-point-free): τ(z) ≠ z for all z ∈ ℂ \ {0}.
   - Induces the Klein bottle quotient structure on the complex torus.
-/

namespace InfoGeometry.Arithmetic.ZetaBetaCayleyKleinBridge

/-! ## 1. The Klein Four-Group on the Beta Coordinate -/

/-- Functional equation reflection: β ↦ 2 - β -/
def F_beta (β : ℂ) : ℂ := 2 - β

/-- Complex conjugation: β ↦ conj(β) -/
def C_beta (β : ℂ) : ℂ := star β

/-- Antiunitary reflection across the critical line: β ↦ 2 - conj(β) -/
def R_beta (β : ℂ) : ℂ := 2 - star β

@[simp]
theorem F_beta_involutive (β : ℂ) : F_beta (F_beta β) = β := by
  dsimp [F_beta]
  ring

@[simp]
theorem C_beta_involutive (β : ℂ) : C_beta (C_beta β) = β := by
  dsimp [C_beta]
  exact star_star β

@[simp]
theorem R_beta_involutive (β : ℂ) : R_beta (R_beta β) = β := by
  dsimp [R_beta]
  have hstar2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by apply Complex.ext <;> simp
  simp [star_sub, hstar2]

theorem F_comp_C (β : ℂ) : F_beta (C_beta β) = R_beta β := by
  dsimp [F_beta, C_beta, R_beta]

theorem C_comp_F (β : ℂ) : C_beta (F_beta β) = R_beta β := by
  dsimp [F_beta, C_beta, R_beta]
  have hstar2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by apply Complex.ext <;> simp
  simp [star_sub, hstar2]

/-- The antiunitary reflection fixes exactly the critical line Re(β) = 1. -/
theorem R_beta_fixed_iff (β : ℂ) : R_beta β = β ↔ β.re = 1 := by
  simp [R_beta]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  · intro hre
    apply Complex.ext
    · dsimp [R_beta]; rw [hre]; ring
    · dsimp [R_beta]; simp

/-! ## 2. The Cayley Transform and Inversion -/

/-- The Cayley coordinate: z = β / (2 - β) -/
noncomputable def betaToCayley (β : ℂ) : ℂ := β / (2 - β)

/-- The inverse Cayley coordinate: β = 2z / (1 + z) -/
noncomputable def cayleyToBeta (z : ℂ) : ℂ := (2 * z) / (1 + z)

theorem cayleyToBeta_betaToCayley (β : ℂ) (hβ : 2 - β ≠ 0) :
    cayleyToBeta (betaToCayley β) = β := by
  unfold cayleyToBeta betaToCayley
  field_simp [hβ]
  ring

theorem betaToCayley_cayleyToBeta (z : ℂ) (hz : 1 + z ≠ 0) :
    betaToCayley (cayleyToBeta z) = z := by
  unfold betaToCayley cayleyToBeta
  field_simp [hz]
  ring

theorem betaToCayley_F (β : ℂ) :
    betaToCayley (F_beta β) = (betaToCayley β)⁻¹ := by
  unfold betaToCayley F_beta
  have h2 : 2 - (2 - β) = β := by ring
  rw [h2]
  exact (inv_div β (2 - β)).symm

theorem betaToCayley_C (β : ℂ) :
    betaToCayley (C_beta β) = star (betaToCayley β) := by
  unfold betaToCayley C_beta
  have hstar2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by apply Complex.ext <;> simp
  dsimp
  simp [star_sub, hstar2]

theorem betaToCayley_R (β : ℂ) :
    betaToCayley (R_beta β) = (star (betaToCayley β))⁻¹ := by
  unfold betaToCayley R_beta
  have hstar2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by apply Complex.ext <;> simp
  have h2 : 2 - (2 - star β) = star β := by ring
  rw [h2]
  have hstar : star (β / (2 - β)) = star β / (2 - star β) := by
    simp [star_sub, hstar2]
  rw [hstar]
  exact (inv_div (star β) (2 - star β)).symm

/-- The completed-zeta circle reflection on the Cayley plane: R(z) = 1 / conj(z) -/
noncomputable def cayleyR (z : ℂ) : ℂ := (star z)⁻¹

/-- The completed-zeta reflection fixes precisely the unit circle |z| = 1. -/
theorem cayleyR_fixed_iff (z : ℂ) (hz : z ≠ 0) :
    cayleyR z = z ↔ normSq z = 1 := by
  unfold cayleyR
  have hnorm : (normSq z : ℂ) = star z * z := normSq_eq_conj_mul_self
  constructor
  · intro h
    have h2 : star z * z = 1 := by
      nth_rw 2 [← h]
      exact mul_inv_cancel₀ (star_ne_zero.mpr hz)
    have h3 : (normSq z : ℂ) = 1 := by
      rw [hnorm]
      exact h2
    exact ofReal_injective (by simpa using h3)
  · intro h
    have h2 : star z * z = 1 := by
      rw [← hnorm]
      exact ofReal_inj.mpr h
    have h3 : z = (star z)⁻¹ := eq_inv_of_mul_eq_one_right h2
    exact h3.symm

/-! ## 3. The Half-Period Twisted Glide Reflection and Free Involution -/

/-- The half-period twisted glide reflection: τ(z) = -1 / conj(z) -/
noncomputable def tauGlide (z : ℂ) : ℂ := - (star z)⁻¹

/-- τ is an involution on ℂ \ {0}. -/
@[simp]
theorem tauGlide_involutive (z : ℂ) :
    tauGlide (tauGlide z) = z := by
  unfold tauGlide
  simp

/-- THEOREM: τ is strictly fixed-point-free (a genuine free involution). -/
theorem tauGlide_no_fixed_points (z : ℂ) (hz : z ≠ 0) :
    tauGlide z ≠ z := by
  intro h
  unfold tauGlide at h
  have hneg : (star z)⁻¹ = -z := by
    calc (star z)⁻¹ = - (- (star z)⁻¹) := by ring
    _ = -z := by rw [h]
  have h2 : (1 : ℂ) = - (star z * z) := by
    calc (1 : ℂ) = star z * (star z)⁻¹ := (mul_inv_cancel₀ (star_ne_zero.mpr hz)).symm
    _ = star z * -z := by rw [hneg]
    _ = - (star z * z) := by ring
  have hnorm : (normSq z : ℂ) = star z * z := normSq_eq_conj_mul_self
  have h3 : (1 : ℂ) = - (normSq z : ℂ) := by
    rw [hnorm]
    exact h2
  have hreal : (1 : ℝ) = - normSq z := by
    have := congrArg Complex.re h3
    simpa using this
  have hpos : 0 ≤ normSq z := normSq_nonneg z
  linarith

/-- The orbit relation induced by the free involution τ. -/
def tauOrbitRel (z w : ℂ) : Prop :=
  z = w ∨ z = tauGlide w

theorem tauOrbitRel_refl (z : ℂ) : tauOrbitRel z z := Or.inl rfl

theorem tauOrbitRel_symm {z w : ℂ} (h : tauOrbitRel z w) : tauOrbitRel w z := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    rw [h, tauGlide_involutive]

theorem tauOrbitRel_trans {z w v : ℂ} (h1 : tauOrbitRel z w) (h2 : tauOrbitRel w v) :
    tauOrbitRel z v := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · left
      rw [h1, h2, tauGlide_involutive]

theorem tauOrbitRel_is_equivalence : Equivalence tauOrbitRel := by
  exact ⟨fun z => tauOrbitRel_refl z, fun h => tauOrbitRel_symm h, fun h1 h2 => tauOrbitRel_trans h1 h2⟩

end InfoGeometry.Arithmetic.ZetaBetaCayleyKleinBridge
