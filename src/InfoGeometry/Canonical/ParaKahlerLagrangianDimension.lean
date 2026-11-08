/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Epistemology.SubmersionSplitFinrank
import InfoGeometry.Canonical.GrandEpistemicGeometricSynthesis

/-!
# Lagrangian half-dimension for para-Kähler structures

For a nondegenerate para-Kähler structure `(g, ω, K)` on a finite-dimensional real
vector space `V`, the two eigen-sheets `range P⁺` and `range P⁻` are totally
`g`-isotropic and complementary, hence each has dimension exactly `finrank V / 2`.

* `tplus_isotropic`, `tminus_isotropic`: full (bilinear) isotropy of `T^±`.
* `finrank_le_of_isotropic_sup_eq_top`: an isotropic summand of a spanning pair has
  dimension at most that of its partner (cross pairing is injective).
* `finrank_range_plus_eq_minus`, `two_mul_finrank_range_plus`, `even_finrank`.
* `swapParaKahler`, `swapG_nondegenerate`: a concrete nondegenerate witness on `Fin 2 → ℝ`.
-/

namespace InfoGeometry.Canonical.ParaKahlerLagrangianDimension

open InfoGeometry.Canonical.SuperGrassmannianManifold
open InfoGeometry.Canonical.NaturalGradientSubmersionFlow
open InfoGeometry.Epistemology.SubmersionSplitFinrank
open InfoGeometry.Canonical.GrandEpistemicGeometricSynthesis

section Isotropy

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `T^+` is totally isotropic for `g`. -/
theorem tplus_isotropic {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    {v w : V} (hv : InTPlus K v) (hw : InTPlus K w) : g v w = 0 := by
  have h := metric_anti_invariance g omega K hK hPK v w
  rw [show K v = v from hv, show K w = w from hw] at h
  linarith

/-- `T^-` is totally isotropic for `g`. -/
theorem tminus_isotropic {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    {v w : V} (hv : InTMinus K v) (hw : InTMinus K w) : g v w = 0 := by
  have h := metric_anti_invariance g omega K hK hPK v w
  rw [show K v = -v from hv, show K w = -w from hw] at h
  simp only [map_neg, LinearMap.neg_apply, neg_neg] at h
  linarith

/-- Every element of `range P⁺` lies in `T^+`. -/
theorem inTPlus_of_mem_range {K : V →ₗ[ℝ] V} (hK : ParaComplexStructure K) {v : V}
    (hv : v ∈ LinearMap.range (paraProjectorPlus K)) : InTPlus K v := by
  obtain ⟨x, rfl⟩ := hv
  exact paraProjectorPlus_in_TPlus K hK x

/-- Every element of `range P⁻` lies in `T^-`. -/
theorem inTMinus_of_mem_range {K : V →ₗ[ℝ] V} (hK : ParaComplexStructure K) {v : V}
    (hv : v ∈ LinearMap.range (paraProjectorMinus K)) : InTMinus K v := by
  obtain ⟨x, rfl⟩ := hv
  exact paraProjectorMinus_in_TMinus K hK x

/-- `range P⁺` is totally isotropic. -/
theorem range_plus_isotropic {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) :
    ∀ v ∈ LinearMap.range (paraProjectorPlus K),
      ∀ w ∈ LinearMap.range (paraProjectorPlus K), g v w = 0 :=
  fun _ hv _ hw => tplus_isotropic hK hPK (inTPlus_of_mem_range hK hv)
    (inTPlus_of_mem_range hK hw)

/-- `range P⁻` is totally isotropic. -/
theorem range_minus_isotropic {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) :
    ∀ v ∈ LinearMap.range (paraProjectorMinus K),
      ∀ w ∈ LinearMap.range (paraProjectorMinus K), g v w = 0 :=
  fun _ hv _ hw => tminus_isotropic hK hPK (inTMinus_of_mem_range hK hv)
    (inTMinus_of_mem_range hK hw)

end Isotropy

section CrossPairing

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The cross pairing `A → Dual B`, `a ↦ (b ↦ g a b)`, is injective when `A` is isotropic,
`A ⊔ B = ⊤`, and `g` is nondegenerate. -/
theorem crossPairing_injective (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) {A B : Submodule ℝ V}
    (hiso : ∀ a ∈ A, ∀ a' ∈ A, g a a' = 0) (hspan : A ⊔ B = ⊤) :
    Function.Injective (g.domRestrict₁₂ A B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  apply Subtype.ext
  apply hnd
  intro x
  have hx : x ∈ A ⊔ B := hspan ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have hz0 : g a z = 0 := LinearMap.congr_fun ha ⟨z, hz⟩
  rw [map_add, hiso a a.2 y hy, hz0, add_zero]

/-- An isotropic summand of a spanning pair has dimension at most that of its partner. -/
theorem finrank_le_of_isotropic_sup_eq_top [FiniteDimensional ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0)
    {A B : Submodule ℝ V} (hiso : ∀ a ∈ A, ∀ a' ∈ A, g a a' = 0) (hspan : A ⊔ B = ⊤) :
    Module.finrank ℝ A ≤ Module.finrank ℝ B := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (crossPairing_injective g hnd hiso hspan)
  rwa [Subspace.dual_finrank_eq] at h

/-- The two eigen-sheet ranges span `V`. -/
lemma range_plus_sup_range_minus {K : V →ₗ[ℝ] V} (hK : ParaComplexStructure K) :
    LinearMap.range (paraProjectorPlus K) ⊔ LinearMap.range (paraProjectorMinus K) = ⊤ :=
  (isCompl_range_projH_range_projV (paraComplexSubmersionSplit K hK)).sup_eq_top

end CrossPairing

section HalfDimension

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}

/-- `finrank (range P⁺) ≤ finrank (range P⁻)`. -/
theorem finrank_range_plus_le (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    Module.finrank ℝ (LinearMap.range (paraProjectorPlus K)) ≤
      Module.finrank ℝ (LinearMap.range (paraProjectorMinus K)) :=
  finrank_le_of_isotropic_sup_eq_top g hnd (range_plus_isotropic hK hPK)
    (range_plus_sup_range_minus hK)

/-- `finrank (range P⁻) ≤ finrank (range P⁺)`. -/
theorem finrank_range_minus_le (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    Module.finrank ℝ (LinearMap.range (paraProjectorMinus K)) ≤
      Module.finrank ℝ (LinearMap.range (paraProjectorPlus K)) :=
  finrank_le_of_isotropic_sup_eq_top g hnd (range_minus_isotropic hK hPK)
    (by rw [sup_comm]; exact range_plus_sup_range_minus hK)

/-- Headline: the two Lagrangian sheets have equal dimension. -/
theorem finrank_range_plus_eq_minus (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    Module.finrank ℝ (LinearMap.range (paraProjectorPlus K)) =
      Module.finrank ℝ (LinearMap.range (paraProjectorMinus K)) :=
  le_antisymm (finrank_range_plus_le hK hPK hnd) (finrank_range_minus_le hK hPK hnd)

/-- Headline: each Lagrangian sheet has half the dimension of `V`. -/
theorem two_mul_finrank_range_plus (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    2 * Module.finrank ℝ (LinearMap.range (paraProjectorPlus K)) = Module.finrank ℝ V := by
  rw [finrank_paraComplex_split K hK, ← finrank_range_plus_eq_minus hK hPK hnd, two_mul]

/-- Corollary: a nondegenerate para-Kähler space has even dimension. -/
theorem even_finrank (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    Even (Module.finrank ℝ V) :=
  ⟨_, (two_mul_finrank_range_plus hK hPK hnd).symm.trans (two_mul _)⟩

end HalfDimension

section Witness

private lemma swapG_symmetric_formula (v w : Fin 2 → ℝ) :
    v 0 * w 0 - v 1 * w 1 = w 0 * v 0 - w 1 * v 1 := by ring

private lemma swapOmega_skew_formula (v w : Fin 2 → ℝ) :
    v 0 * w 1 - v 1 * w 0 = -(w 0 * v 1 - w 1 * v 0) := by ring

private lemma swapOmega_anti_invariant_formula (v w : Fin 2 → ℝ) :
    v 1 * w 0 - v 0 * w 1 = -(v 0 * w 1 - v 1 * w 0) := by ring

private lemma swapG_add_left_formula (u v w : Fin 2 → ℝ) :
    (u 0 + v 0) * w 0 - (u 1 + v 1) * w 1 =
      (u 0 * w 0 - u 1 * w 1) + (v 0 * w 0 - v 1 * w 1) := by ring

private lemma swapG_smul_left_formula (c : ℝ) (u v : Fin 2 → ℝ) :
    (c * u 0) * v 0 - (c * u 1) * v 1 = c * (u 0 * v 0 - u 1 * v 1) := by ring

private lemma swapG_add_right_formula (u v w : Fin 2 → ℝ) :
    u 0 * (v 0 + w 0) - u 1 * (v 1 + w 1) =
      (u 0 * v 0 - u 1 * v 1) + (u 0 * w 0 - u 1 * w 1) := by ring

private lemma swapG_smul_right_formula (c : ℝ) (u v : Fin 2 → ℝ) :
    u 0 * (c * v 0) - u 1 * (c * v 1) = c * (u 0 * v 0 - u 1 * v 1) := by ring

private lemma swapOmega_add_left_formula (u v w : Fin 2 → ℝ) :
    (u 0 + v 0) * w 1 - (u 1 + v 1) * w 0 =
      (u 0 * w 1 - u 1 * w 0) + (v 0 * w 1 - v 1 * w 0) := by ring

private lemma swapOmega_smul_left_formula (c : ℝ) (u v : Fin 2 → ℝ) :
    (c * u 0) * v 1 - (c * u 1) * v 0 = c * (u 0 * v 1 - u 1 * v 0) := by ring

private lemma swapOmega_add_right_formula (u v w : Fin 2 → ℝ) :
    u 0 * (v 1 + w 1) - u 1 * (v 0 + w 0) =
      (u 0 * v 1 - u 1 * v 0) + (u 0 * w 1 - u 1 * w 0) := by ring

private lemma swapOmega_smul_right_formula (c : ℝ) (u v : Fin 2 → ℝ) :
    u 0 * (c * v 1) - u 1 * (c * v 0) = c * (u 0 * v 1 - u 1 * v 0) := by ring

/-- Split metric `g(u, v) = u₀ v₀ - u₁ v₁` on `Fin 2 → ℝ`. -/
noncomputable def swapG : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => u 0 * v 0 - u 1 * v 1)
    (fun u v w => by simp only [Pi.add_apply]; exact swapG_add_left_formula u v w)
    (fun c u v => by simp only [Pi.smul_apply, smul_eq_mul]; exact swapG_smul_left_formula c u v)
    (fun u v w => by simp only [Pi.add_apply]; exact swapG_add_right_formula u v w)
    (fun c u v => by simp only [Pi.smul_apply, smul_eq_mul]; exact swapG_smul_right_formula c u v)

/-- Symplectic form `ω(u, v) = u₀ v₁ - u₁ v₀` on `Fin 2 → ℝ`. -/
noncomputable def swapOmega : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => u 0 * v 1 - u 1 * v 0)
    (fun u v w => by simp only [Pi.add_apply]; exact swapOmega_add_left_formula u v w)
    (fun c u v => by simp only [Pi.smul_apply, smul_eq_mul]; exact swapOmega_smul_left_formula c u v)
    (fun u v w => by simp only [Pi.add_apply]; exact swapOmega_add_right_formula u v w)
    (fun c u v => by simp only [Pi.smul_apply, smul_eq_mul]; exact swapOmega_smul_right_formula c u v)

lemma swapK_apply_zero (v : Fin 2 → ℝ) : swapK v 0 = v 1 := by
  simp [swapK, LinearMap.funLeft_apply]

lemma swapK_apply_one (v : Fin 2 → ℝ) : swapK v 1 = v 0 := by
  simp [swapK, LinearMap.funLeft_apply]

/-- `(swapG, swapOmega, swapK)` is a para-Kähler structure. -/
theorem swapParaKahler : ParaKahlerStructure swapG swapOmega swapK where
  g_symm v w := by simpa only [swapG, LinearMap.mk₂_apply] using swapG_symmetric_formula v w
  omega_skew v w := by simpa only [swapOmega, LinearMap.mk₂_apply] using swapOmega_skew_formula v w
  compatibility v w := by
    simp only [swapG, swapOmega, LinearMap.mk₂_apply, swapK_apply_zero, swapK_apply_one]
  omega_anti_inv v w := by
    simp only [swapOmega, LinearMap.mk₂_apply, swapK_apply_zero, swapK_apply_one]
    exact swapOmega_anti_invariant_formula v w

/-- `swapG` is nondegenerate. -/
theorem swapG_nondegenerate : ∀ v, (∀ w, swapG v w = 0) → v = 0 := by
  intro v hv
  have h0 := hv (Pi.single 0 1)
  have h1 := hv (Pi.single 1 1)
  simp [swapG] at h0 h1
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Non-vacuity: the headline applies to the swap witness. -/
theorem swap_two_mul_finrank_range_plus :
    2 * Module.finrank ℝ (LinearMap.range (paraProjectorPlus swapK)) =
      Module.finrank ℝ (Fin 2 → ℝ) :=
  two_mul_finrank_range_plus swapK_paraComplex swapParaKahler swapG_nondegenerate

end Witness

end InfoGeometry.Canonical.ParaKahlerLagrangianDimension
