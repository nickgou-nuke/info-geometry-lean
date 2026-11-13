/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel

/-!
# Triangular extensions of three-term module complexes

The maps `incoming` and `outgoing` are the block differentials
`(u,v) ↦ (d₂ u + a v, d₃ v)` and `(x,y) ↦ (d₁ x - b y, d₂ y)`.
Their compatibility is expressed in the noncommutative algebra of linear maps.
They form a native `ShortComplex (ModuleCat R)`. Exactness is transferred from
the two explicitly assumed adjacent kernel/range equalities.

The signed equations `a = d₂ ∘ G - H ∘ d₃` and
`b = Q ∘ d₂ - d₁ ∘ H` give invertible triangular coordinate changes and a
native short-complex isomorphism to the uncoupled complex. The resulting
homology isomorphism is the one supplied by mathlib's homology functor.

This is the algebraic construction underlying Construction 2 and the shear
calculation of Appendix G in Hao Song, arXiv:2608.09913v1. It does not prove
Koszul exactness from regularity, the dagger-dual sector, or a Clifford circuit.
-/

namespace InfoGeometry.TriangularShortComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [Ring R]
variable {K₀ K₁ K₂ K₃ : Type v}
variable [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup K₂] [AddCommGroup K₃]
variable [Module R K₀] [Module R K₁] [Module R K₂] [Module R K₃]

/-- The incoming differential of a triangular extension. -/
def incoming (d₂ : K₂ →ₗ[R] K₁) (d₃ : K₃ →ₗ[R] K₂) (a : K₃ →ₗ[R] K₁) :
    (K₂ × K₃) →ₗ[R] (K₁ × K₂) :=
  (d₂.coprod a).prod ((0 : K₂ →ₗ[R] K₂).coprod d₃)

/-- The outgoing differential, with the sign needed over an arbitrary ring. -/
def outgoing (d₁ : K₁ →ₗ[R] K₀) (d₂ : K₂ →ₗ[R] K₁) (b : K₂ →ₗ[R] K₀) :
    (K₁ × K₂) →ₗ[R] (K₀ × K₁) :=
  (d₁.coprod (-b)).prod ((0 : K₁ →ₗ[R] K₁).coprod d₂)

@[simp]
theorem incoming_apply (d₂ : K₂ →ₗ[R] K₁) (d₃ : K₃ →ₗ[R] K₂)
    (a : K₃ →ₗ[R] K₁) (p : K₂ × K₃) :
    incoming d₂ d₃ a p = (d₂ p.1 + a p.2, d₃ p.2) := by
  simp [incoming]

@[simp]
theorem outgoing_apply (d₁ : K₁ →ₗ[R] K₀) (d₂ : K₂ →ₗ[R] K₁)
    (b : K₂ →ₗ[R] K₀) (p : K₁ × K₂) :
    outgoing d₁ d₂ b p = (d₁ p.1 - b p.2, d₂ p.2) := by
  simp [outgoing, sub_eq_add_neg]

section Complex

variable (d₁ : K₁ →ₗ[R] K₀) (d₂ : K₂ →ₗ[R] K₁) (d₃ : K₃ →ₗ[R] K₂)
variable (a : K₃ →ₗ[R] K₁) (b : K₂ →ₗ[R] K₀)
variable (h₁₂ : d₁.comp d₂ = 0) (h₂₃ : d₂.comp d₃ = 0)
variable (hab : d₁.comp a = b.comp d₃)

include h₁₂ h₂₃ hab in
/-- The coupled differentials compose to zero when their off-diagonal blocks agree. -/
theorem incoming_outgoing :
    (outgoing d₁ d₂ b).comp (incoming d₂ d₃ a) = 0 := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  have h₁₂u : d₁ (d₂ u) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      congrArg (fun f : K₂ →ₗ[R] K₀ => f u) h₁₂
  have h₂₃v : d₂ (d₃ v) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      congrArg (fun f : K₃ →ₗ[R] K₁ => f v) h₂₃
  have habv : d₁ (a v) = b (d₃ v) := by
    simpa only [LinearMap.comp_apply] using
      congrArg (fun f : K₃ →ₗ[R] K₀ => f v) hab
  simp only [LinearMap.comp_apply, incoming_apply, outgoing_apply, LinearMap.zero_apply]
  apply Prod.ext
  · change d₁ (d₂ u + a v) - b (d₃ v) = 0
    rw [map_add, h₁₂u, zero_add, habv, sub_self]
  · exact h₂₃v

/-- The native module-category short complex of a compatible triangular extension. -/
def complex : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (incoming d₂ d₃ a) (outgoing d₁ d₂ b)
    (incoming_outgoing d₁ d₂ d₃ a b h₁₂ h₂₃ hab)

@[simp]
theorem complex_f_hom :
    (complex d₁ d₂ d₃ a b h₁₂ h₂₃ hab).f.hom = incoming d₂ d₃ a := rfl

@[simp]
theorem complex_g_hom :
    (complex d₁ d₂ d₃ a b h₁₂ h₂₃ hab).g.hom = outgoing d₁ d₂ b := rfl

/-- Adjacent exactness supplies an explicit preimage for every coupled cycle. -/
theorem exact
    (hExact₁ : LinearMap.range d₂ = LinearMap.ker d₁)
    (hExact₂ : LinearMap.range d₃ = LinearMap.ker d₂) :
    (complex d₁ d₂ d₃ a b h₁₂ h₂₃ hab).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  rintro ⟨x, y⟩ hxy
  change outgoing d₁ d₂ b (x, y) = 0 at hxy
  have hx : d₁ x - b y = 0 := by
    simpa using congrArg Prod.fst hxy
  have hy : d₂ y = 0 := by
    simpa using congrArg Prod.snd hxy
  have hyRange : y ∈ LinearMap.range d₃ := by
    rw [hExact₂, LinearMap.mem_ker]
    exact hy
  obtain ⟨v, hv⟩ := hyRange
  have habv : d₁ (a v) = b (d₃ v) := by
    simpa only [LinearMap.comp_apply] using
      congrArg (fun f : K₃ →ₗ[R] K₀ => f v) hab
  have hResidual : d₁ (x - a v) = 0 := by
    rw [map_sub, habv, hv]
    exact hx
  have hResidualRange : x - a v ∈ LinearMap.range d₂ := by
    rw [hExact₁, LinearMap.mem_ker]
    exact hResidual
  obtain ⟨u, hu⟩ := hResidualRange
  refine ⟨(u, v), ?_⟩
  change incoming d₂ d₃ a (u, v) = (x, y)
  simp only [incoming_apply, hu, hv, sub_add_cancel]

/-- The transferred exactness is vanishing of mathlib's native middle homology. -/
theorem homology_isZero
    (hExact₁ : LinearMap.range d₂ = LinearMap.ker d₁)
    (hExact₂ : LinearMap.range d₃ = LinearMap.ker d₂) :
    IsZero (complex d₁ d₂ d₃ a b h₁₂ h₂₃ hab).homology :=
  (ShortComplex.exact_iff_isZero_homology _).mp
    (exact d₁ d₂ d₃ a b h₁₂ h₂₃ hab hExact₁ hExact₂)

end Complex

section Shear

variable {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]

/-- An invertible upper-triangular change of coordinates on a product module. -/
def shear (f : Y →ₗ[R] X) : (X × Y) ≃ₗ[R] (X × Y) where
  toFun p := (p.1 + f p.2, p.2)
  invFun p := (p.1 - f p.2, p.2)
  left_inv p := by
    rcases p with ⟨x, y⟩
    simp
  right_inv p := by
    rcases p with ⟨x, y⟩
    simp
  map_add' p q := by
    apply Prod.ext
    · change (p.1 + q.1) + f (p.2 + q.2) = (p.1 + f p.2) + (q.1 + f q.2)
      rw [map_add]
      abel
    · rfl
  map_smul' r p := by
    apply Prod.ext
    · change r • p.1 + f (r • p.2) = r • (p.1 + f p.2)
      rw [map_smul, smul_add]
    · rfl

@[simp]
theorem shear_apply (f : Y →ₗ[R] X) (p : X × Y) :
    shear f p = (p.1 + f p.2, p.2) := rfl

@[simp]
theorem shear_symm_apply (f : Y →ₗ[R] X) (p : X × Y) :
    (shear f).symm p = (p.1 - f p.2, p.2) := rfl

/-- Negating the off-diagonal map inverts the shear. -/
theorem shear_symm (f : Y →ₗ[R] X) : (shear f).symm = shear (-f) := by
  apply LinearEquiv.ext
  intro p
  apply Prod.ext
  · change p.1 - f p.2 = p.1 + (-f) p.2
    simp only [LinearMap.neg_apply, sub_eq_add_neg]
  · rfl

end Shear

section Splitting

variable (d₁ : K₁ →ₗ[R] K₀) (d₂ : K₂ →ₗ[R] K₁) (d₃ : K₃ →ₗ[R] K₂)
variable (a : K₃ →ₗ[R] K₁) (b : K₂ →ₗ[R] K₀)
variable (h₁₂ : d₁.comp d₂ = 0) (h₂₃ : d₂.comp d₃ = 0)
variable (hab : d₁.comp a = b.comp d₃)
variable (G : K₃ →ₗ[R] K₂) (H : K₂ →ₗ[R] K₁) (Q : K₁ →ₗ[R] K₀)
variable (ha : a = d₂.comp G - H.comp d₃)
variable (hb : b = Q.comp d₂ - d₁.comp H)

include h₁₂ h₂₃ ha hb in
/-- The signed splitting equations themselves imply compatibility of the coupling. -/
theorem compatible_of_splitting : d₁.comp a = b.comp d₃ := by
  apply LinearMap.ext
  intro v
  have h₁₂Gv : d₁ (d₂ (G v)) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      congrArg (fun f : K₂ →ₗ[R] K₀ => f (G v)) h₁₂
  have h₂₃v : d₂ (d₃ v) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      congrArg (fun f : K₃ →ₗ[R] K₁ => f v) h₂₃
  simp only [LinearMap.comp_apply, ha, hb, LinearMap.sub_apply, map_sub]
  rw [h₁₂Gv, h₂₃v, map_zero]

include ha in
/-- The source and middle shears remove the incoming off-diagonal block. -/
theorem shear_incoming :
    (shear H).toLinearMap.comp (incoming d₂ d₃ a) =
      (incoming d₂ d₃ 0).comp (shear G).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  have hav : a v = d₂ (G v) - H (d₃ v) := by
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply] using
      congrArg (fun f : K₃ →ₗ[R] K₁ => f v) ha
  change shear H (incoming d₂ d₃ a (u, v)) = incoming d₂ d₃ 0 (shear G (u, v))
  simp only [incoming_apply, shear_apply]
  apply Prod.ext
  · change (d₂ u + a v) + H (d₃ v) = d₂ (u + G v) + 0
    rw [hav, map_add]
    abel
  · rfl

include hb in
/-- The middle and target shears remove the outgoing off-diagonal block. -/
theorem shear_outgoing :
    (shear Q).toLinearMap.comp (outgoing d₁ d₂ b) =
      (outgoing d₁ d₂ 0).comp (shear H).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hby : b y = Q (d₂ y) - d₁ (H y) := by
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply] using
      congrArg (fun f : K₂ →ₗ[R] K₀ => f y) hb
  change shear Q (outgoing d₁ d₂ b (x, y)) = outgoing d₁ d₂ 0 (shear H (x, y))
  simp only [outgoing_apply, shear_apply]
  apply Prod.ext
  · change (d₁ x - b y) + Q (d₂ y) = d₁ (x + H y) - 0
    rw [hby, map_add]
    abel
  · rfl

/-- The shears give an isomorphism of the coupled and uncoupled native short complexes. -/
def splittingIso :
    complex d₁ d₂ d₃ a b h₁₂ h₂₃ hab ≅
      complex d₁ d₂ d₃ 0 0 h₁₂ h₂₃ (by simp) := by
  refine ShortComplex.isoMk (shear G).toModuleIso (shear H).toModuleIso
    (shear Q).toModuleIso ?_ ?_
  · apply ModuleCat.hom_ext
    exact (shear_incoming d₂ d₃ a G H ha).symm
  · apply ModuleCat.hom_ext
    exact (shear_outgoing d₁ d₂ b H Q hb).symm

/-- The splitting induces mathlib's functorial isomorphism on middle homology. -/
noncomputable def splittingHomologyIso :
    (complex d₁ d₂ d₃ a b h₁₂ h₂₃ hab).homology ≅
      (complex d₁ d₂ d₃ 0 0 h₁₂ h₂₃ (by simp)).homology :=
  ShortComplex.homologyMapIso
    (splittingIso d₁ d₂ d₃ a b h₁₂ h₂₃ hab G H Q ha hb)

/-- The same native homology isomorphism, exposed as an equivalence of modules. -/
noncomputable def splittingHomologyLinearEquiv :
    (complex d₁ d₂ d₃ a b h₁₂ h₂₃ hab).homology ≃ₗ[R]
      (complex d₁ d₂ d₃ 0 0 h₁₂ h₂₃ (by simp)).homology :=
  (splittingHomologyIso d₁ d₂ d₃ a b h₁₂ h₂₃ hab G H Q ha hb).toLinearEquiv

end Splitting

end InfoGeometry.TriangularShortComplex
