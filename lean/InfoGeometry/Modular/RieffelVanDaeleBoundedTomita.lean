/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealTomitaStandardSubspace
import InfoGeometry.Canonical.TomitaTakesakiRealStandardForm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Rieffel–van Daele Bounded Operator Theory for Standard Real Subspaces (`TT-F1A`)

This module develops the bounded-operator approach to Tomita–Takesaki theory for a
standard real subspace `K` of a complex Hilbert space `H`, following:

* Alfons van Daele, *"A new approach to the Tomita–Takesaki theory of generalized
  Hilbert algebras"*, *J. Funct. Anal.* **15** (1974), 378–393.
* Marc A. Rieffel and Alfons van Daele, *"A bounded operator approach to Tomita–Takesaki
  theory"*, *Pacific J. Math.* **69** (1977), no. 1, 187–221.

## Mathematical Summary

Viewing a complex Hilbert space `H` as a real Hilbert space with inner product
`⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re`, let `P_K` (`projK K`) and `P_{iK}` (`projIK K`) denote
the orthogonal projections onto a closed real subspace `K` and its rotated partner
`iK = ImaginarySubmodule K`. The fundamental bounded Rieffel–van Daele operators are:

* `rvdR K = P_K + P_{iK}`: bounded, self-adjoint, `0 ≤ R ≤ 2`, commuting with `i`
  (hence `ℂ`-linear), injective with dense range when `K` is standard (`K ⊓ iK = ⊥`
  and `K ⊔ iK` dense), as is `2 - R`.
* `rvdT K = P_K - P_{iK}`: bounded, self-adjoint, `‖T‖ ≤ 1`, anticommuting with `i`
  (hence `ℂ`-antilinear), satisfying `T² = R (2 - R)` and `R T = T (2 - R)`.
* Bridge to `TomitaOnStandard`: on `K ⊔ iK`, `T (S z) = (2 - R) z` and
  `(2 - R) (S z) = T z`, encoding `S = (2 - R)⁻¹ T` without unbounded operators.
* Symplectic complement `K' = (iK)ᗮ` and antiunitary involution `J` (`J K = K'`):
  `J R J = 2 - R` and `J T J = T`, plus invertibility of `1 + α R` and
  `1 + α (2 - R)` for `α ≥ 0`.

## Scope and Track Separation (`TT-F1A` vs `TT-F1B` vs `TT-F5`)

* **Bounded-vs-unbounded boundary**: This module stays strictly within bounded
  real-linear operators (`R`, `T`, `(1 + α R)⁻¹`, `J`-conjugation) and the algebraic
  `TomitaOnStandard` domain `K ⊔ iK`. Spectral extraction of `Δ^{it}` via Borel
  functional calculus belongs to `TT-F5` / infinite-dimensional spectral theory.
* **Track separation**: `TT-F1A` (this file) is strictly separate from `TT-F1B`
  (`FilteredGNSTomitaFormResolvent` / `FilteredGNSTomitaFriedrichsResolvent`), which
  constructs `(1 + Δ)⁻¹` from the closed GNS Tomita graph form.
* **Diamond-free realification**: No global or `scoped` `InnerProductSpace ℝ H`
  instance is registered here; `InnerProductSpace.rclikeToReal ℂ H` is introduced
  locally via `let` / `letI` when real Hilbert-space projections or adjoints are needed.
-/

noncomputable section

namespace InfoGeometry.Modular.RieffelVanDaeleBoundedTomita

open InfoGeometry.Canonical.RealTomitaStandardSubspace
open scoped InnerProductSpace

section IMapSection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Continuous real-linear `i`-multiplication operator `x ↦ i • x` on a complex
inner product space `H`. -/
def IMapCLM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : H →L[ℝ] H where
  toLinearMap := IMap H
  cont := (continuous_const_smul (Complex.I : ℂ)).comp continuous_id

@[simp]
theorem IMapCLM_apply (x : H) : IMapCLM H x = IMap H x := rfl

@[simp]
theorem IMap_norm (x : H) : ‖IMap H x‖ = ‖x‖ := by
  change ‖(Complex.I : ℂ) • x‖ = ‖x‖
  rw [norm_smul, Complex.norm_I, one_mul]

@[simp]
theorem IMapCLM_norm (x : H) : ‖IMapCLM H x‖ = ‖x‖ :=
  IMap_norm x

theorem IMapCLM_isometry : Isometry (IMapCLM H) :=
  Isometry.of_dist_eq fun x y => by
    simp only [dist_eq_norm, ← map_sub, IMapCLM_norm]

/-- `IMap` packaged as a real-linear isometric equivalence `H ≃ₗᵢ[ℝ] H`. -/
def IMapLIE (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : H ≃ₗᵢ[ℝ] H where
  toLinearMap := IMap H
  invFun := fun x => (-Complex.I : ℂ) • x
  left_inv := fun x => by
    change (-Complex.I : ℂ) • ((Complex.I : ℂ) • x) = x
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  right_inv := fun x => by
    change (Complex.I : ℂ) • ((-Complex.I : ℂ) • x) = x
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  norm_map' := IMap_norm

@[simp]
theorem IMapLIE_apply (x : H) : IMapLIE H x = IMap H x := rfl

@[simp]
theorem IMapLIE_symm_apply (x : H) : (IMapLIE H).symm x = (-Complex.I : ℂ) • x := rfl

/-- `IMap` packaged as a continuous real-linear equivalence `H ≃L[ℝ] H`. -/
def IMapCLE (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : H ≃L[ℝ] H :=
  (IMapLIE H).toContinuousLinearEquiv

@[simp]
theorem IMapCLE_apply (x : H) : IMapCLE H x = IMap H x := rfl

@[simp]
theorem IMapCLM_sq : (IMapCLM H).comp (IMapCLM H) = -ContinuousLinearMap.id ℝ H := by
  ext x
  change (Complex.I : ℂ) • ((Complex.I : ℂ) • x) = -x
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

theorem IMapCLM_mul_self : IMapCLM H * IMapCLM H = -1 :=
  IMapCLM_sq

theorem IMap_inner (x y : H) : ⟪IMap H x, IMap H y⟫_ℂ = ⟪x, y⟫_ℂ := by
  change ⟪(Complex.I : ℂ) • x, (Complex.I : ℂ) • y⟫_ℂ = ⟪x, y⟫_ℂ
  rw [inner_smul_left, inner_smul_right, starRingEnd_apply, Complex.star_def, Complex.conj_I,
    ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

theorem IMap_inner_re (x y : H) : (⟪IMap H x, IMap H y⟫_ℂ).re = (⟪x, y⟫_ℂ).re :=
  congrArg Complex.re (IMap_inner x y)

theorem IMap_inner_left_re (x y : H) :
    (⟪IMap H x, y⟫_ℂ).re = -(⟪x, IMap H y⟫_ℂ).re := by
  change (⟪(Complex.I : ℂ) • x, y⟫_ℂ).re = -(⟪x, (Complex.I : ℂ) • y⟫_ℂ).re
  rw [inner_smul_left, inner_smul_right, starRingEnd_apply, Complex.star_def, Complex.conj_I,
    neg_mul, Complex.neg_re]

theorem IMapCLM_adjoint [CompleteSpace H] :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    (IMapCLM H).adjoint = -(IMapCLM H) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [neg_apply, inner_neg_left, IMapCLM_apply, IMapCLM_apply]
  change -(⟪IMap H x, y⟫_ℂ).re = (⟪x, IMap H y⟫_ℂ).re
  rw [IMap_inner_left_re, neg_neg]

end IMapSection

section SubmoduleClosedness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem mem_imaginarySubmodule_iff (K : Submodule ℝ H) (x : H) :
    x ∈ ImaginarySubmodule (H := H) K ↔ (-Complex.I : ℂ) • x ∈ K := by
  rw [ImaginarySubmodule, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hinv : (-Complex.I : ℂ) • IMap H y = y := (IMapLIE H).left_inv y
    simpa [hinv] using hy
  · intro hx
    refine ⟨(-Complex.I : ℂ) • x, hx, ?_⟩
    exact (IMapLIE H).right_inv x

theorem isClosed_imaginarySubmodule {K : Submodule ℝ H} (hK : IsClosed (K : Set H)) :
    IsClosed (ImaginarySubmodule (H := H) K : Set H) := by
  have hset : (ImaginarySubmodule (H := H) K : Set H) =
      (fun x : H => (-Complex.I : ℂ) • x) ⁻¹' (K : Set H) := by
    ext x
    exact mem_imaginarySubmodule_iff K x
  rw [hset]
  exact hK.preimage (continuous_const_smul (-Complex.I : ℂ))

theorem completeSpace_imaginarySubmodule (K : Submodule ℝ H) [CompleteSpace K] :
    CompleteSpace (ImaginarySubmodule (H := H) K) := by
  have hCompleteK : IsComplete (K : Set H) :=
    completeSpace_coe_iff_isComplete.mp ‹CompleteSpace K›
  have hImage : ((IMapLIE H : H → H) '' (K : Set H)) =
      (ImaginarySubmodule (H := H) K : Set H) := by
    ext x
    simp [ImaginarySubmodule]
  have hCompleteIK : IsComplete (ImaginarySubmodule (H := H) K : Set H) := by
    rw [← hImage]
    exact (_root_.isComplete_image_iff (IMapLIE H).isometry.isUniformInducing).mpr hCompleteK
  exact hCompleteIK.completeSpace_coe

end SubmoduleClosedness

section Projections

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Orthogonal projection `P_K : H →L[ℝ] H` onto a complete real subspace `K`
with respect to the realified inner product `(⟪x, y⟫_ℂ).re`. -/
def projK (K : Submodule ℝ H) [CompleteSpace K] : H →L[ℝ] H :=
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  K.starProjection

/-- Orthogonal projection `P_{iK} : H →L[ℝ] H` onto a complete imaginary-rotated
real subspace `iK = ImaginarySubmodule K`. -/
def projIK (K : Submodule ℝ H) [CompleteSpace (ImaginarySubmodule (H := H) K)] : H →L[ℝ] H :=
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  (ImaginarySubmodule (H := H) K).starProjection

theorem projK_eq_subtypeL_comp_orthogonalProjectionOnto
    (K : Submodule ℝ H) [CompleteSpace K] :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    projK (H := H) K = K.subtypeL ∘L K.orthogonalProjectionOnto :=
  rfl

theorem projIK_eq_subtypeL_comp_orthogonalProjectionOnto
    (K : Submodule ℝ H) [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    projIK (H := H) K =
      (ImaginarySubmodule (H := H) K).subtypeL ∘L
        (ImaginarySubmodule (H := H) K).orthogonalProjectionOnto :=
  rfl

theorem projK_apply_mem (K : Submodule ℝ H) [CompleteSpace K] (x : H) :
    projK (H := H) K x ∈ K := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact K.starProjection_apply_mem x

theorem projIK_apply_mem (K : Submodule ℝ H) [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (x : H) :
    projIK (H := H) K x ∈ ImaginarySubmodule (H := H) K := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact (ImaginarySubmodule (H := H) K).starProjection_apply_mem x

theorem projK_eq_self_iff (K : Submodule ℝ H) [CompleteSpace K] (x : H) :
    projK (H := H) K x = x ↔ x ∈ K := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact K.starProjection_eq_self_iff

theorem projIK_eq_self_iff (K : Submodule ℝ H) [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (x : H) :
    projIK (H := H) K x = x ↔ x ∈ ImaginarySubmodule (H := H) K := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact (ImaginarySubmodule (H := H) K).starProjection_eq_self_iff

theorem projK_isSelfAdjoint [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K] :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    IsSelfAdjoint (projK (H := H) K) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact isSelfAdjoint_starProjection K

theorem projIK_isSelfAdjoint [CompleteSpace H] (K : Submodule ℝ H)
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    IsSelfAdjoint (projIK (H := H) K) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact isSelfAdjoint_starProjection (ImaginarySubmodule (H := H) K)

@[simp]
theorem projK_mul_self (K : Submodule ℝ H) [CompleteSpace K] :
    projK (H := H) K * projK (H := H) K = projK (H := H) K := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact K.isIdempotentElem_starProjection.eq

@[simp]
theorem projIK_mul_self (K : Submodule ℝ H) [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    projIK (H := H) K * projIK (H := H) K = projIK (H := H) K := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact (ImaginarySubmodule (H := H) K).isIdempotentElem_starProjection.eq

@[simp]
theorem projK_comp_self (K : Submodule ℝ H) [CompleteSpace K] :
    (projK (H := H) K).comp (projK (H := H) K) = projK (H := H) K :=
  projK_mul_self K

@[simp]
theorem projIK_comp_self (K : Submodule ℝ H) [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    (projIK (H := H) K).comp (projIK (H := H) K) = projIK (H := H) K :=
  projIK_mul_self K

theorem projK_norm_le (K : Submodule ℝ H) [CompleteSpace K] :
    ‖projK (H := H) K‖ ≤ 1 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact K.starProjection_norm_le

theorem projIK_norm_le (K : Submodule ℝ H) [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    ‖projIK (H := H) K‖ ≤ 1 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact (ImaginarySubmodule (H := H) K).starProjection_norm_le

theorem norm_projK_apply_le (K : Submodule ℝ H) [CompleteSpace K] (x : H) :
    ‖projK (H := H) K x‖ ≤ ‖x‖ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact K.norm_starProjection_apply_le x

theorem norm_projIK_apply_le (K : Submodule ℝ H)
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    ‖projIK (H := H) K x‖ ≤ ‖x‖ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact (ImaginarySubmodule (H := H) K).norm_starProjection_apply_le x

theorem projK_inner_re_left_eq_right (K : Submodule ℝ H) [CompleteSpace K] (x y : H) :
    (⟪projK (H := H) K x, y⟫_ℂ).re = (⟪x, projK (H := H) K y⟫_ℂ).re := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact K.inner_starProjection_left_eq_right x y

theorem projIK_inner_re_left_eq_right (K : Submodule ℝ H)
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x y : H) :
    (⟪projIK (H := H) K x, y⟫_ℂ).re = (⟪x, projIK (H := H) K y⟫_ℂ).re := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact (ImaginarySubmodule (H := H) K).inner_starProjection_left_eq_right x y

theorem projK_inner_re_eq (K : Submodule ℝ H) [CompleteSpace K] (x : H) :
    (⟪x, projK (H := H) K x⟫_ℂ).re = ‖projK (H := H) K x‖ ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [← projK_inner_re_left_eq_right K x x]
  exact K.re_inner_starProjection_eq_normSq x

theorem projIK_inner_re_eq (K : Submodule ℝ H)
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    (⟪x, projIK (H := H) K x⟫_ℂ).re = ‖projIK (H := H) K x‖ ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [← projIK_inner_re_left_eq_right K x x]
  exact (ImaginarySubmodule (H := H) K).re_inner_starProjection_eq_normSq x

theorem IMapCLM_comp_projK (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    (IMapCLM H).comp (projK (H := H) K) = (projIK (H := H) K).comp (IMapCLM H) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  ext x
  simp only [ContinuousLinearMap.comp_apply, projK, projIK, IMapCLM_apply]
  let fLIE : H ≃ₗᵢ[ℝ] H :=
    { toLinearEquiv := (IMapLIE H).toLinearEquiv
      norm_map' := (IMapLIE H).norm_map }
  have hProj := Submodule.starProjection_map_apply (𝕜 := ℝ) (E := H) (E' := H)
    fLIE K (IMap H x)
  have hLeft : (K.map (fLIE.toLinearEquiv : H →ₗ[ℝ] H)).starProjection (IMap H x) =
      (ImaginarySubmodule (H := H) K).starProjection (IMap H x) := by
    congr 1
  rw [← hLeft, hProj]
  have hInv : fLIE.symm (IMap H x) = x := (IMapLIE H).left_inv x
  rw [hInv]
  rfl

theorem IMapCLM_comp_projIK (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    (IMapCLM H).comp (projIK (H := H) K) = (projK (H := H) K).comp (IMapCLM H) := by
  have h1 : (IMapCLM H).comp ((projK (H := H) K).comp (IMapCLM H)) = -(projIK (H := H) K) := by
    rw [← ContinuousLinearMap.comp_assoc, IMapCLM_comp_projK, ContinuousLinearMap.comp_assoc,
      IMapCLM_sq, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id]
  have h2 := congrArg ((IMapCLM H).comp ·) h1
  rw [← ContinuousLinearMap.comp_assoc, IMapCLM_sq, ContinuousLinearMap.neg_comp,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_neg] at h2
  exact neg_inj.mp h2.symm

end Projections

section RieffelVanDaeleOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Rieffel–van Daele bounded positive operator `R = P_K + P_{iK} : H →L[ℝ] H`. -/
def rvdR (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] : H →L[ℝ] H :=
  projK (H := H) K + projIK (H := H) K

/-- The Rieffel–van Daele bounded antilinear operator `T = P_K - P_{iK} : H →L[ℝ] H`. -/
def rvdT (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] : H →L[ℝ] H :=
  projK (H := H) K - projIK (H := H) K

theorem rvdR_apply (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    rvdR (H := H) K x = projK (H := H) K x + projIK (H := H) K x :=
  rfl

theorem rvdT_apply (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    rvdT (H := H) K x = projK (H := H) K x - projIK (H := H) K x :=
  rfl

theorem rvdR_isSelfAdjoint [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    IsSelfAdjoint (rvdR (H := H) K) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact (projK_isSelfAdjoint (H := H) K).add (projIK_isSelfAdjoint (H := H) K)

theorem rvdT_isSelfAdjoint [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    IsSelfAdjoint (rvdT (H := H) K) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact (projK_isSelfAdjoint (H := H) K).sub (projIK_isSelfAdjoint (H := H) K)

theorem rvdR_inner_re_left_eq_right (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x y : H) :
    (⟪rvdR (H := H) K x, y⟫_ℂ).re = (⟪x, rvdR (H := H) K y⟫_ℂ).re := by
  simp only [rvdR_apply, inner_add_left, inner_add_right, Complex.add_re,
    projK_inner_re_left_eq_right, projIK_inner_re_left_eq_right]

theorem rvdT_inner_re_left_eq_right (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x y : H) :
    (⟪rvdT (H := H) K x, y⟫_ℂ).re = (⟪x, rvdT (H := H) K y⟫_ℂ).re := by
  simp only [rvdT_apply, inner_sub_left, inner_sub_right, Complex.sub_re,
    projK_inner_re_left_eq_right, projIK_inner_re_left_eq_right]

theorem rvdR_inner_re_eq (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    (⟪x, rvdR (H := H) K x⟫_ℂ).re =
      ‖projK (H := H) K x‖ ^ 2 + ‖projIK (H := H) K x‖ ^ 2 := by
  simp only [rvdR_apply, inner_add_right, Complex.add_re,
    projK_inner_re_eq, projIK_inner_re_eq]

theorem rvdT_inner_re_eq (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    (⟪x, rvdT (H := H) K x⟫_ℂ).re =
      ‖projK (H := H) K x‖ ^ 2 - ‖projIK (H := H) K x‖ ^ 2 := by
  simp only [rvdT_apply, inner_sub_right, Complex.sub_re,
    projK_inner_re_eq, projIK_inner_re_eq]

theorem rvdR_inner_re_bounds (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    0 ≤ (⟪x, rvdR (H := H) K x⟫_ℂ).re ∧ (⟪x, rvdR (H := H) K x⟫_ℂ).re ≤ 2 * ‖x‖ ^ 2 := by
  rw [rvdR_inner_re_eq]
  have hp1 : 0 ≤ ‖projK (H := H) K x‖ ^ 2 := sq_nonneg _
  have hp2 : 0 ≤ ‖projIK (H := H) K x‖ ^ 2 := sq_nonneg _
  have hb1 : ‖projK (H := H) K x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_projK_apply_le K x) 2
  have hb2 : ‖projIK (H := H) K x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_projIK_apply_le K x) 2
  constructor <;> linarith

theorem rvdR_inner_bounds (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    0 ≤ ⟪x, rvdR (H := H) K x⟫_ℝ ∧ ⟪x, rvdR (H := H) K x⟫_ℝ ≤ 2 * ‖x‖ ^ 2 :=
  rvdR_inner_re_bounds K x

theorem rvdT_inner_re_bounds (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    -(‖x‖ ^ 2) ≤ (⟪x, rvdT (H := H) K x⟫_ℂ).re ∧ (⟪x, rvdT (H := H) K x⟫_ℂ).re ≤ ‖x‖ ^ 2 := by
  rw [rvdT_inner_re_eq]
  have hp1 : 0 ≤ ‖projK (H := H) K x‖ ^ 2 := sq_nonneg _
  have hp2 : 0 ≤ ‖projIK (H := H) K x‖ ^ 2 := sq_nonneg _
  have hb1 : ‖projK (H := H) K x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_projK_apply_le K x) 2
  have hb2 : ‖projIK (H := H) K x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_projIK_apply_le K x) 2
  constructor <;> linarith

theorem rvdR_norm_le (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    ‖rvdR (H := H) K‖ ≤ 2 := by
  have h1 : ‖projK (H := H) K‖ ≤ 1 := projK_norm_le K
  have h2 : ‖projIK (H := H) K‖ ≤ 1 := projIK_norm_le K
  have hadd : ‖rvdR (H := H) K‖ ≤ ‖projK (H := H) K‖ + ‖projIK (H := H) K‖ :=
    norm_add_le _ _
  linarith

theorem rvdR_isPositive [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    (rvdR (H := H) K).IsPositive := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨(rvdR_isSelfAdjoint K).isSymmetric, fun x => ?_⟩
  rw [real_inner_comm]
  exact (rvdR_inner_re_bounds K x).1

theorem two_sub_rvdR_inner_re_eq (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    (⟪x, ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x⟫_ℂ).re =
      (‖x‖ ^ 2 - ‖projK (H := H) K x‖ ^ 2) + (‖x‖ ^ 2 - ‖projIK (H := H) K x‖ ^ 2) := by
  have h2op : ((2 : ℝ) • (1 : H →L[ℝ] H)) x = x + x := by
    rw [two_smul ℝ (1 : H →L[ℝ] H)]
    rfl
  have hxx : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
    let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    exact real_inner_self_eq_norm_sq x
  have h2 : (⟪x, ((2 : ℝ) • (1 : H →L[ℝ] H)) x⟫_ℂ).re = 2 * ‖x‖ ^ 2 := by
    rw [h2op, inner_add_right, Complex.add_re, hxx]
    ring
  have hsub : ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x =
      ((2 : ℝ) • (1 : H →L[ℝ] H)) x - rvdR (H := H) K x := rfl
  rw [hsub, inner_sub_right, Complex.sub_re, h2, rvdR_inner_re_eq]
  ring

theorem two_sub_rvdR_inner_re_bounds (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    0 ≤ (⟪x, ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x⟫_ℂ).re ∧
      (⟪x, ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x⟫_ℂ).re ≤ 2 * ‖x‖ ^ 2 := by
  have hsum : (⟪x, ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x⟫_ℂ).re =
      2 * ‖x‖ ^ 2 - (⟪x, rvdR (H := H) K x⟫_ℂ).re := by
    rw [two_sub_rvdR_inner_re_eq, rvdR_inner_re_eq]
    ring
  have hr := rvdR_inner_re_bounds K x
  rw [hsum]
  constructor <;> linarith

theorem rvdT_sq_eq (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    rvdT (H := H) K * rvdT (H := H) K =
      rvdR (H := H) K * ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) := by
  have hp : projK (H := H) K * projK (H := H) K = projK (H := H) K := projK_mul_self K
  have hq : projIK (H := H) K * projIK (H := H) K = projIK (H := H) K := projIK_mul_self K
  have h2 : (2 : ℝ) • (1 : H →L[ℝ] H) = 1 + 1 := two_smul ℝ (1 : H →L[ℝ] H)
  rw [h2]
  simp only [rvdT, rvdR, mul_sub, sub_mul, mul_add, add_mul, mul_one, hp, hq]
  abel

theorem one_sub_rvdR_sq_add_rvdT_sq (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    (1 - rvdR (H := H) K) * (1 - rvdR (H := H) K) + rvdT (H := H) K * rvdT (H := H) K = 1 := by
  rw [rvdT_sq_eq]
  have h2 : (2 : ℝ) • (1 : H →L[ℝ] H) = 1 + 1 := two_smul ℝ (1 : H →L[ℝ] H)
  rw [h2]
  simp only [sub_mul, mul_sub, mul_add, mul_one, one_mul]
  abel

theorem one_sub_rvdR_norm_sq_add_rvdT_norm_sq (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    ‖(1 - rvdR (H := H) K) x‖ ^ 2 + ‖rvdT (H := H) K x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hnorm : ∀ y : H, ‖y‖ ^ 2 = (⟪y, y⟫_ℂ).re := fun y => by
    let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    exact (real_inner_self_eq_norm_sq y).symm
  have hn1 : ‖(1 - rvdR (H := H) K) x‖ ^ 2 =
      (⟪x, ((1 - rvdR (H := H) K) * (1 - rvdR (H := H) K)) x⟫_ℂ).re := by
    rw [hnorm]
    let y := (1 - rvdR (H := H) K) x
    have hy : (1 - rvdR (H := H) K) x = x - rvdR (H := H) K x := rfl
    calc
      (⟪y, y⟫_ℂ).re = (⟪x - rvdR (H := H) K x, y⟫_ℂ).re := by rw [← hy]
      _ = (⟪x, y⟫_ℂ).re - (⟪rvdR (H := H) K x, y⟫_ℂ).re := by
            rw [inner_sub_left, Complex.sub_re]
      _ = (⟪x, y⟫_ℂ).re - (⟪x, rvdR (H := H) K y⟫_ℂ).re := by
            rw [rvdR_inner_re_left_eq_right]
      _ = (⟪x, y - rvdR (H := H) K y⟫_ℂ).re := by
            rw [inner_sub_right, Complex.sub_re]
      _ = (⟪x, ((1 - rvdR (H := H) K) * (1 - rvdR (H := H) K)) x⟫_ℂ).re := rfl
  have hn2 : ‖rvdT (H := H) K x‖ ^ 2 = (⟪x, (rvdT (H := H) K * rvdT (H := H) K) x⟫_ℂ).re := by
    rw [hnorm, rvdT_inner_re_left_eq_right]
    rfl
  rw [hn1, hn2, ← Complex.add_re, ← inner_add_right]
  have hsum : ((1 - rvdR (H := H) K) * (1 - rvdR (H := H) K)) x +
      (rvdT (H := H) K * rvdT (H := H) K) x =
      ((1 - rvdR (H := H) K) * (1 - rvdR (H := H) K) +
        rvdT (H := H) K * rvdT (H := H) K) x := rfl
  rw [hsum, one_sub_rvdR_sq_add_rvdT_sq]
  change (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2
  exact (hnorm x).symm

theorem rvdT_norm_le (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    ‖rvdT (H := H) K‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  have hsq : ‖rvdT (H := H) K x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have hpyth := one_sub_rvdR_norm_sq_add_rvdT_norm_sq K x
    have hnonneg : 0 ≤ ‖(1 - rvdR (H := H) K) x‖ ^ 2 := sq_nonneg _
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem IMapCLM_comp_rvdR (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    (IMapCLM H).comp (rvdR (H := H) K) = (rvdR (H := H) K).comp (IMapCLM H) := by
  simp only [rvdR, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
    IMapCLM_comp_projK, IMapCLM_comp_projIK, add_comm]

theorem IMapCLM_comp_rvdT (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    (IMapCLM H).comp (rvdT (H := H) K) = -((rvdT (H := H) K).comp (IMapCLM H)) := by
  simp only [rvdT, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    IMapCLM_comp_projK, IMapCLM_comp_projIK, neg_sub]

theorem IMapCLM_commutes_rvdT_sq (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    (IMapCLM H).comp (rvdT (H := H) K * rvdT (H := H) K) =
      (rvdT (H := H) K * rvdT (H := H) K).comp (IMapCLM H) := by
  calc
    (IMapCLM H).comp ((rvdT (H := H) K).comp (rvdT (H := H) K))
        = ((IMapCLM H).comp (rvdT (H := H) K)).comp (rvdT (H := H) K) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = (-((rvdT (H := H) K).comp (IMapCLM H))).comp (rvdT (H := H) K) := by
          rw [IMapCLM_comp_rvdT]
    _ = -((rvdT (H := H) K).comp ((IMapCLM H).comp (rvdT (H := H) K))) := by
          rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]
    _ = -((rvdT (H := H) K).comp (-((rvdT (H := H) K).comp (IMapCLM H)))) := by
          rw [IMapCLM_comp_rvdT]
    _ = ((rvdT (H := H) K).comp (rvdT (H := H) K)).comp (IMapCLM H) := by
          simp [ContinuousLinearMap.comp_assoc]

theorem rvdR_comp_rvdT (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    rvdR (H := H) K * rvdT (H := H) K =
      rvdT (H := H) K * ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) := by
  have hp : projK (H := H) K * projK (H := H) K = projK (H := H) K := projK_mul_self K
  have hq : projIK (H := H) K * projIK (H := H) K = projIK (H := H) K := projIK_mul_self K
  have h2 : (2 : ℝ) • (1 : H →L[ℝ] H) = 1 + 1 := two_smul ℝ (1 : H →L[ℝ] H)
  rw [h2]
  simp only [rvdR, rvdT, mul_sub, sub_mul, mul_add, add_mul, mul_one, hp, hq]
  abel

/-- Complex-linear lift of `rvdR K` as `H →L[ℂ] H`, constructed from `IMapCLM_comp_rvdR`. -/
def rvdRComplexCLM (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] : H →L[ℂ] H where
  toFun := rvdR (H := H) K
  map_add' := (rvdR (H := H) K).map_add
  map_smul' := fun c x => by
    have hI : rvdR (H := H) K ((Complex.I : ℂ) • x) = (Complex.I : ℂ) • rvdR (H := H) K x := by
      have h := congrArg (fun f : H →L[ℝ] H => f x) (IMapCLM_comp_rvdR (H := H) K)
      simpa [IMapCLM_apply, IMap] using h.symm
    have hde : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    conv_lhs => rw [hde, add_smul]
    rw [map_add]
    have h1 : rvdR (H := H) K ((c.re : ℂ) • x) = (c.re : ℂ) • rvdR (H := H) K x :=
      (rvdR (H := H) K).map_smul c.re x
    have h2 : rvdR (H := H) K (((c.im : ℂ) * Complex.I) • x) =
        ((c.im : ℂ) * Complex.I) • rvdR (H := H) K x := by
      rw [← smul_smul]
      calc
        rvdR (H := H) K ((c.im : ℂ) • (Complex.I • x))
            = rvdR (H := H) K (c.im • (Complex.I • x)) := rfl
        _ = c.im • rvdR (H := H) K (Complex.I • x) := (rvdR (H := H) K).map_smul _ _
        _ = (c.im : ℂ) • (Complex.I • rvdR (H := H) K x) := by rw [hI]; rfl
        _ = ((c.im : ℂ) * Complex.I) • rvdR (H := H) K x := smul_smul _ _ _
    rw [h1, h2, ← add_smul, ← hde]
    rfl
  cont := (rvdR (H := H) K).continuous

/-- Complex-antilinear lift of `rvdT K` as `H →L⋆[ℂ] H`, constructed from
`IMapCLM_comp_rvdT`. -/
def rvdTConjugateCLM (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] : H →L⋆[ℂ] H where
  toFun := rvdT (H := H) K
  map_add' := (rvdT (H := H) K).map_add
  map_smul' := fun c x => by
    have hI : rvdT (H := H) K ((Complex.I : ℂ) • x) = -(Complex.I : ℂ) • rvdT (H := H) K x := by
      have h := congrArg (fun f : H →L[ℝ] H => f x) (IMapCLM_comp_rvdT (H := H) K)
      have h' : (Complex.I : ℂ) • rvdT (H := H) K x =
          -(rvdT (H := H) K ((Complex.I : ℂ) • x)) := by
        simpa [IMapCLM_apply, IMap] using h
      rw [neg_smul]
      exact neg_eq_iff_eq_neg.mp h'.symm
    have hde : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    have hstar : starRingEnd ℂ c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
      rw [starRingEnd_apply, Complex.star_def]
      exact Complex.ext (by simp) (by simp)
    conv_lhs => rw [hde, add_smul]
    rw [map_add, hstar, sub_smul]
    have h1 : rvdT (H := H) K ((c.re : ℂ) • x) = (c.re : ℂ) • rvdT (H := H) K x :=
      (rvdT (H := H) K).map_smul c.re x
    have h2 : rvdT (H := H) K (((c.im : ℂ) * Complex.I) • x) =
        -((c.im : ℂ) * Complex.I) • rvdT (H := H) K x := by
      rw [← smul_smul]
      calc
        rvdT (H := H) K ((c.im : ℂ) • (Complex.I • x))
            = rvdT (H := H) K (c.im • (Complex.I • x)) := rfl
        _ = c.im • rvdT (H := H) K (Complex.I • x) := (rvdT (H := H) K).map_smul _ _
        _ = (c.im : ℂ) • (-(Complex.I : ℂ) • rvdT (H := H) K x) := by rw [hI]; rfl
        _ = -((c.im : ℂ) * Complex.I) • rvdT (H := H) K x := by
          rw [smul_smul, mul_neg, neg_smul]
    rw [h1, h2, neg_smul, ← sub_eq_add_neg]
  cont := (rvdT (H := H) K).continuous

end RieffelVanDaeleOperators

section KernelAndDensity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rvdR_eq_zero_iff (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    rvdR (H := H) K x = 0 ↔
      letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
      x ∈ (K ⊔ ImaginarySubmodule (H := H) K)ᗮ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [← Submodule.inf_orthogonal, Submodule.mem_inf,
    ← K.starProjection_apply_eq_zero_iff,
    ← (ImaginarySubmodule (H := H) K).starProjection_apply_eq_zero_iff]
  change rvdR (H := H) K x = 0 ↔ projK (H := H) K x = 0 ∧ projIK (H := H) K x = 0
  constructor
  · intro hR
    have hre : (⟪x, rvdR (H := H) K x⟫_ℂ).re = 0 := by simp [hR]
    rw [rvdR_inner_re_eq] at hre
    have h1 : ‖projK (H := H) K x‖ ^ 2 = 0 := by
      have ha : 0 ≤ ‖projK (H := H) K x‖ ^ 2 := sq_nonneg _
      have hb : 0 ≤ ‖projIK (H := H) K x‖ ^ 2 := sq_nonneg _
      linarith
    have h2 : ‖projIK (H := H) K x‖ ^ 2 = 0 := by
      have ha : 0 ≤ ‖projK (H := H) K x‖ ^ 2 := sq_nonneg _
      have hb : 0 ≤ ‖projIK (H := H) K x‖ ^ 2 := sq_nonneg _
      linarith
    exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp h1), norm_eq_zero.mp (sq_eq_zero_iff.mp h2)⟩
  · rintro ⟨h1, h2⟩
    simp [rvdR_apply, h1, h2]

theorem rvdR_injective (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (hK : IsStandardSubspace (H := H) K) :
    Function.Injective (rvdR (H := H) K) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ (K ⊔ ImaginarySubmodule (H := H) K)ᗮ :=
    (rvdR_eq_zero_iff (H := H) K x).mp hx
  exact hK.1.eq_zero_of_mem_orthogonal hmem

theorem two_sub_rvdR_eq_zero_iff (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x = 0 ↔
      x ∈ K ⊓ ImaginarySubmodule (H := H) K := by
  rw [Submodule.mem_inf, ← projK_eq_self_iff (H := H) K x,
    ← projIK_eq_self_iff (H := H) K x]
  constructor
  · intro h
    have hre : (⟪x, ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x⟫_ℂ).re = 0 := by simp [h]
    rw [two_sub_rvdR_inner_re_eq] at hre
    have hb1 : ‖projK (H := H) K x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_projK_apply_le K x) 2
    have hb2 : ‖projIK (H := H) K x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_projIK_apply_le K x) 2
    have hn1 : ‖projK (H := H) K x‖ ^ 2 = ‖x‖ ^ 2 := by linarith
    have hn2 : ‖projIK (H := H) K x‖ ^ 2 = ‖x‖ ^ 2 := by linarith
    let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    have hdiff1 : ‖x - projK (H := H) K x‖ ^ 2 = 0 := by
      have horth : ‖x‖ ^ 2 = ‖projK (H := H) K x‖ ^ 2 +
          ‖(Kᗮ).starProjection x‖ ^ 2 :=
        K.norm_sq_eq_add_norm_sq_starProjection x
      have hsub : (Kᗮ).starProjection x = x - projK (H := H) K x := by
        rw [K.starProjection_orthogonal']
        rfl
      rw [hsub] at horth
      linarith
    have hdiff2 : ‖x - projIK (H := H) K x‖ ^ 2 = 0 := by
      have horth : ‖x‖ ^ 2 = ‖projIK (H := H) K x‖ ^ 2 +
          ‖((ImaginarySubmodule (H := H) K)ᗮ).starProjection x‖ ^ 2 :=
        (ImaginarySubmodule (H := H) K).norm_sq_eq_add_norm_sq_starProjection x
      have hsub : ((ImaginarySubmodule (H := H) K)ᗮ).starProjection x =
          x - projIK (H := H) K x := by
        rw [(ImaginarySubmodule (H := H) K).starProjection_orthogonal']
        rfl
      rw [hsub] at horth
      linarith
    exact ⟨(sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdiff1))).symm,
      (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdiff2))).symm⟩
  · rintro ⟨h1, h2⟩
    have h2op : ((2 : ℝ) • (1 : H →L[ℝ] H)) x = x + x := by
      rw [two_smul ℝ (1 : H →L[ℝ] H)]
      rfl
    change ((2 : ℝ) • (1 : H →L[ℝ] H)) x - rvdR (H := H) K x = 0
    rw [h2op, rvdR_apply, h1, h2, sub_self]

theorem two_sub_rvdR_injective (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (hK : IsStandardSubspace (H := H) K) :
    Function.Injective ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ K ⊓ ImaginarySubmodule (H := H) K :=
    (two_sub_rvdR_eq_zero_iff (H := H) K x).mp hx
  rw [hK.2, Submodule.mem_bot] at hmem
  exact hmem

theorem rvdT_injective (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (hK : IsStandardSubspace (H := H) K) :
    Function.Injective (rvdT (H := H) K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hEq : projK (H := H) K x = projIK (H := H) K x := sub_eq_zero.mp hx
  have hMem : projK (H := H) K x ∈ K ⊓ ImaginarySubmodule (H := H) K := by
    refine ⟨projK_apply_mem K x, ?_⟩
    rw [hEq]
    exact projIK_apply_mem K x
  rw [hK.2, Submodule.mem_bot] at hMem
  have hPK : projK (H := H) K x = 0 := hMem
  have hPIK : projIK (H := H) K x = 0 := hEq.symm.trans hPK
  have hR : rvdR (H := H) K x = 0 := by simp [rvdR_apply, hPK, hPIK]
  exact rvdR_injective K hK (hR.trans (map_zero _).symm)

theorem denseRange_of_isSelfAdjoint_injective [CompleteSpace H]
    (A : H →L[ℝ] H)
    (hSA : letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
      IsSelfAdjoint A)
    (hInj : Function.Injective A) :
    DenseRange A := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  change Dense (A.range : Set H)
  rw [dense_iff_closure_eq]
  have hker : A.adjoint.ker = ⊥ := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp hSA, Submodule.eq_bot_iff]
    intro x hx
    exact hInj (by simpa using hx)
  have htop : A.range.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range]
    exact hker
  exact congrArg (fun S : Submodule ℝ H => (S : Set H)) htop

theorem denseRange_rvdR [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (hK : IsStandardSubspace (H := H) K) :
    DenseRange (rvdR (H := H) K) :=
  denseRange_of_isSelfAdjoint_injective (rvdR (H := H) K) (rvdR_isSelfAdjoint K)
    (rvdR_injective K hK)

theorem denseRange_two_sub_rvdR [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (hK : IsStandardSubspace (H := H) K) :
    DenseRange ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) := by
  refine denseRange_of_isSelfAdjoint_injective ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) ?_
    (two_sub_rvdR_injective K hK)
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change ⟪(2 : ℝ) • x - rvdR (H := H) K x, y⟫_ℝ = ⟪x, (2 : ℝ) • y - rvdR (H := H) K y⟫_ℝ
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  have hr : ⟪rvdR (H := H) K x, y⟫_ℝ = ⟪x, rvdR (H := H) K y⟫_ℝ :=
    rvdR_inner_re_left_eq_right K x y
  rw [hr]

theorem denseRange_rvdT [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (hK : IsStandardSubspace (H := H) K) :
    DenseRange (rvdT (H := H) K) :=
  denseRange_of_isSelfAdjoint_injective (rvdT (H := H) K) (rvdT_isSelfAdjoint K)
    (rvdT_injective K hK)

end KernelAndDensity

section TomitaAndResolventBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem two_sub_rvdR_eq_rvdT_on_K (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] {x : H} (hx : x ∈ K) :
    ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x = rvdT (H := H) K x := by
  have hpx : projK (H := H) K x = x := (projK_eq_self_iff K x).mpr hx
  have h2 : ((2 : ℝ) • (1 : H →L[ℝ] H)) x = x + x := by
    rw [two_smul ℝ (1 : H →L[ℝ] H)]
    rfl
  change ((2 : ℝ) • (1 : H →L[ℝ] H)) x - rvdR (H := H) K x = rvdT (H := H) K x
  rw [h2, rvdR_apply, rvdT_apply, hpx]
  abel

theorem two_sub_rvdR_eq_neg_rvdT_on_iK (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] {y : H}
    (hy : y ∈ ImaginarySubmodule (H := H) K) :
    ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) y = -(rvdT (H := H) K y) := by
  have hpy : projIK (H := H) K y = y := (projIK_eq_self_iff K y).mpr hy
  have h2 : ((2 : ℝ) • (1 : H →L[ℝ] H)) y = y + y := by
    rw [two_smul ℝ (1 : H →L[ℝ] H)]
    rfl
  change ((2 : ℝ) • (1 : H →L[ℝ] H)) y - rvdR (H := H) K y = -(rvdT (H := H) K y)
  rw [h2, rvdR_apply, rvdT_apply, hpy]
  abel

theorem rvdT_tomitaOnStandard [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (hK : IsStandardSubspace (H := H) K)
    (z : ↥(K ⊔ ImaginarySubmodule (H := H) K)) :
    rvdT (H := H) K (TomitaOnStandard (H := H) K hK z : H) =
      ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) (z : H) := by
  let p := (decompositionEquiv (H := H) K hK).symm z
  have hz : (z : H) = (p.1 : H) + (p.2 : H) := by
    have hp := (decompositionEquiv (H := H) K hK).apply_symm_apply z
    exact (congrArg (fun t : ↥(K ⊔ ImaginarySubmodule (H := H) K) => (t : H)) hp).symm
  have hS : (TomitaOnStandard (H := H) K hK z : H) = (p.1 : H) - (p.2 : H) := by
    change ((decompositionEquiv (H := H) K hK) (tomitaProd (H := H) K p) : H) = _
    simp [decompositionEquiv, addToSupMap, tomitaProd, sub_eq_add_neg]
  rw [hS, hz, map_sub, map_add]
  rw [← two_sub_rvdR_eq_rvdT_on_K K p.1.property,
    ← neg_eq_iff_eq_neg.mpr (two_sub_rvdR_eq_neg_rvdT_on_iK K p.2.property)]
  abel

theorem two_sub_rvdR_tomitaOnStandard [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (hK : IsStandardSubspace (H := H) K)
    (z : ↥(K ⊔ ImaginarySubmodule (H := H) K)) :
    ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K)
        (TomitaOnStandard (H := H) K hK z : H) =
      rvdT (H := H) K (z : H) := by
  let w := TomitaOnStandard (H := H) K hK z
  have hw : TomitaOnStandard (H := H) K hK w = z := tomitaOnStandard_involutive K hK z
  have h := rvdT_tomitaOnStandard K hK w
  rw [hw] at h
  exact h.symm

theorem isUnit_one_add_smul_rvdR [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] {α : ℝ} (hα : 0 ≤ α) :
    IsUnit ((1 : H →L[ℝ] H) + α • rvdR (H := H) K) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    ((1 : H →L[ℝ] H) + α • rvdR (H := H) K) (c := (1 : NNReal)) zero_lt_one fun x => ?_
  have hinner : ⟪((1 : H →L[ℝ] H) + α • rvdR (H := H) K) x, x⟫_ℝ =
      ‖x‖ ^ 2 + α * ⟪x, rvdR (H := H) K x⟫_ℝ := by
    change ⟪x + α • rvdR (H := H) K x, x⟫_ℝ = ‖x‖ ^ 2 + α * ⟪x, rvdR (H := H) K x⟫_ℝ
    rw [inner_add_left, real_inner_self_eq_norm_sq, real_inner_smul_left,
      real_inner_comm (rvdR (H := H) K x) x]
  have hnonneg : 0 ≤ α * ⟪x, rvdR (H := H) K x⟫_ℝ :=
    mul_nonneg hα (rvdR_inner_bounds K x).1
  have hge : ‖x‖ ^ 2 ≤ ⟪((1 : H →L[ℝ] H) + α • rvdR (H := H) K) x, x⟫_ℝ := by
    rw [hinner]
    linarith
  have hnorm : ‖x‖ ^ 2 ≤ ‖⟪((1 : H →L[ℝ] H) + α • rvdR (H := H) K) x, x⟫_ℝ‖ :=
    hge.trans (le_abs_self _)
  simpa using hnorm

theorem isUnit_one_add_smul_two_sub_rvdR [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] {α : ℝ} (hα : 0 ≤ α) :
    IsUnit ((1 : H →L[ℝ] H) + α • ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K)) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    ((1 : H →L[ℝ] H) + α • ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K))
    (c := (1 : NNReal)) zero_lt_one fun x => ?_
  have hinner : ⟪((1 : H →L[ℝ] H) + α • ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K)) x, x⟫_ℝ =
      ‖x‖ ^ 2 + α * (⟪x, ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x⟫_ℂ).re := by
    change ⟪x + α • ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x, x⟫_ℝ =
      ‖x‖ ^ 2 + α * (⟪x, ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x⟫_ℂ).re
    rw [inner_add_left, real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_comm x]
    rfl
  have hnonneg : 0 ≤ α * (⟪x, ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) x⟫_ℂ).re :=
    mul_nonneg hα (two_sub_rvdR_inner_re_bounds K x).1
  have hge : ‖x‖ ^ 2 ≤
      ⟪((1 : H →L[ℝ] H) + α • ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K)) x, x⟫_ℝ := by
    rw [hinner]
    linarith
  have hnorm : ‖x‖ ^ 2 ≤
      ‖⟪((1 : H →L[ℝ] H) + α • ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K)) x, x⟫_ℝ‖ :=
    hge.trans (le_abs_self _)
  simpa using hnorm

end TomitaAndResolventBridge

section SymplecticComplementAndJ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Symplectic complement `K' = (iK)ᗮ` of a real subspace `K` with respect to
the symplectic form `Im ⟪·, ·⟫_ℂ`. -/
def symplCompSubmodule (K : Submodule ℝ H) : Submodule ℝ H :=
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  (ImaginarySubmodule (H := H) K)ᗮ

theorem mem_symplCompSubmodule_iff (K : Submodule ℝ H) (x : H) :
    x ∈ symplCompSubmodule (H := H) K ↔ ∀ y ∈ K, (⟪y, x⟫_ℂ).im = 0 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [symplCompSubmodule, Submodule.mem_orthogonal]
  constructor
  · intro h y hy
    have h0 := h (IMap H y) (Submodule.mem_map_of_mem hy)
    change (⟪(Complex.I : ℂ) • y, x⟫_ℂ).re = 0 at h0
    rw [inner_smul_left, starRingEnd_apply, Complex.star_def, Complex.conj_I,
      neg_mul, Complex.neg_re, Complex.I_mul_re] at h0
    linarith
  · intro h w hw
    rcases (Submodule.mem_map).mp hw with ⟨y, hy, rfl⟩
    change (⟪(Complex.I : ℂ) • y, x⟫_ℂ).re = 0
    rw [inner_smul_left, starRingEnd_apply, Complex.star_def, Complex.conj_I,
      neg_mul, Complex.neg_re, Complex.I_mul_re, h y hy]
    simp

theorem isClosed_symplCompSubmodule (K : Submodule ℝ H) :
    IsClosed (symplCompSubmodule (H := H) K : Set H) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact (ImaginarySubmodule (H := H) K).isClosed_orthogonal

theorem completeSpace_symplCompSubmodule [CompleteSpace H] (K : Submodule ℝ H) :
    CompleteSpace (symplCompSubmodule (H := H) K) :=
  (isClosed_symplCompSubmodule (H := H) K).completeSpace_coe

theorem completeSpace_imaginary_symplCompSubmodule [CompleteSpace H] (K : Submodule ℝ H) :
    CompleteSpace (ImaginarySubmodule (H := H) (symplCompSubmodule (H := H) K)) :=
  (isClosed_imaginarySubmodule (isClosed_symplCompSubmodule (H := H) K)).completeSpace_coe

theorem projK_symplComp [CompleteSpace H] (K : Submodule ℝ H)
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    letI : CompleteSpace (symplCompSubmodule (H := H) K) :=
      completeSpace_symplCompSubmodule (H := H) K
    projK (H := H) (symplCompSubmodule (H := H) K) = 1 - projIK (H := H) K := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let : CompleteSpace (symplCompSubmodule (H := H) K) :=
    completeSpace_symplCompSubmodule (H := H) K
  change ((ImaginarySubmodule (H := H) K)ᗮ).starProjection =
    1 - (ImaginarySubmodule (H := H) K).starProjection
  exact (ImaginarySubmodule (H := H) K).starProjection_orthogonal'

theorem imaginary_symplCompSubmodule_eq_orthogonal (K : Submodule ℝ H) :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    ImaginarySubmodule (H := H) (symplCompSubmodule (H := H) K) = Kᗮ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  ext x
  rw [mem_imaginarySubmodule_iff, mem_symplCompSubmodule_iff, Submodule.mem_orthogonal]
  constructor
  · intro h y hy
    have hyx := h y hy
    change (⟪y, x⟫_ℂ).re = 0
    have hre : (⟪y, (-Complex.I : ℂ) • x⟫_ℂ).im = -(⟪y, x⟫_ℂ).re := by
      rw [inner_smul_right, neg_mul, Complex.neg_im, Complex.I_mul_im]
    linarith
  · intro h y hy
    have hre : (⟪y, x⟫_ℂ).re = 0 := h y hy
    rw [inner_smul_right, neg_mul, Complex.neg_im, Complex.I_mul_im, hre, neg_zero]

private theorem starProjection_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : U = V) (x : E) : U.starProjection x = V.starProjection x := by
  subst hUV
  rfl

theorem projIK_symplComp [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K] :
    letI : CompleteSpace (ImaginarySubmodule (H := H) (symplCompSubmodule (H := H) K)) :=
      completeSpace_imaginary_symplCompSubmodule (H := H) K
    projIK (H := H) (symplCompSubmodule (H := H) K) = 1 - projK (H := H) K := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let : CompleteSpace (ImaginarySubmodule (H := H) (symplCompSubmodule (H := H) K)) :=
    completeSpace_imaginary_symplCompSubmodule (H := H) K
  have h1 : projIK (H := H) (symplCompSubmodule (H := H) K) = Kᗮ.starProjection := by
    ext x
    exact starProjection_congr (imaginary_symplCompSubmodule_eq_orthogonal K) x
  rw [h1, K.starProjection_orthogonal']
  rfl

theorem rvdR_symplComp [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    letI : CompleteSpace (symplCompSubmodule (H := H) K) :=
      completeSpace_symplCompSubmodule (H := H) K
    letI : CompleteSpace (ImaginarySubmodule (H := H) (symplCompSubmodule (H := H) K)) :=
      completeSpace_imaginary_symplCompSubmodule (H := H) K
    rvdR (H := H) (symplCompSubmodule (H := H) K) =
      (2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K := by
  let : CompleteSpace (symplCompSubmodule (H := H) K) :=
    completeSpace_symplCompSubmodule (H := H) K
  let : CompleteSpace (ImaginarySubmodule (H := H) (symplCompSubmodule (H := H) K)) :=
    completeSpace_imaginary_symplCompSubmodule (H := H) K
  rw [rvdR, projK_symplComp K, projIK_symplComp K, rvdR, two_smul ℝ (1 : H →L[ℝ] H)]
  abel

theorem rvdT_symplComp [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    letI : CompleteSpace (symplCompSubmodule (H := H) K) :=
      completeSpace_symplCompSubmodule (H := H) K
    letI : CompleteSpace (ImaginarySubmodule (H := H) (symplCompSubmodule (H := H) K)) :=
      completeSpace_imaginary_symplCompSubmodule (H := H) K
    rvdT (H := H) (symplCompSubmodule (H := H) K) = rvdT (H := H) K := by
  let : CompleteSpace (symplCompSubmodule (H := H) K) :=
    completeSpace_symplCompSubmodule (H := H) K
  let : CompleteSpace (ImaginarySubmodule (H := H) (symplCompSubmodule (H := H) K)) :=
    completeSpace_imaginary_symplCompSubmodule (H := H) K
  rw [rvdT, projK_symplComp K, projIK_symplComp K, rvdT]
  abel

private theorem j_map_imaginarySubmodule (K : Submodule ℝ H) (J : H ≃ₗᵢ[ℝ] H)
    (hJ_anti : ∀ x : H, J ((Complex.I : ℂ) • x) = -(Complex.I : ℂ) • J x)
    (hJK : K.map (J.toLinearEquiv : H →ₗ[ℝ] H) = symplCompSubmodule (H := H) K) :
    (ImaginarySubmodule (H := H) K).map (J.toLinearEquiv : H →ₗ[ℝ] H) =
      ImaginarySubmodule (H := H) (symplCompSubmodule (H := H) K) := by
  ext x
  simp only [Submodule.mem_map, ImaginarySubmodule]
  constructor
  · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨-(J y), ?_, ?_⟩
    · refine Submodule.neg_mem _ ?_
      rw [← hJK, Submodule.mem_map]
      exact ⟨y, hy, rfl⟩
    · change (Complex.I : ℂ) • (-(J y)) = J ((Complex.I : ℂ) • y)
      rw [smul_neg, hJ_anti y, neg_smul]
  · rintro ⟨z, hz, rfl⟩
    rw [← hJK, Submodule.mem_map] at hz
    rcases hz with ⟨y, hy, rfl⟩
    refine ⟨-((Complex.I : ℂ) • y), ⟨-y, Submodule.neg_mem _ hy, ?_⟩, ?_⟩
    · change (Complex.I : ℂ) • (-y) = -((Complex.I : ℂ) • y)
      exact smul_neg _ _
    · change J (-((Complex.I : ℂ) • y)) = (Complex.I : ℂ) • J y
      rw [map_neg, hJ_anti y, neg_smul, neg_neg]

theorem j_conj_projK [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (J : H ≃ₗᵢ[ℝ] H)
    (hJK : K.map (J.toLinearEquiv : H →ₗ[ℝ] H) = symplCompSubmodule (H := H) K) :
    (J.toContinuousLinearEquiv : H →L[ℝ] H) * projK (H := H) K =
      (1 - projIK (H := H) K) * (J.toContinuousLinearEquiv : H →L[ℝ] H) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let : CompleteSpace (symplCompSubmodule (H := H) K) :=
    completeSpace_symplCompSubmodule (H := H) K
  let J_real : H ≃ₗᵢ[ℝ] H :=
    { toLinearEquiv := J.toLinearEquiv
      norm_map' := J.norm_map }
  ext x
  have hstar := Submodule.starProjection_map_apply (𝕜 := ℝ) (E := H) (E' := H)
    J_real K (J x)
  have hmap : (K.map (J_real.toLinearEquiv : H →ₗ[ℝ] H)).starProjection (J x) =
      projK (H := H) (symplCompSubmodule (H := H) K) (J x) :=
    starProjection_congr hJK (J x)
  have hleft : J (K.starProjection (J_real.symm (J x))) = J (projK (H := H) K x) := by
    have hinv : J_real.symm (J x) = x := J.left_inv x
    rw [hinv]
    rfl
  change J (projK (H := H) K x) = (1 - projIK (H := H) K) (J x)
  rw [← hleft, ← hstar, hmap, projK_symplComp K]

theorem j_conj_projIK [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (J : H ≃ₗᵢ[ℝ] H)
    (hJ_anti : ∀ x : H, J ((Complex.I : ℂ) • x) = -(Complex.I : ℂ) • J x)
    (hJK : K.map (J.toLinearEquiv : H →ₗ[ℝ] H) = symplCompSubmodule (H := H) K) :
    (J.toContinuousLinearEquiv : H →L[ℝ] H) * projIK (H := H) K =
      (1 - projK (H := H) K) * (J.toContinuousLinearEquiv : H →L[ℝ] H) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let : CompleteSpace (ImaginarySubmodule (H := H) (symplCompSubmodule (H := H) K)) :=
    completeSpace_imaginary_symplCompSubmodule (H := H) K
  let J_real : H ≃ₗᵢ[ℝ] H :=
    { toLinearEquiv := J.toLinearEquiv
      norm_map' := J.norm_map }
  ext x
  have hstar := Submodule.starProjection_map_apply (𝕜 := ℝ) (E := H) (E' := H)
    J_real (ImaginarySubmodule (H := H) K) (J x)
  have hmap : ((ImaginarySubmodule (H := H) K).map
      (J_real.toLinearEquiv : H →ₗ[ℝ] H)).starProjection (J x) =
      projIK (H := H) (symplCompSubmodule (H := H) K) (J x) :=
    starProjection_congr (j_map_imaginarySubmodule K J hJ_anti hJK) (J x)
  have hleft : J ((ImaginarySubmodule (H := H) K).starProjection (J_real.symm (J x))) =
      J (projIK (H := H) K x) := by
    have hinv : J_real.symm (J x) = x := J.left_inv x
    rw [hinv]
    rfl
  change J (projIK (H := H) K x) = (1 - projK (H := H) K) (J x)
  rw [← hleft, ← hstar, hmap, projIK_symplComp K]

theorem j_conj_rvdR_comp [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (J : H ≃ₗᵢ[ℝ] H)
    (hJ_anti : ∀ x : H, J ((Complex.I : ℂ) • x) = -(Complex.I : ℂ) • J x)
    (hJK : K.map (J.toLinearEquiv : H →ₗ[ℝ] H) = symplCompSubmodule (H := H) K) :
    (J.toContinuousLinearEquiv : H →L[ℝ] H) * rvdR (H := H) K =
      ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) *
        (J.toContinuousLinearEquiv : H →L[ℝ] H) := by
  have h2 : (2 : ℝ) • (1 : H →L[ℝ] H) = 1 + 1 := two_smul ℝ (1 : H →L[ℝ] H)
  rw [h2, rvdR, mul_add, j_conj_projK K J hJK, j_conj_projIK K J hJ_anti hJK]
  simp only [sub_mul, add_mul, one_mul]
  abel

theorem j_conj_rvdR [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (J : H ≃ₗᵢ[ℝ] H)
    (hJ_sq : ∀ x : H, J (J x) = x)
    (hJ_anti : ∀ x : H, J ((Complex.I : ℂ) • x) = -(Complex.I : ℂ) • J x)
    (hJK : K.map (J.toLinearEquiv : H →ₗ[ℝ] H) = symplCompSubmodule (H := H) K) :
    (J.toContinuousLinearEquiv : H →L[ℝ] H) * rvdR (H := H) K *
        (J.toContinuousLinearEquiv : H →L[ℝ] H) =
      (2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K := by
  have hJJ : (J.toContinuousLinearEquiv : H →L[ℝ] H) *
      (J.toContinuousLinearEquiv : H →L[ℝ] H) = 1 := by
    ext x
    exact hJ_sq x
  rw [j_conj_rvdR_comp K J hJ_anti hJK, mul_assoc, hJJ, mul_one]

theorem j_conj_rvdT_comp [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (J : H ≃ₗᵢ[ℝ] H)
    (hJ_anti : ∀ x : H, J ((Complex.I : ℂ) • x) = -(Complex.I : ℂ) • J x)
    (hJK : K.map (J.toLinearEquiv : H →ₗ[ℝ] H) = symplCompSubmodule (H := H) K) :
    (J.toContinuousLinearEquiv : H →L[ℝ] H) * rvdT (H := H) K =
      rvdT (H := H) K * (J.toContinuousLinearEquiv : H →L[ℝ] H) := by
  rw [rvdT, mul_sub, j_conj_projK K J hJK, j_conj_projIK K J hJ_anti hJK]
  simp only [sub_mul, one_mul]
  abel

theorem j_conj_rvdT [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (J : H ≃ₗᵢ[ℝ] H)
    (hJ_sq : ∀ x : H, J (J x) = x)
    (hJ_anti : ∀ x : H, J ((Complex.I : ℂ) • x) = -(Complex.I : ℂ) • J x)
    (hJK : K.map (J.toLinearEquiv : H →ₗ[ℝ] H) = symplCompSubmodule (H := H) K) :
    (J.toContinuousLinearEquiv : H →L[ℝ] H) * rvdT (H := H) K *
        (J.toContinuousLinearEquiv : H →L[ℝ] H) =
      rvdT (H := H) K := by
  have hJJ : (J.toContinuousLinearEquiv : H →L[ℝ] H) *
      (J.toContinuousLinearEquiv : H →L[ℝ] H) = 1 := by
    ext x
    exact hJ_sq x
  rw [j_conj_rvdT_comp K J hJ_anti hJK, mul_assoc, hJJ, mul_one]

theorem j_conj_rvdT_sq [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (J : H ≃ₗᵢ[ℝ] H)
    (hJ_sq : ∀ x : H, J (J x) = x)
    (hJ_anti : ∀ x : H, J ((Complex.I : ℂ) • x) = -(Complex.I : ℂ) • J x)
    (hJK : K.map (J.toLinearEquiv : H →ₗ[ℝ] H) = symplCompSubmodule (H := H) K) :
    (J.toContinuousLinearEquiv : H →L[ℝ] H) * (rvdT (H := H) K * rvdT (H := H) K) *
        (J.toContinuousLinearEquiv : H →L[ℝ] H) =
      rvdT (H := H) K * rvdT (H := H) K := by
  have hJJ : (J.toContinuousLinearEquiv : H →L[ℝ] H) *
      (J.toContinuousLinearEquiv : H →L[ℝ] H) = 1 := by
    ext x
    exact hJ_sq x
  have hc := j_conj_rvdT_comp K J hJ_anti hJK
  rw [← mul_assoc (J.toContinuousLinearEquiv : H →L[ℝ] H), hc,
    mul_assoc (rvdT (H := H) K), hc, mul_assoc, mul_assoc (rvdT (H := H) K), hJJ, mul_one]

end SymplecticComplementAndJ

section ComplexWitness

/-- Canonical standard real subspace `ℝ ⊆ ℂ`. -/
def realAxisSubmodule : Submodule ℝ ℂ :=
  Submodule.span ℝ {(1 : ℂ)}

theorem mem_realAxisSubmodule_iff (z : ℂ) :
    z ∈ realAxisSubmodule ↔ z.im = 0 := by
  rw [realAxisSubmodule, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    simp
  · intro hz
    refine ⟨z.re, ?_⟩
    exact Complex.ext (by simp) (by simp [hz])

theorem isClosed_realAxisSubmodule : IsClosed (realAxisSubmodule : Set ℂ) := by
  have hset : (realAxisSubmodule : Set ℂ) = Complex.im ⁻¹' {(0 : ℝ)} := by
    ext z
    simp [mem_realAxisSubmodule_iff]
  rw [hset]
  exact isClosed_singleton.preimage Complex.continuous_im

instance : CompleteSpace realAxisSubmodule :=
  isClosed_realAxisSubmodule.completeSpace_coe

instance : CompleteSpace (ImaginarySubmodule (H := ℂ) realAxisSubmodule) :=
  completeSpace_imaginarySubmodule (H := ℂ) realAxisSubmodule

theorem mem_imaginary_realAxisSubmodule_iff (z : ℂ) :
    z ∈ ImaginarySubmodule (H := ℂ) realAxisSubmodule ↔ z.re = 0 := by
  rw [mem_imaginarySubmodule_iff, mem_realAxisSubmodule_iff]
  simp

theorem realAxisSubmodule_isStandard : IsStandardSubspace (H := ℂ) realAxisSubmodule := by
  constructor
  · have htop : realAxisSubmodule ⊔ ImaginarySubmodule (H := ℂ) realAxisSubmodule = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [Submodule.mem_sup]
      refine ⟨(z.re : ℂ), (mem_realAxisSubmodule_iff _).mpr rfl,
        (z.im : ℂ) * Complex.I, (mem_imaginary_realAxisSubmodule_iff _).mpr (by simp), ?_⟩
      exact Complex.re_add_im z
    rw [htop]
    simp [dense_univ]
  · rw [eq_bot_iff]
    intro z hz
    rcases Submodule.mem_inf.mp hz with ⟨h1, h2⟩
    rw [mem_realAxisSubmodule_iff] at h1
    rw [mem_imaginary_realAxisSubmodule_iff] at h2
    exact Complex.ext h2 h1

theorem realAxisSubmodule_symplComp :
    symplCompSubmodule (H := ℂ) realAxisSubmodule = realAxisSubmodule := by
  ext z
  rw [mem_symplCompSubmodule_iff, mem_realAxisSubmodule_iff]
  constructor
  · intro h
    have h1 := h 1 ((mem_realAxisSubmodule_iff 1).mpr rfl)
    simpa using h1
  · intro hz y hy
    rw [mem_realAxisSubmodule_iff] at hy
    simp [RCLike.inner_apply, hy, hz]

theorem realAxisSubmodule_conj_map :
    realAxisSubmodule.map (Complex.conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) =
      symplCompSubmodule (H := ℂ) realAxisSubmodule := by
  rw [realAxisSubmodule_symplComp]
  ext z
  rw [Submodule.mem_map, mem_realAxisSubmodule_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_realAxisSubmodule_iff] at hw
    simp [hw]
  · intro hz
    refine ⟨z, (mem_realAxisSubmodule_iff z).mpr hz, ?_⟩
    exact Complex.ext (by simp) (by simp [hz])

theorem projK_realAxisSubmodule (z : ℂ) :
    projK (H := ℂ) realAxisSubmodule z = (z.re : ℂ) := by
  let : InnerProductSpace ℝ ℂ := InnerProductSpace.rclikeToReal ℂ ℂ
  change realAxisSubmodule.starProjection z = (z.re : ℂ)
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((mem_realAxisSubmodule_iff (z.re : ℂ)).mpr (by simp)) fun w hw => ?_
  rw [mem_realAxisSubmodule_iff] at hw
  change (⟪z - (z.re : ℂ), w⟫_ℂ).re = 0
  simp [RCLike.inner_apply, Complex.mul_re, hw]

theorem projIK_realAxisSubmodule (z : ℂ) :
    projIK (H := ℂ) realAxisSubmodule z = (z.im : ℂ) * Complex.I := by
  let : InnerProductSpace ℝ ℂ := InnerProductSpace.rclikeToReal ℂ ℂ
  change (ImaginarySubmodule (H := ℂ) realAxisSubmodule).starProjection z =
    (z.im : ℂ) * Complex.I
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((mem_imaginary_realAxisSubmodule_iff _).mpr (by simp)) fun w hw => ?_
  rw [mem_imaginary_realAxisSubmodule_iff] at hw
  change (⟪z - (z.im : ℂ) * Complex.I, w⟫_ℂ).re = 0
  simp [RCLike.inner_apply, Complex.mul_re, hw]

theorem rvdR_realAxisSubmodule :
    rvdR (H := ℂ) realAxisSubmodule = 1 := by
  ext z
  simp [rvdR_apply, projK_realAxisSubmodule, projIK_realAxisSubmodule, Complex.re_add_im]

theorem rvdT_realAxisSubmodule :
    rvdT (H := ℂ) realAxisSubmodule = (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
  ext z
  simp only [rvdT_apply, projK_realAxisSubmodule, projIK_realAxisSubmodule,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  exact Complex.ext (by simp) (by simp)

theorem j_conj_rvdR_realAxisSubmodule :
    (Complex.conjLIE.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ) *
        rvdR (H := ℂ) realAxisSubmodule *
        (Complex.conjLIE.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ) =
      (2 : ℝ) • (1 : ℂ →L[ℝ] ℂ) - rvdR (H := ℂ) realAxisSubmodule :=
  j_conj_rvdR realAxisSubmodule Complex.conjLIE
    (fun z => Complex.conj_conj z)
    (fun z => by simp)
    realAxisSubmodule_conj_map

theorem j_conj_rvdT_realAxisSubmodule :
    (Complex.conjLIE.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ) *
        rvdT (H := ℂ) realAxisSubmodule *
        (Complex.conjLIE.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ) =
      rvdT (H := ℂ) realAxisSubmodule :=
  j_conj_rvdT realAxisSubmodule Complex.conjLIE
    (fun z => Complex.conj_conj z)
    (fun z => by simp)
    realAxisSubmodule_conj_map

end ComplexWitness

end InfoGeometry.Modular.RieffelVanDaeleBoundedTomita
