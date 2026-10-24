/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum
import InfoGeometry.Modular.PositiveStatePullback
import Mathlib.Analysis.Normed.Operator.Extend
import InfoGeometry.Canonical.FilteredGNSRepresentation

/-!
# Completed complex GNS covariance

Uncompiled sandbox candidate. The input compatibility is equality of positive
functionals. Native `PositiveStatePullback.pullback` supplies an actual pullback.
Both pre-GNS spaces remain seminormed; extension targets are the native GNS
completions. No normalization or faithfulness is assumed.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CompletedGNSCovariance

open UniformSpace
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ ψ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] A)
variable (h : ∀ a, ψ a = φ (e a))

/-- The star algebra equivalence preserves the pulled-back GNS seminorm. -/
def preEquiv : ψ.PreGNS ≃ₗᵢ[ℂ] φ.PreGNS where
  toLinearEquiv := ψ.ofPreGNS.trans (e.toAlgEquiv.toLinearEquiv.trans φ.toPreGNS)
  norm_map' x := by
    change Real.sqrt (φ (star (e (ψ.ofPreGNS x)) * e (ψ.ofPreGNS x))).re =
      Real.sqrt (ψ (star (ψ.ofPreGNS x) * ψ.ofPreGNS x)).re
    rw [h, map_mul, map_star]

@[simp] theorem preEquiv_toPreGNS (a : A) :
    preEquiv φ ψ e h (ψ.toPreGNS a) = φ.toPreGNS (e a) := rfl

@[simp] theorem preEquiv_symm_toPreGNS (a : A) :
    (preEquiv φ ψ e h).symm (φ.toPreGNS a) = ψ.toPreGNS (e.symm a) := rfl

/-- Extend into the complete normed target, not into its seminormed pre-space. -/
def forward : ψ.GNS →ₗᵢ[ℂ] φ.GNS :=
  ((Completion.toComplₗᵢ : φ.PreGNS →ₗᵢ[ℂ] φ.GNS).comp
    (preEquiv φ ψ e h).toLinearIsometry).fromCompletion

/-- The inverse is independently extended into the other native completion. -/
def backward : φ.GNS →ₗᵢ[ℂ] ψ.GNS :=
  ((Completion.toComplₗᵢ : ψ.PreGNS →ₗᵢ[ℂ] ψ.GNS).comp
    (preEquiv φ ψ e h).symm.toLinearIsometry).fromCompletion

@[simp] theorem forward_coe (x : ψ.PreGNS) :
    forward φ ψ e h (x : ψ.GNS) = (preEquiv φ ψ e h x : φ.GNS) := by
  exact LinearIsometry.fromCompletion_apply_coe _ x

@[simp] theorem backward_coe (x : φ.PreGNS) :
    backward φ ψ e h (x : φ.GNS) = ((preEquiv φ ψ e h).symm x : ψ.GNS) := by
  exact LinearIsometry.fromCompletion_apply_coe _ x

theorem backward_forward (x : ψ.GNS) :
    backward φ ψ e h (forward φ ψ e h x) = x := by
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((backward φ ψ e h).continuous.comp (forward φ ψ e h).continuous)
        continuous_id
  | ih x => simp only [forward_coe, backward_coe, LinearIsometryEquiv.symm_apply_apply]

theorem forward_backward (x : φ.GNS) :
    forward φ ψ e h (backward φ ψ e h x) = x := by
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((forward φ ψ e h).continuous.comp (backward φ ψ e h).continuous)
        continuous_id
  | ih x => simp only [backward_coe, forward_coe, LinearIsometryEquiv.apply_symm_apply]

/-- Covariance on mathlib's actual completed complex GNS spaces. -/
def completedEquiv : ψ.GNS ≃ₗᵢ[ℂ] φ.GNS where
  toLinearEquiv :=
    { (forward φ ψ e h).toLinearMap with
      invFun := backward φ ψ e h
      left_inv := backward_forward φ ψ e h
      right_inv := forward_backward φ ψ e h }
  norm_map' := (forward φ ψ e h).norm_map

@[simp] theorem completedEquiv_toPreGNS (a : A) :
    completedEquiv φ ψ e h (ψ.toPreGNS a : ψ.GNS) =
      (φ.toPreGNS (e a) : φ.GNS) := by
  change forward φ ψ e h (ψ.toPreGNS a : ψ.GNS) = _
  rw [forward_coe, preEquiv_toPreGNS]

@[simp] theorem completedEquiv_symm_toPreGNS (a : A) :
    (completedEquiv φ ψ e h).symm (φ.toPreGNS a : φ.GNS) =
      (ψ.toPreGNS (e.symm a) : ψ.GNS) := by
  change backward φ ψ e h (φ.toPreGNS a : φ.GNS) = _
  rw [backward_coe, preEquiv_symm_toPreGNS]

theorem completedEquiv_vacuum :
    completedEquiv φ ψ e h (PositiveLinearMapGNSVacuum.gnsVacuum ψ) =
      PositiveLinearMapGNSVacuum.gnsVacuum φ := by
  simpa only [PositiveLinearMapGNSVacuum.gnsVacuum,
    PositiveLinearMapGNSVacuum.preGNSVacuum, map_one] using
    completedEquiv_toPreGNS φ ψ e h (1 : A)

/-- The completed equivalence intertwines the representations on every vector. -/
theorem completedEquiv_intertwines (a : A) (x : ψ.GNS) :
    completedEquiv φ ψ e h (ψ.gnsStarAlgHom a x) =
      φ.gnsStarAlgHom (e a) (completedEquiv φ ψ e h x) := by
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((completedEquiv φ ψ e h).continuous.comp (ψ.gnsStarAlgHom a).continuous)
        ((φ.gnsStarAlgHom (e a)).continuous.comp (completedEquiv φ ψ e h).continuous)
  | ih x =>
      obtain ⟨b, rfl⟩ := ψ.toPreGNS.surjective x
      simp [PositiveLinearMap.gnsStarAlgHom,
        PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
        PositiveLinearMap.leftMulMapPreGNS, map_mul]

open CStarStateColimit.Native in
/-- On normalized states, the completed equivalence agrees everywhere with
the existing native filtered GNS transport. -/
theorem completedEquiv_eq_filteredGNSMap (ω : State A)
    (x : (ω.restrict e.toStarAlgHom).functional.GNS) :
    completedEquiv ω.functional (ω.restrict e.toStarAlgHom).functional e
        (fun a => State.restrict_apply e.toStarAlgHom ω a) x =
      FilteredGNS.gnsMap e.toStarAlgHom ω x := by
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (completedEquiv ω.functional (ω.restrict e.toStarAlgHom).functional e
          (fun a => State.restrict_apply e.toStarAlgHom ω a)).continuous
        (FilteredGNS.gnsMap_isometry e.toStarAlgHom ω).continuous
  | ih x =>
      obtain ⟨a, rfl⟩ := (ω.restrict e.toStarAlgHom).functional.toPreGNS.surjective x
      rw [completedEquiv_toPreGNS, FilteredGNS.gnsMap_toPreGNS]

end InfoGeometry.OperatorAlgebra.CompletedGNSCovariance
