/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.FreeSupermoduleChart
import Mathlib.LinearAlgebra.StdBasis

/-!
# Scalar extension of finite free left-module maps

Right coefficients are transported along arbitrary ring homomorphisms. The
native free-module basis proves uniqueness, so neither surjectivity nor
injectivity of the coefficient homomorphism is required.
-/

namespace InfoGeometry.SuperGrassmannian.FiniteFreeCoefficientChange

open GraphChartBaseChange FreeSupermoduleChart

variable {A B I J K : Type*} [Ring A] [Ring B]
  [Fintype I] [DecidableEq I]

/-- Transport the coefficients in the native free-module basis. -/
def mapHom (φ : A →+* B) (f : (I → A) →ₗ[A] (J → A)) : (I → B) →ₗ[B] (J → B) :=
  coordinateLinearMap (fun i j => φ (f (Pi.single i 1) j))

/-- Evaluation on vectors from the source algebra commutes with scalar extension. -/
theorem mapHom_natural (φ : A →+* B) (f : (I → A) →ₗ[A] (J → A)) (x : I → A) :
    mapHom φ f (fun i => φ (x i)) = fun j => φ (f x j) := by
  unfold mapHom
  rw [coordinateLinearMap_natural, coordinateLinearMap_eq_piRing]
  change (fun j => φ (((LinearEquiv.piRing A (J → A) I ℤ).symm
    ((LinearEquiv.piRing A (J → A) I ℤ) f)) x j)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The source-algebra basis already determines a target-linear map. -/
theorem mapHom_unique (φ : A →+* B) (f : (I → A) →ₗ[A] (J → A))
    (g : (I → B) →ₗ[B] (J → B))
    (h : ∀ x, g (fun i => φ (x i)) = fun j => φ (f x j)) : g = mapHom φ f := by
  apply (Pi.basisFun B I).ext
  intro i
  have he := (h (Pi.single i 1)).trans (mapHom_natural φ f (Pi.single i 1)).symm
  have hv : (fun j => φ ((Pi.single i (1 : A) : I → A) j)) =
      (Pi.single i (1 : B) : I → B) := by
    funext j
    simp [Pi.single_apply]
  rw [hv] at he
  simpa only [Pi.basisFun_apply] using he

@[simp] theorem mapHom_id (φ : A →+* B) :
    mapHom (I := I) φ (LinearMap.id : (I → A) →ₗ[A] (I → A)) = LinearMap.id := by
  symm
  apply mapHom_unique
  intro x
  rfl

/-- Composition order is preserved over noncommutative coefficient rings. -/
theorem mapHom_comp [Fintype J] [DecidableEq J] (φ : A →+* B)
    (f : (I → A) →ₗ[A] (J → A)) (g : (J → A) →ₗ[A] (K → A)) :
    mapHom φ (g.comp f) = (mapHom φ g).comp (mapHom φ f) := by
  symm
  apply mapHom_unique
  intro x
  simp only [LinearMap.comp_apply, mapHom_natural]

/-- A genuine inverse is transported, rather than assumed at the target ring. -/
def mapEquiv (φ : A →+* B) (e : (I → A) ≃ₗ[A] (I → A)) :
    (I → B) ≃ₗ[B] (I → B) where
  toLinearMap := mapHom φ e.toLinearMap
  invFun := mapHom φ e.symm.toLinearMap
  left_inv x := by
    have h := mapHom_comp φ e.toLinearMap e.symm.toLinearMap
    simpa using (LinearMap.congr_fun h x).symm
  right_inv x := by
    have h := mapHom_comp φ e.symm.toLinearMap e.toLinearMap
    simpa using (LinearMap.congr_fun h x).symm

variable [Fintype J] [DecidableEq J]

/-- Coefficient extension of an ambient operator, using its four native blocks. -/
def mapPairHom (φ : A →+* B) (G : Module.End A ((I → A) × (J → A))) :
    Module.End B ((I → B) × (J → B)) :=
  ((mapHom φ ((LinearMap.fst A _ _).comp (G.comp (LinearMap.inl A _ _)))).coprod
    (mapHom φ ((LinearMap.fst A _ _).comp (G.comp (LinearMap.inr A _ _))))).prod
  ((mapHom φ ((LinearMap.snd A _ _).comp (G.comp (LinearMap.inl A _ _)))).coprod
    (mapHom φ ((LinearMap.snd A _ _).comp (G.comp (LinearMap.inr A _ _)))))

/-- The ambient scalar-extension square commutes. -/
theorem mapPairHom_natural (φ : A →+* B) (G : Module.End A ((I → A) × (J → A)))
    (z : (I → A) × (J → A)) :
    mapPairHom φ G (coefficientMap φ z) = coefficientMap φ (G z) := by
  have hs : G (z.1, 0) + G (0, z.2) = G z := by rw [← map_add]; simp
  apply Prod.ext <;> funext j
  · have h := congrFun (congrArg Prod.fst hs) j
    simpa [mapPairHom, coefficientMap, mapHom_natural] using congrArg φ h
  · have h := congrFun (congrArg Prod.snd hs) j
    simpa [mapPairHom, coefficientMap, mapHom_natural] using congrArg φ h

end InfoGeometry.SuperGrassmannian.FiniteFreeCoefficientChange
