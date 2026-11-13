/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.CSSKoszulExtension
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Scalar extension of coupled Koszul complexes

Entrywise evaluation of the finite free presentation is identified with actual
tensor extension of scalars. This comparison transports chain isomorphisms.
It does not assert that tensoring preserves exactness or commutes with homology.
-/

namespace InfoGeometry.Quantum.CSSKoszulExtension

open CategoryTheory Matrix TensorProduct
open scoped ChangeOfRings

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

theorem map_boundary1 (φ : R →+* S) (f x : Vec3 R) :
    φ (boundary1 f x) = boundary1 (φ ∘ f) (φ ∘ x) := by
  simp [boundary1, dotProduct]

theorem map_boundary2 (φ : R →+* S) (f x : Vec3 R) :
    φ ∘ boundary2 f x = boundary2 (φ ∘ f) (φ ∘ x) := by
  ext i
  fin_cases i <;> simp [boundary2, koszulMatrix, dotProduct, Fin.sum_univ_three]

theorem map_incoming (φ : R →+* S) (f a : Vec3 R) (x : Vec3 R × R) :
    (φ ∘ (incoming f a x).1, φ ∘ (incoming f a x).2) =
      incoming (φ ∘ f) (φ ∘ a) (φ ∘ x.1, φ x.2) := by
  rw [incoming_apply, incoming_apply]
  apply Prod.ext
  · ext i
    have h := congrFun (map_boundary2 φ f x.1) i
    simpa using congrArg (fun z => z + φ x.2 * φ (a i)) h
  · ext i
    simp

theorem map_outgoing (φ : R →+* S) (f a : Vec3 R) (x : Vec3 R × Vec3 R) :
    (φ (outgoing f a x).1, φ ∘ (outgoing f a x).2) =
      outgoing (φ ∘ f) (φ ∘ a) (φ ∘ x.1, φ ∘ x.2) := by
  rw [outgoing_apply, outgoing_apply]
  exact Prod.ext (by simp only [map_sub, map_boundary1]) (map_boundary2 φ f x.2)

/-- Tensor extension of the incoming four-coordinate free module. -/
noncomputable def sourceBaseChangeEquiv (φ : R →+* S) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R (Vec3 R × R)) ≃ₗ[S]
      (Vec3 S × S) := by
  letI := φ.toAlgebra
  exact (TensorProduct.prodRight R S S (Vec3 R) R).trans
    ((TensorProduct.piScalarRight R S S (Fin 3)).prodCongr
      (TensorProduct.AlgebraTensorModule.rid R S S))

/-- Tensor extension of the middle six-coordinate free module. -/
noncomputable def middleBaseChangeEquiv (φ : R →+* S) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R (Vec3 R × Vec3 R)) ≃ₗ[S]
      (Vec3 S × Vec3 S) := by
  letI := φ.toAlgebra
  exact (TensorProduct.prodRight R S S (Vec3 R) (Vec3 R)).trans
    ((TensorProduct.piScalarRight R S S (Fin 3)).prodCongr
      (TensorProduct.piScalarRight R S S (Fin 3)))

/-- Tensor extension of the outgoing four-coordinate free module. -/
noncomputable def targetBaseChangeEquiv (φ : R →+* S) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R (R × Vec3 R)) ≃ₗ[S]
      (S × Vec3 S) := by
  letI := φ.toAlgebra
  exact (TensorProduct.prodRight R S S R (Vec3 R)).trans
    ((TensorProduct.AlgebraTensorModule.rid R S S).prodCongr
      (TensorProduct.piScalarRight R S S (Fin 3)))

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem sourceBaseChangeEquiv_one_tmul (φ : R →+* S) (x : Vec3 R × R) :
    sourceBaseChangeEquiv φ ((1 : S) ⊗ₜ[R,φ] x) = (φ ∘ x.1, φ x.2) := by
  let := φ.toAlgebra
  change ((TensorProduct.piScalarRight R S S (Fin 3)) ((1 : S) ⊗ₜ[R] x.1),
    (TensorProduct.AlgebraTensorModule.rid R S S) ((1 : S) ⊗ₜ[R] x.2)) = _
  simp [Algebra.smul_def]
  exact ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem middleBaseChangeEquiv_one_tmul (φ : R →+* S)
    (x : Vec3 R × Vec3 R) :
    middleBaseChangeEquiv φ ((1 : S) ⊗ₜ[R,φ] x) = (φ ∘ x.1, φ ∘ x.2) := by
  let := φ.toAlgebra
  change ((TensorProduct.piScalarRight R S S (Fin 3)) ((1 : S) ⊗ₜ[R] x.1),
    (TensorProduct.piScalarRight R S S (Fin 3)) ((1 : S) ⊗ₜ[R] x.2)) = _
  simp [Algebra.smul_def]
  exact ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem targetBaseChangeEquiv_one_tmul (φ : R →+* S) (x : R × Vec3 R) :
    targetBaseChangeEquiv φ ((1 : S) ⊗ₜ[R,φ] x) = (φ x.1, φ ∘ x.2) := by
  let := φ.toAlgebra
  change ((TensorProduct.AlgebraTensorModule.rid R S S) ((1 : S) ⊗ₜ[R] x.1),
    (TensorProduct.piScalarRight R S S (Fin 3)) ((1 : S) ⊗ₜ[R] x.2)) = _
  simp [Algebra.smul_def]
  exact ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the displayed coefficients agrees with actual scalar extension
of the short complex, including the coupling terms. -/
noncomputable def baseChangeIso (φ : R →+* S) (f a : Vec3 R) :
    (complex f a).map (ModuleCat.extendScalars φ) ≅ complex (φ ∘ f) (φ ∘ a) :=
  ShortComplex.isoMk (sourceBaseChangeEquiv φ).toModuleIso
    (middleBaseChangeEquiv φ).toModuleIso (targetBaseChangeEquiv φ).toModuleIso
    (by
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change incoming (φ ∘ f) (φ ∘ a)
          (sourceBaseChangeEquiv φ ((1 : S) ⊗ₜ[R,φ] x)) =
        middleBaseChangeEquiv φ ((1 : S) ⊗ₜ[R,φ] incoming f a x)
      rw [sourceBaseChangeEquiv_one_tmul, middleBaseChangeEquiv_one_tmul]
      exact (map_incoming φ f a x).symm)
    (by
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change outgoing (φ ∘ f) (φ ∘ a)
          (middleBaseChangeEquiv φ ((1 : S) ⊗ₜ[R,φ] x)) =
        targetBaseChangeEquiv φ ((1 : S) ⊗ₜ[R,φ] outgoing f a x)
      rw [middleBaseChangeEquiv_one_tmul, targetBaseChangeEquiv_one_tmul]
      exact (map_outgoing φ f a x).symm)

/-- Scalar extension preserves an actual chain isomorphism; no flatness is
needed for this statement. -/
noncomputable def specializeIso (φ : R →+* S) {f a f' a' : Vec3 R}
    (e : complex f a ≅ complex f' a') :
    complex (φ ∘ f) (φ ∘ a) ≅ complex (φ ∘ f') (φ ∘ a') :=
  (baseChangeIso φ f a).symm ≪≫
    (ModuleCat.extendScalars φ).mapShortComplex.mapIso e ≪≫
      baseChangeIso φ f' a'

end InfoGeometry.Quantum.CSSKoszulExtension
