import Mathlib
import InfoGeometry.Categorical.QuantumG2RMatrixBraidingDatum

/-!
# Tensor transport for checked R-operators

This file contains the representation-theoretic part of the Spin/Fock bridge:
an invertible linear identification transports an operator, its intertwining
identity, and Yang--Baxter coherence.  It deliberately does not assert that a
Cuntz algebra or a Spin carrier has already been identified with the other.
-/

namespace InfoGeometry.Categorical.QuantumG2RMatrixTensorTransport

open TensorProduct

variable {𝕜 A B : Type*}
variable [CommRing 𝕜]
variable [AddCommGroup A] [Module 𝕜 A]
variable [AddCommGroup B] [Module 𝕜 B]

/-- Conjugation of an endomorphism along a linear equivalence. -/
def conjugate (J : A ≃ₗ[𝕜] B) (f : A ≃ₗ[𝕜] A) : B ≃ₗ[𝕜] B :=
  J.symm.trans (f.trans J)

theorem intertwining_conjugate (J : A ≃ₗ[𝕜] B) (f : A ≃ₗ[𝕜] A) :
    J.trans (conjugate J f) = f.trans J := by
  ext x
  simp [conjugate, LinearEquiv.trans_apply]

theorem conjugate_comp (J : A ≃ₗ[𝕜] B)
    (f g : A ≃ₗ[𝕜] A) :
    conjugate J (f.trans g) = (conjugate J f).trans (conjugate J g) := by
  ext x
  simp [conjugate, LinearEquiv.trans_apply]

theorem conjugate_yangBaxter
    (J : A ≃ₗ[𝕜] B)
    (R S : A ≃ₗ[𝕜] A)
    (h : R.toLinearMap ∘ₗ S.toLinearMap ∘ₗ R.toLinearMap =
      S.toLinearMap ∘ₗ R.toLinearMap ∘ₗ S.toLinearMap) :
    (conjugate J R).toLinearMap ∘ₗ (conjugate J S).toLinearMap ∘ₗ
        (conjugate J R).toLinearMap =
      (conjugate J S).toLinearMap ∘ₗ (conjugate J R).toLinearMap ∘ₗ
        (conjugate J S).toLinearMap := by
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun h (J.symm x)
  simpa [conjugate, LinearEquiv.trans_apply, LinearMap.comp_apply] using
    congrArg (fun y => J y) hx

/-- Tensor-square transport of a carrier equivalence. -/
def tensorSquareEquiv
    {V W : Type*} [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W]
    (J : V ≃ₗ[𝕜] W) :
    (V ⊗[𝕜] V) ≃ₗ[𝕜] (W ⊗[𝕜] W) :=
  TensorProduct.congr J J

/-- Tensor-cube transport on the right-associated tensor product. -/
def tensorCubeEquiv
    {V W : Type*} [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W]
    (J : V ≃ₗ[𝕜] W) :
    (V ⊗[𝕜] (V ⊗[𝕜] V)) ≃ₗ[𝕜]
      (W ⊗[𝕜] (W ⊗[𝕜] W)) :=
  TensorProduct.congr J (TensorProduct.congr J J)

/-- Transport a local R-operator to the target tensor square. -/
def transportedR
    {V W : Type*} [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W]
    (J : V ≃ₗ[𝕜] W)
    (R : (V ⊗[𝕜] V) ≃ₗ[𝕜] (V ⊗[𝕜] V)) :
    (W ⊗[𝕜] W) ≃ₗ[𝕜] (W ⊗[𝕜] W) :=
  conjugate (tensorSquareEquiv J) R

theorem transportedR_intertwines
    {V W : Type*} [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W]
    (J : V ≃ₗ[𝕜] W)
    (R : (V ⊗[𝕜] V) ≃ₗ[𝕜] (V ⊗[𝕜] V)) :
    (tensorSquareEquiv J).trans (transportedR J R) =
      R.trans (tensorSquareEquiv J) := by
  exact intertwining_conjugate (tensorSquareEquiv J) R

theorem transportedR_yangBaxter
    {V W : Type*} [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W]
    (J : V ≃ₗ[𝕜] W)
    (R S : (V ⊗[𝕜] V) ≃ₗ[𝕜] (V ⊗[𝕜] V))
    (h : R.toLinearMap ∘ₗ S.toLinearMap ∘ₗ R.toLinearMap =
      S.toLinearMap ∘ₗ R.toLinearMap ∘ₗ S.toLinearMap) :
    (transportedR J R).toLinearMap ∘ₗ (transportedR J S).toLinearMap ∘ₗ
        (transportedR J R).toLinearMap =
      (transportedR J S).toLinearMap ∘ₗ (transportedR J R).toLinearMap ∘ₗ
        (transportedR J S).toLinearMap := by
  exact conjugate_yangBaxter (tensorSquareEquiv J) R S h

end InfoGeometry.Categorical.QuantumG2RMatrixTensorTransport
