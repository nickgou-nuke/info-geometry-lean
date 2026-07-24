import Mathlib
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Canonical.TensorColimitExpectation
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.KMSTraceColimit

/-!
# CPT/KMS Colimit Tower Construction

This module connects the finite-stage normalized KMS trace readback layer
(`KMSTraceColimit.lean`) with the algebraic colimit sequence transport layer
(`TensorColimitExpectation.lean`) for the diagonal algebra tower.

Specifically, it establishes that the finite-stage normalized KMS states
form a compatible functional family, allowing the construction of the
limiting state on the infinite-dimensional direct-limit CAR/diagonal boundary algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.CPTKMSColimitTower

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.KMSTraceColimit
open InfoGeometry.Canonical.TensorColimitExpectation

/-- The diagonal successor embedding viewed as an algebra homomorphism over `ℂ`. -/
def diagBondAlg (n : ℕ) : DiagAlg n →ₐ[ℂ] DiagAlg (n + 1) where
  toFun := diagEmbedSucc n
  map_one' := diagEmbedSucc_one n
  map_mul' f g := diagEmbedSucc_mul n f g
  map_zero' := diagEmbedSucc_zero n
  map_add' f g := diagEmbedSucc_add n f g
  commutes' c := by
    ext w
    rfl

/-- The finite-stage normalized KMS trace viewed as a linear map over `ℂ`. -/
def normalizedTraceLinear (n : ℕ) : DiagAlg n →ₗ[ℂ] ℂ where
  toFun := normalizedTrace n
  map_add' f g := by
    dsimp [normalizedTrace]
    rw [Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    dsimp [normalizedTrace]
    rw [← Finset.mul_sum]
    ring

/-- The family of finite-stage KMS traces is algebraically compatible. -/
theorem kms_functional_family_compat (n : ℕ) (f : DiagAlg n) :
    normalizedTraceLinear (n + 1) (diagBondAlg n f) = normalizedTraceLinear n f := by
  change normalizedTrace (n + 1) (diagEmbedSucc n f) = normalizedTrace n f
  exact normalizedTrace_embed n f

/-- **Theorem: CPT/KMS Compatible Functional Family**
    The collection of normalized KMS traces at every finite stage n forms a compatible
    functional family over the diagonal algebra tower. -/
def kmsCompatibleFunctionalFamily : CompatibleFunctionalFamily (A := DiagAlg) diagBondAlg where
  omega n := normalizedTraceLinear n
  compatible n f := kms_functional_family_compat n f

/-- The cylinder map as an algebra homomorphism over `ℂ`. -/
noncomputable def cylinderAlg (n : ℕ) : DiagAlg n →ₐ[ℂ] (CantorBoundary → ℂ) where
  toFun := cylinder n
  map_one' := cylinder_one n
  map_mul' f g := cylinder_mul n f g
  map_zero' := by ext; rfl
  map_add' f g := cylinder_add n f g
  commutes' c := by ext; rfl

/-- **Theorem: MASA Inductive Limit Package**
    The diagonal algebra tower with successor embeddings and cylinder maps
    forms a valid algebraic tensor inductive limit carrier. -/
noncomputable def diagonalUHFInductiveLimit : TensorInductiveLimit (R := ℂ) (A := DiagAlg) diagBondAlg where
  AInf := CantorBoundary → ℂ
  instSemiring := inferInstance
  instAlgebra := inferInstance
  inj n := cylinderAlg n
  inj_compat n f := cylinder_compatible_succ n f

end InfoGeometry.Canonical.CPTKMSColimitTower

end noncomputable section
