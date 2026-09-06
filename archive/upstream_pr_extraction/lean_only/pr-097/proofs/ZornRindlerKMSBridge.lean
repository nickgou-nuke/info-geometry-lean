import proofs.ZornRindlerHorizon
import proofs.SupergradedCuntzBdG
import proofs.KreinVacuumKMSBridge

/-!
# Canonical Zorn Rindler/KMS bridge

This module connects three existing, independently compiled APIs on their
actual common types:

* the Zorn `DiracSpinor16` carrier and its nonzero directed operators `σ±`;
* the generic exponential `RindlerWeylFlow`;
* the generic finite cyclic and delta-regularized KMS contexts.

No new analytic KMS existence assertion is introduced.  The concrete state is
the finite-dimensional operator trace, while the delta-regularized results are
conditional only on the fields of the existing proof-carrying context.
-/

noncomputable section

open CanonicalZornCliffordRepresentation
open ZornCliffordParityAPI
open ZornChiralLightcone
open ZornLightconeCAR
open ZornRindlerHorizon
open SupergradedCuntzBdG
open InfoGeometry.Quantum.KreinVacuumKMSBridge

namespace ZornRindlerKMSBridge

/-- The repository's generic Rindler/Weyl flow specialized to Zorn Dirac
operators. -/
def zornOperatorRindlerFlow (ρ : ℝ)
    (A : Module.End ℂ DiracSpinor16) : Module.End ℂ DiracSpinor16 :=
  RindlerWeylFlow ρ A

@[simp] theorem zornOperatorRindlerFlow_zero
    (A : Module.End ℂ DiracSpinor16) :
    zornOperatorRindlerFlow 0 A = A := by
  exact RindlerWeylFlow_zero A

theorem zornOperatorRindlerFlow_add (ρ σ : ℝ)
    (A : Module.End ℂ DiracSpinor16) :
    zornOperatorRindlerFlow ρ (zornOperatorRindlerFlow σ A) =
      zornOperatorRindlerFlow (ρ + σ) A := by
  exact RindlerWeylFlow_add ρ σ A

/-- The upper Zorn lightcone block is transported by the existing exponential
Rindler/Weyl weight. -/
theorem zornOperatorRindlerFlow_sigmaPlus (ρ : ℝ) (r : Fin 3) :
    zornOperatorRindlerFlow ρ (lightconeSigmaPlus r) =
      qRapidity ρ • lightconeSigmaPlus r := by
  rfl

/-- The lower Zorn lightcone block is transported by the same generic scalar
flow; its intrinsic `-2` grading remains recorded by
`causal_order_minus_proof`. -/
theorem zornOperatorRindlerFlow_sigmaMinus (ρ : ℝ) (r : Fin 3) :
    zornOperatorRindlerFlow ρ (lightconeSigmaMinus r) =
      qRapidity ρ • lightconeSigmaMinus r := by
  rfl

/-- Finite trace KMS sector on the canonical sixteen-dimensional Zorn Dirac
carrier. -/
def diracTraceKMSSector (β : ℝ) : CyclicKMSSector DiracSpinor16 where
  beta := β
  omega := LinearMap.trace ℂ DiracSpinor16
  trace_cyclic := by
    intro A B
    simpa using
      (LinearMap.trace_mul_comm (R := ℂ) (M := DiracSpinor16) A B)

theorem sigmaPlus_chirality_anticommute (r : Fin 3) :
    lightconeSigmaPlus r * ZornCliffordParityAPI.chiralityOperator =
      -(ZornCliffordParityAPI.chiralityOperator * lightconeSigmaPlus r) := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  change lightconeSigmaPlus r (ZornCliffordParityAPI.chiralityOperator (S, C)) =
    -ZornCliffordParityAPI.chiralityOperator (lightconeSigmaPlus r (S, C))
  rw [ZornCliffordParityAPI.chiralityOperator_apply, lightconeSigmaPlus_apply,
    lightconeSigmaPlus_apply, ZornCliffordParityAPI.chiralityOperator_apply,
    CanonicalZornSpinChirality.cliffordMinus_neg]
  apply Prod.ext <;> simp

theorem sigmaMinus_chirality_anticommute (r : Fin 3) :
    lightconeSigmaMinus r * ZornCliffordParityAPI.chiralityOperator =
      -(ZornCliffordParityAPI.chiralityOperator * lightconeSigmaMinus r) := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  change lightconeSigmaMinus r (ZornCliffordParityAPI.chiralityOperator (S, C)) =
    -ZornCliffordParityAPI.chiralityOperator (lightconeSigmaMinus r (S, C))
  rw [ZornCliffordParityAPI.chiralityOperator_apply, lightconeSigmaMinus_apply,
    lightconeSigmaMinus_apply, ZornCliffordParityAPI.chiralityOperator_apply]
  apply Prod.ext <;> simp

/-- The finite trace state annihilates the upper odd Zorn block. -/
theorem diracTraceKMS_sigmaPlus_zero (β : ℝ) (r : Fin 3) :
    (diracTraceKMSSector β).omega (lightconeSigmaPlus r) = 0 := by
  exact kms_vacuum_is_finite
    (diracTraceKMSSector β) ZornCliffordParityAPI.chiralityOperator
      (lightconeSigmaPlus r)
    ZornCliffordParityAPI.chiralityOperator_sq
      (sigmaPlus_chirality_anticommute r)

/-- The finite trace state annihilates the lower odd Zorn block. -/
theorem diracTraceKMS_sigmaMinus_zero (β : ℝ) (r : Fin 3) :
    (diracTraceKMSSector β).omega (lightconeSigmaMinus r) = 0 := by
  exact kms_vacuum_is_finite
    (diracTraceKMSSector β) ZornCliffordParityAPI.chiralityOperator
      (lightconeSigmaMinus r)
    ZornCliffordParityAPI.chiralityOperator_sq
      (sigmaMinus_chirality_anticommute r)

/-- Trace cancellation is non-vacuous: the upper operator is nonzero. -/
theorem diracTraceKMS_sigmaPlus_nonvacuous (β : ℝ) (r : Fin 3) :
    lightconeSigmaPlus r ≠ 0 ∧
      (diracTraceKMSSector β).omega (lightconeSigmaPlus r) = 0 := by
  exact ⟨ZornChiralLightcone.lightconeSigmaPlus_ne_zero r,
    diracTraceKMS_sigmaPlus_zero β r⟩

/-- Trace cancellation is non-vacuous: the lower operator is nonzero. -/
theorem diracTraceKMS_sigmaMinus_nonvacuous (β : ℝ) (r : Fin 3) :
    lightconeSigmaMinus r ≠ 0 ∧
      (diracTraceKMSSector β).omega (lightconeSigmaMinus r) = 0 := by
  exact ⟨ZornChiralLightcone.lightconeSigmaMinus_ne_zero r,
    diracTraceKMS_sigmaMinus_zero β r⟩

/-- Existing delta-regularized KMS data annihilate the upper Zorn block. -/
theorem deltaRegularizedKMS_sigmaPlus_zero
    (K : DeltaRegularizedKMSContext DiracSpinor16) (r : Fin 3) :
    K.omega (lightconeSigmaPlus r) = 0 := by
  exact deltaRegularized_kms_vacuum_is_finite
    K ZornCliffordParityAPI.chiralityOperator (lightconeSigmaPlus r)
    ZornCliffordParityAPI.chiralityOperator_sq
      (sigmaPlus_chirality_anticommute r)

/-- Existing delta-regularized KMS data annihilate the lower Zorn block. -/
theorem deltaRegularizedKMS_sigmaMinus_zero
    (K : DeltaRegularizedKMSContext DiracSpinor16) (r : Fin 3) :
    K.omega (lightconeSigmaMinus r) = 0 := by
  exact deltaRegularized_kms_vacuum_is_finite
    K ZornCliffordParityAPI.chiralityOperator (lightconeSigmaMinus r)
    ZornCliffordParityAPI.chiralityOperator_sq
      (sigmaMinus_chirality_anticommute r)

end ZornRindlerKMSBridge

end noncomputable section
