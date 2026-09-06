import Mathlib
import proofs.KreinVacuumPropagator
import proofs.AnomalousKMSFlow

noncomputable section

namespace InfoGeometry.Quantum.KreinVacuumKMSBridge

open Complex
open InfoGeometry.Quantum.KreinVacuumPropagator

/--
Tracial KMS sector at inverse temperature `β`.

This structure assumes only the displayed linear functional and tracial
cyclicity law.  It does not assert existence or uniqueness of a global KMS
state; finite-dimensional instances below supply the ordinary matrix trace.
-/
structure CyclicKMSSector (H : Type*) [AddCommGroup H] [Module ℂ H] where
  beta : ℝ
  omega : Module.End ℂ H →ₗ[ℂ] ℂ
  trace_cyclic : ∀ A B : Module.End ℂ H, omega (A * B) = omega (B * A)

/--
Delta-regularized KMS sector.

A general KMS functional is twisted-cyclic: `ω(A B) = ω(B σ(A))` for the
chosen modular twist `σ`.  This context assumes neither pointwise equality
`σ(A) = A` nor a global analytic modular-flow construction.  Ordinary cyclicity
is derived only for operators whose regularized defect `σ(A) - A` has zero
pairing against the tested right factor.
-/
structure DeltaRegularizedKMSContext (H : Type*) [AddCommGroup H] [Module ℂ H] where
  omega : Module.End ℂ H →ₗ[ℂ] ℂ
  modularTwist : Module.End ℂ H → Module.End ℂ H
  kms_twisted_cyclic :
    ∀ A B : Module.End ℂ H, omega (A * B) = omega (B * modularTwist A)
  regularized_defect_vanishes :
    ∀ A B : Module.End ℂ H, omega (B * (modularTwist A - A)) = 0

/--
For a delta-regularized sector, twisted cyclicity plus the stated defect
annihilation hypothesis gives ordinary cyclicity for the tested pair.
-/
theorem cyclic_of_deltaRegularized
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (K : DeltaRegularizedKMSContext H) :
    ∀ A B : Module.End ℂ H, K.omega (A * B) = K.omega (B * A) := by
  intro A B
  rw [K.kms_twisted_cyclic A B]
  have hsplit :
      B * K.modularTwist A = B * A + B * (K.modularTwist A - A) := by
    noncomm_ring
  rw [hsplit]
  simp [K.regularized_defect_vanishes A B]

/--
Delta-regularized algebraic vacuum cancellation.

The KMS functional is used only through the displayed twisted-cyclicity and
defect-annihilation assumptions.  Under those assumptions, an involutive chiral
parity `ε` and an odd propagator `G` have zero state-value.
-/
theorem deltaRegularized_kms_vacuum_is_finite
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (K : DeltaRegularizedKMSContext H)
    (ε G : Module.End ℂ H)
    (hEpsilonSq : ε * ε = 1)
    (hAnti : G * ε = -(ε * G)) :
    K.omega G = 0 := by
  let C : ChiralPropagatorContext H :=
    { epsilon := ε
      propagator := G
      tr := K.omega
      epsilon_sq := hEpsilonSq
      propagator_chiral_anticommute := hAnti
      trace_cyclic := cyclic_of_deltaRegularized K }
  exact uv_divergence_cancellation (C := C)

/--
Algebraic vacuum cancellation in a cyclic KMS sector.

Assuming the displayed tracial cyclicity law, a chiral parity `ε`, and a
propagator `G` satisfying the same algebraic oddness used in
`KreinVacuumPropagator`, the state-value of `G` vanishes.

This wrapper is tracial.  For a twisted KMS setup, use
`deltaRegularized_kms_vacuum_is_finite`, where cyclicity is derived from the
stated twisted relation and the regularized-defect annihilation hypothesis.
-/
theorem kms_vacuum_is_finite
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (K : CyclicKMSSector H)
    (ε G : Module.End ℂ H)
    (hEpsilonSq : ε * ε = 1)
    (hAnti : G * ε = -(ε * G)) :
    K.omega G = 0 := by
  let C : ChiralPropagatorContext H :=
    { epsilon := ε
      propagator := G
      tr := K.omega
      epsilon_sq := hEpsilonSq
      propagator_chiral_anticommute := hAnti
      trace_cyclic := K.trace_cyclic }
  exact uv_divergence_cancellation (C := C)

/--
Concrete finite tracial KMS sector on `Fin 2 → ℂ`.

The functional is the ordinary finite-dimensional trace.  The parameter `β` is
recorded as thermodynamic data, but the proof uses only the finite cyclic trace
identity from Mathlib.
-/
def finiteTraceKMSSector (β : ℝ) : CyclicKMSSector (Fin 2 → ℂ) where
  beta := β
  omega := LinearMap.trace ℂ (Fin 2 → ℂ)
  trace_cyclic := by
    intro A B
    simpa using (LinearMap.trace_mul_comm (R := ℂ) (M := Fin 2 → ℂ) A B)

/-!
Concrete finite Klein/Tomita sectors through `DeltaRegularizedKMSContext`.

These statements are finite algebraic consequences of the fields in
`DeltaRegularizedKMSContext`: twisted cyclicity and vanishing pairing with the
regularized modular defect.
-/

/--
Concrete finite Klein instantiation in a delta-regularized KMS sector:
the state-value on the `Γ`-odd propagator `J` vanishes.
-/
theorem deltaRegularized_kms_vacuum_is_finite_klein
    (K : DeltaRegularizedKMSContext (Fin 2 → ℂ)) :
    K.omega AnomalousKMSFlow.kleinBottleJ = 0 := by
  simpa using
    (deltaRegularized_kms_vacuum_is_finite K
      AnomalousKMSFlow.kleinBottleΓ AnomalousKMSFlow.kleinBottleJ
      AnomalousKMSFlow.kleinBottleΓ_sq
      InfoGeometry.Quantum.KreinVacuumPropagator.kleinBottleJ_chiral_anticommute)

/--
Concrete finite TOMITA instantiation in a delta-regularized KMS sector:
the state-value on the TOMITA-canonical `J` vanishes.
-/
theorem deltaRegularized_kms_vacuum_is_finite_tomita
    (K : DeltaRegularizedKMSContext (Fin 2 → ℂ)) :
    K.omega AnomalousKMSFlow.tomitaBottleJ = 0 := by
  simpa using
    (deltaRegularized_kms_vacuum_is_finite K
      AnomalousKMSFlow.tomitaBottleΓ AnomalousKMSFlow.tomitaBottleJ
      (by simpa [AnomalousKMSFlow.tomitaBottleΓ_eq_kleinBottleΓ] using
        AnomalousKMSFlow.kleinBottleΓ_sq)
      InfoGeometry.Quantum.KreinVacuumPropagator.tomitaBottleJ_chiral_anticommute)

/--
Concrete finite Klein instantiation: the state-value on the `Γ`-odd propagator
`J` vanishes.
-/
theorem kms_vacuum_is_finite_klein (β : ℝ) :
    (finiteTraceKMSSector β).omega AnomalousKMSFlow.kleinBottleJ = 0 := by
  simpa using
    (kms_vacuum_is_finite (K := finiteTraceKMSSector β)
      AnomalousKMSFlow.kleinBottleΓ AnomalousKMSFlow.kleinBottleJ
      AnomalousKMSFlow.kleinBottleΓ_sq
      InfoGeometry.Quantum.KreinVacuumPropagator.kleinBottleJ_chiral_anticommute)

/--
Concrete finite TOMITA instantiation: the state-value on the TOMITA-canonical
`J` vanishes.
-/
theorem kms_vacuum_is_finite_tomita (β : ℝ) :
    (finiteTraceKMSSector β).omega AnomalousKMSFlow.tomitaBottleJ = 0 := by
  simpa using
    (kms_vacuum_is_finite (K := finiteTraceKMSSector β)
      AnomalousKMSFlow.tomitaBottleΓ AnomalousKMSFlow.tomitaBottleJ
      (by simpa [AnomalousKMSFlow.tomitaBottleΓ_eq_kleinBottleΓ] using AnomalousKMSFlow.kleinBottleΓ_sq)
      InfoGeometry.Quantum.KreinVacuumPropagator.tomitaBottleJ_chiral_anticommute)

end InfoGeometry.Quantum.KreinVacuumKMSBridge
