import InfoGeometry.Quantum.GeometricTensor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.GeometricTensorTransport
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.BogoliubovProjectorTransport

open InfoGeometry.Quantum
open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovProjectorTransport

namespace InfoGeometry.Quantum.Test

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
**ofMajorana metric projection**:
Verified that the `g` accessor on the `ofMajorana` constructor correctly
projects the original metric.
-/
theorem ofMajorana_g_eq_metric
    (metric : LinearMap.BilinForm ℝ H₂)
    (h_symm : metric.IsSymm)
    (h_skew : ∀ u v, metric (modularComplexI u) v = -metric u (modularComplexI v)) :
    (GeometricQuantumTensor.ofMajorana metric h_symm h_skew).metric = metric := rfl

/--
**ofMajorana compatibility**:
Verified that the induced Berry form Ω matches the metric precomposed with K.
-/
theorem ofMajorana_compat
    (metric : LinearMap.BilinForm ℝ H₂)
    (h_symm : metric.IsSymm)
    (h_skew : ∀ u v, metric (modularComplexI u) v = -metric u (modularComplexI v)) :
    let Q := GeometricQuantumTensor.ofMajorana metric h_symm h_skew
    ∀ u v, Q.berry u v = Q.metric (modularComplexI u) v := by
  intro Q u v
  exact Q.compat u v

/--
**ofMajorana compatibility, owner-name form**:
Verified that the induced Berry form Ω matches the metric precomposed with
the root owner phase axis `complex_i`.
-/
theorem ofMajorana_compat_complex_i
    (metric : LinearMap.BilinForm ℝ H₂)
    (h_symm : metric.IsSymm)
    (h_skew : ∀ u v, metric (modularComplexI u) v = -metric u (modularComplexI v)) :
    let Q := GeometricQuantumTensor.ofMajorana metric h_symm h_skew
    ∀ u v, Q.berry u v = Q.metric (complex_i (E := E) u) v := by
  intro Q u v
  rw [← InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i (E := E)]
  exact Q.compat u v

/--
**Berry Alternation**:
Verified that the generated Berry form is indeed alternating.
-/
theorem ofMajorana_Ω_alt
    (metric : LinearMap.BilinForm ℝ H₂)
    (h_symm : metric.IsSymm)
    (h_skew : ∀ u v, metric (modularComplexI u) v = -metric u (modularComplexI v)) :
    (GeometricQuantumTensor.ofMajorana metric h_symm h_skew).berry.IsAlt := 
  (GeometricQuantumTensor.ofMajorana metric h_symm h_skew).berry_alt

omit [CompleteSpace E] in
/--
**Transport Commutation Test**:
Verified that the modular transport preserves the sector decomposition
when the generator commutes with the projector.
-/
theorem modularTransport_commutes_with_projector
    (hMod : EndH) (t : ℝ)
    (h_comm : Commute (spectralPlusProj (E := E)) (modularTransportGenerator hMod)) :
    Commute (spectralPlusProj (E := E)) (modularTransportFlow hMod t) :=
  spectralPlusProj_commutes_modularTransportFlow hMod t h_comm

/-- The Quantum Geometric Tensor (QGT) metric on the chosen slice is realized by
the centered modular variance. -/
def QGTRealizesModularVariance
    (Q : GeometricQuantumTensor E) (ψ : H₂) (hMod : EndH) : Prop :=
  Q.metric ψ ψ = modularVariance (E := E) ψ hMod

/--
**QGT Variance Bridge**:
The information metric components are identical to the modular Hamiltonian
variance when the state is unit-normalized in the Krein metric.
-/
theorem qgt_metric_eq_secondMoment_minus_square
    (Q : GeometricQuantumTensor E) (ψ : H₂) (hMod : EndH)
    (hQ : QGTRealizesModularVariance (E := E) Q ψ hMod)
    (hψ : kreinExpectation (E := E) ψ (1 : EndH) = 1) :
    Q.metric ψ ψ
      = kreinExpectation (E := E) ψ (hMod * hMod)
        - (kreinExpectation (E := E) ψ hMod)^2 := by
  rw [hQ, modularVariance_of_normalized (E := E) ψ hMod hψ]

/--
The only phase coordinate carried by an operatorial QGT seed on the local
Cartan branch is the exponential parameter of `KRotation = exp(tK)`.
-/
theorem qgtOfOperator_KRotation_metric_and_berry_invariant
    (A : EndH)
    (hA : IsSelfAdjoint A)
    (hComm :
      A.comp (modularComplexI (E := E))
        =
      (modularComplexI (E := E)).comp A)
    (t : ℝ) :
    let Q := GeometricQuantumTensor.qgtOfOperator (E := E) A hA hComm
    (∀ u v : H₂,
      Q.metric (KRotation (E := E) t u) (KRotation (E := E) t v) = Q.metric u v)
      ∧
    (∀ u v : H₂,
      Q.berry (KRotation (E := E) t u) (KRotation (E := E) t v) = Q.berry u v) := by
  simpa using
    GeometricQuantumTensor.qgtOfOperator_KRotation_invariant
      (E := E) (A := A) hA hComm t

/--
The Krein-side operatorial QGT is invariant under the same exact local phase
coordinate `t` on the Cartan-odd / phase-antilinear branch.
-/
theorem kreinQgtOfOperator_KRotation_metric_and_berry_invariant
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A)
    (t : ℝ) :
    let Q := GeometricQuantumTensor.kreinQgtOfOperator (E := E) A hA hAnti
    (∀ u v : H₂,
      Q.metric (KRotation (E := E) t u) (KRotation (E := E) t v) = Q.metric u v)
      ∧
    (∀ u v : H₂,
      Q.berry (KRotation (E := E) t u) (KRotation (E := E) t v) = Q.berry u v) := by
  simpa using
    GeometricQuantumTensor.kreinQgtOfOperator_KRotation_invariant
      (E := E) (A := A) hA hAnti t

/--
If the modular transport seed is phase-linear/self-adjoint and the operatorial
seed commutes with the true Cartan generator `hMod ∘ K`, the full operatorial
QGT is preserved along the corresponding exact modular transport flow.
-/
theorem qgtOfOperator_modularTransportFlow_metric_and_berry_invariant_of_commute_generator
    (A hMod : EndH)
    (hA : IsSelfAdjoint A)
    (hACommK :
      A.comp (modularComplexI (E := E))
        =
      (modularComplexI (E := E)).comp A)
    (hSelf : IsSelfAdjoint hMod)
    (hPhase : IsPhaseLinear (E := E) hMod)
    (hCommGen : Commute A (modularTransportGenerator (E := E) hMod))
    (t : ℝ) :
    let Q := GeometricQuantumTensor.qgtOfOperator (E := E) A hA hACommK
    (∀ u v : H₂,
      Q.metric (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.metric u v)
      ∧
    (∀ u v : H₂,
      Q.berry (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.berry u v) := by
  simpa using
    GeometricQuantumTensor.qgtOfOperator_modularTransportFlow_invariant_of_commute_generator
      (E := E) (A := A) (hMod := hMod) hA hACommK hSelf hPhase hCommGen t

/--
If the modular transport generator is exactly a local Cartan phase-axis
generator, the Hilbert-side operatorial QGT is preserved along the exact
modular transport flow.
-/
theorem qgtOfOperator_modularTransportFlow_metric_and_berry_invariant_of_generator_eq_smul_phaseAxis
    (A hMod : EndH)
    (hA : IsSelfAdjoint A)
    (hComm :
      A.comp (modularComplexI (E := E))
        =
      (modularComplexI (E := E)).comp A)
    (σ t : ℝ)
    (hGen :
      modularTransportGenerator (E := E) hMod
        =
      σ • modularComplexI (E := E)) :
    let Q := GeometricQuantumTensor.qgtOfOperator (E := E) A hA hComm
    (∀ u v : H₂,
      Q.metric (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.metric u v)
      ∧
    (∀ u v : H₂,
      Q.berry (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.berry u v) := by
  simpa using
    GeometricQuantumTensor.qgtOfOperator_modularTransportFlow_invariant_of_generator_eq_smul_phaseAxis
      (E := E) (A := A) (hMod := hMod) hA hComm σ t hGen

/--
If the modular transport generator is exactly a local Cartan phase-axis
generator, the Krein-side operatorial QGT is preserved along the exact modular
transport flow.
-/
theorem kreinQgtOfOperator_modularTransportFlow_metric_and_berry_invariant_of_generator_eq_smul_phaseAxis
    (A hMod : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A)
    (σ t : ℝ)
    (hGen :
      modularTransportGenerator (E := E) hMod
        =
      σ • modularComplexI (E := E)) :
    let Q := GeometricQuantumTensor.kreinQgtOfOperator (E := E) A hA hAnti
    (∀ u v : H₂,
      Q.metric (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.metric u v)
      ∧
    (∀ u v : H₂,
      Q.berry (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.berry u v) := by
  simpa using
    GeometricQuantumTensor.kreinQgtOfOperator_modularTransportFlow_invariant_of_generator_eq_smul_phaseAxis
      (E := E) (A := A) (hMod := hMod) hA hAnti σ t hGen

end InfoGeometry.Quantum.Test
