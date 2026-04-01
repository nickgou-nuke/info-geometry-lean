import InfoGeometry.Quantum.GeometricTensor
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

end InfoGeometry.Quantum.Test
