import InfoGeometry.Canonical.ThermodynamicGenerator
import InfoGeometry.Canonical.SuperJordanLie
import InfoGeometry.Canonical.VortexAnomalyLink
import InfoGeometry.Canonical.SuperUnified

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SouriauFlowCliffordBridge

Thin bridge collecting the operatorial Souriau-temperature lane with existing
Clifford/Jordan/Lie and source/sink transport owners.
-/

namespace SouriauFlowCliffordBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.ThermodynamicGenerator
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.SuperJordanLie
open InfoGeometry.Canonical.VortexAnomalyLink

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
On the Souriau-temperature lane, the even-even super-bracket is exactly twice
the Lie component of the operator product.
-/
@[rep_depth transport]
theorem souriau_fockCommutator_eq_two_smul_lieProduct
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH) :
    fockCommutator (E := E) (souriauTemperatureVector (E := E) P ψ) A
      =
    (2 : ℝ) • lieProduct (E := E) (souriauTemperatureVector (E := E) P ψ) A := by
  simpa using
    (InfoGeometry.Canonical.SuperJordanLie.fockCommutator_eq_two_smul_lieProduct
      (E := E) (A := souriauTemperatureVector (E := E) P ψ) (B := A))

/--
On the Souriau-temperature lane, the odd-odd super-bracket is exactly twice
the Jordan component of the operator product.
-/
@[rep_depth transport]
theorem souriau_fockAnticommutator_eq_two_smul_jordanProduct
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH) :
    fockAnticommutator (E := E) (souriauTemperatureVector (E := E) P ψ) A
      =
    (2 : ℝ) • jordanProduct (E := E) (souriauTemperatureVector (E := E) P ψ) A := by
  simpa using
    (InfoGeometry.Canonical.SuperJordanLie.fockAnticommutator_eq_two_smul_jordanProduct
      (E := E) (A := souriauTemperatureVector (E := E) P ψ) (B := A))

/--
Specialized Clifford/Jordan/Lie split for the Souriau generator:
`GA = J(G,A) + L(G,A)`.
-/
@[rep_depth transport]
theorem souriau_comp_eq_jordan_plus_lie
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH) :
    (souriauTemperatureVector (E := E) P ψ).comp A
      =
    jordanProduct (E := E) (souriauTemperatureVector (E := E) P ψ) A
      +
    lieProduct (E := E) (souriauTemperatureVector (E := E) P ψ) A := by
  simpa [InfoGeometry.SuperUnified.jordanProduct, InfoGeometry.SuperUnified.lieBracket,
      InfoGeometry.Canonical.SuperJordanLie.jordanProduct,
      InfoGeometry.Canonical.SuperJordanLie.lieProduct] using
    (InfoGeometry.SuperUnified.clifford_decomposition
      (E := E)
      (A := souriauTemperatureVector (E := E) P ψ)
      (B := A))

/--
Infinitesimal thermodynamic conjugation at `β = 0` on the Souriau lane:
the derivative of the Gibbs partition readout is minus the Souriau expectation.
-/
@[rep_depth transport, capstone]
theorem deriv_apply_operatorialGibbsWeight_zero_eq_neg_expectation_souriau
    (ω : EndH →L[ℝ] ℝ)
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) :
    deriv (fun β : ℝ => ω (operatorialGibbsWeight (E := E) P ψ β)) 0
      =
    -ω (souriauTemperatureVector (E := E) P ψ) := by
  simpa using
    (deriv_apply_operatorialGibbsWeight_zero
      (E := E) (ω := ω) (P := P) (ψ := ψ))

/--
Hestenes-phase readout on the Souriau lane:
for the modular datum carried by `P`, the phase bilinear form is exactly the
metric bilinear form composed with `complex_i = Jε`.
-/
@[rep_depth transport]
theorem souriau_stateQGTPhaseReadout_eq_metric_comp_complex_i
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH) :
    InfoGeometry.Canonical.StateDependentTransport.stateQGTPhaseReadout
        (E := E) P.modularData ψ A
      =
    (InfoGeometry.Canonical.StateDependentTransport.stateQGTMetricReadout
        (E := E) P.modularData ψ A).compLeft
      (InfoGeometry.Krein.complex_i (E := E)).toLinearMap := by
  exact
    (InfoGeometry.Canonical.StateDependentTransport.stateQGTPhaseReadout_eq_metric_comp_complex_i
      (E := E) (M := P.modularData) (ψ := ψ) (A := A))

/--
If the transport connection is identified with the Souriau-temperature vector,
the source-minus-sink defect split is exactly the grading-axis commutator.
-/
@[rep_depth transport]
theorem sourceSink_souriau_defect_split_of_connection_eq
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hConn : V.connectionGenerator = souriauTemperatureVector (E := E) P ψ) :
    sourceVortexSeed (E := E) V - sinkVortexSeed (E := E) V
      =
    transportCommutator (E := E)
      (souriauTemperatureVector (E := E) P ψ) (spectral_epsilon (E := E)) := by
  simpa [hConn] using
    (sourceVortexSeed_sub_sinkVortexSeed_eq_transportCommutator_spectral_epsilon
      (E := E) (V := V))

end Core

end SouriauFlowCliffordBridge
