import InfoGeometry.OperatorAlgebra.SpatialDerivativeBogoliubovIntertwiner
import InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge

open scoped InnerProductSpace

/-!
# Spatial Derivative–Certified Reduction Bridge

Support-restricted realization of the noncommutative spatial derivative and
its relative Hamiltonian on the certified Drazin regular lane.

No diagonalization or scalar determinant is used.  The hypotheses identify the
certified reduction's operator and logarithm hook with the typed
spatial-derivative realization; the conclusions are then derived from the
existing `Preg/Pzero` owner laws.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpatialDerivativeCertifiedReductionBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge
open InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift
open InfoGeometry.OperatorAlgebra.SpatialDerivativeBogoliubovIntertwiner

variable {A Weight Deriv Phase Core : Type*}
  [Ring A] [Mul Core]
  [MulOneClass Deriv]
  [One Phase] [Mul Phase]
variable {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

variable
  {modularCore :
    InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.NoncommutativeModularOperatorLift
      A Weight Deriv
        (DoubledSpace E →L[ℝ] DoubledSpace E)
        Phase Core}

/--
The certified regular modular operator is the `Preg` compression of the
realized noncommutative spatial derivative.
-/
theorem deltaReg_eq_compress_realizedSpatialDerivative
    (I : InfoGeometry.OperatorAlgebra.SpatialDerivativeBogoliubovIntertwiner.Intertwiner
      (E := E) modularCore)
    (c : CertifiedModularReduction (E := H₂))
    (φ ψ : Weight)
    (hDelta :
      c.Δ = I.realizedSpatialDerivative φ ψ) :
    c.Δreg =
      compress c.Preg (I.realizedSpatialDerivative φ ψ) := by
  exact
    Delta_reg_eq_compress_Preg_canonicalDelta
      (V := E) c (I.realizedSpatialDerivative φ ψ) hDelta

/--
When the certified logarithm hook is the logarithm orientation
`deltaLog = -K(φ,ψ)`, its ambient negative-log generator is the `Preg`
compression of the relative Hamiltonian itself.
-/
theorem Kambient_eq_compress_relativeHamiltonian
    (c : CertifiedModularReduction (E := H₂))
    (φ ψ : Weight)
    (hLog :
      c.logOn c.logDomain =
        -modularCore.relativeHamiltonian φ ψ) :
    c.Kambient =
      compress c.Preg (modularCore.relativeHamiltonian φ ψ) := by
  have h :=
    Kambient_eq_compress_Preg_neg_canonicalDeltaLog
      (V := E) c (-modularCore.relativeHamiltonian φ ψ) hLog
  simpa using h

/--
Complete noncommutative regular-support packet for an ordered weight pair:

* `Δreg` is the regular compression of the realized spatial derivative;
* `Kambient` is the regular compression of the relative Hamiltonian;
* `Preg` supports `Kambient` on both sides;
* `Pzero` annihilates `Kambient` on both sides.
-/
theorem spatialDerivative_certifiedReduction_packet
    (I : InfoGeometry.OperatorAlgebra.SpatialDerivativeBogoliubovIntertwiner.Intertwiner
      (E := E) modularCore)
    (c : CertifiedModularReduction (E := H₂))
    (φ ψ : Weight)
    (hDelta :
      c.Δ = I.realizedSpatialDerivative φ ψ)
    (hLog :
      c.logOn c.logDomain =
        -modularCore.relativeHamiltonian φ ψ) :
    c.Δreg =
        compress c.Preg (I.realizedSpatialDerivative φ ψ)
      ∧ c.Kambient =
        compress c.Preg (modularCore.relativeHamiltonian φ ψ)
      ∧ c.Preg * c.Kambient = c.Kambient
      ∧ c.Kambient * c.Preg = c.Kambient
      ∧ c.Pzero * c.Kambient = 0
      ∧ c.Kambient * c.Pzero = 0 := by
  have hDeltaReg :=
    deltaReg_eq_compress_realizedSpatialDerivative
      (I := I) (c := c) φ ψ hDelta
  have hK :=
    Kambient_eq_compress_relativeHamiltonian
      (c := c) φ ψ hLog
  have hSupport := c.Kambient_supported_on_Preg
  have hDefect := c.Kambient_kills_Pzero
  exact
    ⟨hDeltaReg, hK, hSupport.1, hSupport.2, hDefect.1, hDefect.2⟩

end InfoGeometry.Canonical.SpatialDerivativeCertifiedReductionBridge
