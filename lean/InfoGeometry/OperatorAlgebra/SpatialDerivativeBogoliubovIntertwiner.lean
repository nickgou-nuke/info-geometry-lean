import InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift
import InfoGeometry.Canonical.RealTomitaCore

open scoped InnerProductSpace

/-!
# Spatial Derivative–Bogoliubov Intertwiner

Typed bridge from the noncommutative Connes spatial-derivative owner to the
real doubled Tomita/Bogoliubov transport lane.

The analytic input is explicit: a realization of the spatial-derivative
carrier as bounded doubled operators, together with the property

`exp (-K φ ψ) = realize (dφ/dψ)`.

Everything else in this file is derived from that property and the existing
operator-valued Tomita transport laws.  No diagonalization, determinant, or
scalar entropy readout is used.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SpatialDerivativeBogoliubovIntertwiner

open InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
open InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealTomitaCore

variable {A Weight Deriv Phase Core : Type*}
  [Ring A] [Mul Core]
  [MulOneClass Deriv]
  [One Phase] [Mul Phase]
variable {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
A typed realization of noncommutative spatial derivatives on the doubled
Bogoliubov carrier.

The relative Hamiltonian in `modularCore` is an actual bounded operator.
The sole analytic compatibility field states that its negative exponential is
the realized spatial derivative.
-/
structure Intertwiner
    (modularCore :
      NoncommutativeModularOperatorLift
        A Weight Deriv EndH Phase Core) where
  /--
  Multiplicative operator realization of the affiliated spatial-derivative
  carrier.

  This retains the Connes chain law after realization; no additive logarithm
  law is assumed.
  -/
  realizeSpatialDerivative : Deriv →* EndH

  /-- Exact negative-log orientation property. -/
  exp_neg_relativeHamiltonian :
    ∀ φ ψ : Weight,
      NormedSpace.exp (-modularCore.relativeHamiltonian φ ψ) =
        realizeSpatialDerivative
          (modularCore.spatialDerivative.spatialDerivative φ ψ)

namespace Intertwiner

variable
  {modularCore :
    NoncommutativeModularOperatorLift
      A Weight Deriv
        (InfoGeometry.Krein.DoubledSpace E →L[ℝ]
          InfoGeometry.Krein.DoubledSpace E)
        Phase Core}
  (I : Intertwiner (E := E) modularCore)

/-- Realized noncommutative spatial derivative for an ordered weight pair. -/
def realizedSpatialDerivative (φ ψ : Weight) : EndH :=
  I.realizeSpatialDerivative
    (modularCore.spatialDerivative.spatialDerivative φ ψ)

/--
The realized spatial derivative is the exponential of the negative relative
Hamiltonian.
-/
theorem realizedSpatialDerivative_eq_exp_neg_relativeHamiltonian
    (φ ψ : Weight) :
    I.realizedSpatialDerivative φ ψ =
      NormedSpace.exp (-modularCore.relativeHamiltonian φ ψ) := by
  exact (I.exp_neg_relativeHamiltonian φ ψ).symm

@[simp]
theorem realizedSpatialDerivative_self
    (φ : Weight) :
    I.realizedSpatialDerivative φ φ = 1 := by
  simp [realizedSpatialDerivative,
    modularCore.spatialDerivative_same_weight]

/--
The Connes spatial-derivative chain rule survives as an operator product on
the doubled Bogoliubov carrier.
-/
theorem realizedSpatialDerivative_chain
    (φ ψ η : Weight) :
    I.realizedSpatialDerivative φ ψ *
        I.realizedSpatialDerivative ψ η =
      I.realizedSpatialDerivative φ η := by
  calc
    I.realizedSpatialDerivative φ ψ *
          I.realizedSpatialDerivative ψ η =
        I.realizeSpatialDerivative
          (modularCore.spatialDerivative.spatialDerivative φ ψ *
            modularCore.spatialDerivative.spatialDerivative ψ η) :=
      (I.realizeSpatialDerivative.map_mul _ _).symm
    _ = I.realizedSpatialDerivative φ η :=
      congrArg I.realizeSpatialDerivative
        (modularCore.spatialDerivative_chain φ ψ η)

@[simp]
theorem exp_neg_relativeHamiltonian_self
    (I : Intertwiner (E := E) modularCore)
    (φ : Weight) :
    NormedSpace.exp (-modularCore.relativeHamiltonian φ φ) = 1 := by
  rw [← realizedSpatialDerivative_eq_exp_neg_relativeHamiltonian
    (I := I) φ φ]
  exact realizedSpatialDerivative_self (I := I) φ

/--
The relative-Hamiltonian realization satisfies the exact multiplicative
cocycle law at exponential level.  No noncommutative logarithm-additivity
claim is used.
-/
theorem exp_neg_relativeHamiltonian_chain
    (I : Intertwiner (E := E) modularCore)
    (φ ψ η : Weight) :
    NormedSpace.exp (-modularCore.relativeHamiltonian φ ψ) *
        NormedSpace.exp (-modularCore.relativeHamiltonian ψ η) =
      NormedSpace.exp (-modularCore.relativeHamiltonian φ η) := by
  rw [← realizedSpatialDerivative_eq_exp_neg_relativeHamiltonian
      (I := I) φ ψ,
    ← realizedSpatialDerivative_eq_exp_neg_relativeHamiltonian
      (I := I) ψ η,
    ← realizedSpatialDerivative_eq_exp_neg_relativeHamiltonian
      (I := I) φ η]
  exact realizedSpatialDerivative_chain (I := I) φ ψ η

/--
The ordered weight pair determines genuine real doubled modular-log data:
`Delta = realize (dφ/dψ)` and `deltaLog = -K(φ,ψ)`.
-/
def toRealModularLogData (φ ψ : Weight) :
    RealModularLogData (E := E) where
  Delta := I.realizedSpatialDerivative φ ψ
  deltaLog := -modularCore.relativeHamiltonian φ ψ
  exp_deltaLog := I.exp_neg_relativeHamiltonian φ ψ

@[simp]
theorem toRealModularLogData_Delta
    (φ ψ : Weight) :
    (I.toRealModularLogData φ ψ).Delta =
      I.realizedSpatialDerivative φ ψ :=
  rfl

@[simp]
theorem toRealModularLogData_deltaLog
    (φ ψ : Weight) :
    (I.toRealModularLogData φ ψ).deltaLog =
      -modularCore.relativeHamiltonian φ ψ :=
  rfl

/--
The Tomita logarithm property retains the intended orientation on the
realized spatial derivative.
-/
theorem exp_toRealModularLogData_deltaLog
    (φ ψ : Weight) :
    NormedSpace.exp ((I.toRealModularLogData φ ψ).deltaLog) =
      I.realizedSpatialDerivative φ ψ :=
  (I.toRealModularLogData φ ψ).exp_deltaLog

/-- Bogoliubov/Tomita transport generated by the ordered relative Hamiltonian. -/
def flow (φ ψ : Weight) (t : ℝ) : EndH :=
  (I.toRealModularLogData φ ψ).flow t

@[simp]
theorem flow_zero
    (φ ψ : Weight) :
    I.flow φ ψ 0 = 1 :=
  (I.toRealModularLogData φ ψ).flow_zero

/-- The realized noncommutative Bogoliubov transport is a one-parameter group. -/
theorem flow_add
    (φ ψ : Weight) (s t : ℝ) :
    I.flow φ ψ (s + t) =
      I.flow φ ψ s * I.flow φ ψ t :=
  (I.toRealModularLogData φ ψ).flow_add s t

/-- Negative time gives a left inverse for the realized transport. -/
theorem flow_neg_mul
    (φ ψ : Weight) (t : ℝ) :
    I.flow φ ψ (-t) * I.flow φ ψ t = 1 :=
  (I.toRealModularLogData φ ψ).flow_neg_mul t

/-- Negative time gives a right inverse for the realized transport. -/
theorem flow_mul_neg
    (φ ψ : Weight) (t : ℝ) :
    I.flow φ ψ t * I.flow φ ψ (-t) = 1 :=
  (I.toRealModularLogData φ ψ).flow_mul_neg t

/--
Changing from `log Delta = -K` to the opposite logarithmic orientation reverses
the Bogoliubov/Tomita time parameter.
-/
theorem flow_relativeHamiltonian_eq_time_reverse
    (φ ψ : Weight) (t : ℝ) :
    InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow
        (E := E) (modularCore.relativeHamiltonian φ ψ) t =
      I.flow φ ψ (-t) := by
  simpa [flow, toRealModularLogData] using
    (I.toRealModularLogData φ ψ).flow_negLog_eq_time_reverse t

end Intertwiner

end InfoGeometry.OperatorAlgebra.SpatialDerivativeBogoliubovIntertwiner
