/- SPDX-License-Identifier: Apache-2.0 -/

/-
# Finite Gibbs to relational operatorial Hessian transport

This module is an explicit carrier adapter.  The operatorial Hessian owner and
the finite Gibbs/BKM owner use different carriers, so no theorem identifies
them without transport data.  The adapter records that data and exposes only
the resulting transport theorem.

No identification is inferred from notation, and no conjugation-orbit Hessian
is renamed as a Gibbs log-partition Hessian.
-/

import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.FiniteGibbsOperatorialHessianTransport

open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge
open InfoGeometry.Canonical.RelationalInformationDynamics

abbrev FiniteOperator (n : ℕ) := FiniteOperatorAlgebra n
abbrev RelationalOperator (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/-- Explicit transport data from a finite Gibbs operator algebra to the
relational operator carrier. -/
structure TransportData
    (n : ℕ)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  map : FiniteOperator n →ₗ[ℝ] RelationalOperator E
  readout : RelationalOperator E →L[ℝ] ℝ
  /-- The readout compatibility required to compare the two Hessian owners. -/
  hessian_readout :
    ∀ (H : FiniteOperator n) (hH : IsSelfAdjoint H)
      (hZ : 0 < gibbsPartitionReal H)
      (A B : FiniteOperator n),
      readout
          (operatorInformationHessian
            (E := E) (map H) (map A)) =
        centeredFrechetResponse H hH hZ A B

/-- The transported operatorial Hessian readout supplied by TransportData. -/
def transportedHessianReadout
    {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (D : TransportData n E)
    (H A B : FiniteOperator n) : ℝ :=
  D.readout
    (operatorInformationHessian (E := E) (D.map H) (D.map A))

/-- The transported readout uses the existing double transport
commutator owner for the relational operatorial Hessian. -/
theorem transportedHessianReadout_eq_double_transportCommutator
    {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (D : TransportData n E)
    (H A B : FiniteOperator n) :
    transportedHessianReadout D H A B =
      D.readout
        (transportCommutator (D.map H) (D.map A)) := by
  unfold transportedHessianReadout
  rw [operatorInformationHessian_eq_double_transportCommutator]

/-- The adapter exposes the finite Gibbs centered response exactly when the
explicit compatibility field is available. -/
theorem transportedHessianReadout_eq_centeredFrechetResponse
    {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (D : TransportData n E)
    (H : FiniteOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : FiniteOperator n) :
    transportedHessianReadout D H A B =
      centeredFrechetResponse H hH hZ A B :=
  D.hessian_readout H hH hZ A B

/-- The complete finite-stage bridge: after explicit carrier transport, the
relational Hessian readout is the native centered BKM covariance.  The
self-adjointness premise is exactly the premise required by the existing
centered-response theorem; no Hessian identity is inferred for arbitrary
observables. -/
theorem transportedHessianReadout_eq_centeredBKMRealCovariance
    {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (D : TransportData n E)
    (H : FiniteOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : FiniteOperator n) (hA : IsSelfAdjoint A) :
    transportedHessianReadout D H A B =
      centeredBKMRealCovariance
        (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        A B := by
  calc
    transportedHessianReadout D H A B =
        centeredFrechetResponse H hH hZ A B :=
      transportedHessianReadout_eq_centeredFrechetResponse
        D H hH hZ A B
    _ = centeredBKMRealCovariance
        (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        A B :=
      centeredFrechetResponse_eq_centeredBKMRealCovariance
        H hH hZ A B hA

end InfoGeometry.Canonical.FiniteGibbsOperatorialHessianTransport
