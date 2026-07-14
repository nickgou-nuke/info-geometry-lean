import InfoGeometry.Cocycle.LogarithmicOrderParameter

/-!
# Virasoro Ward Equilibrium for Logarithmic GW Potentials

This module is an abstract interface, not a construction of Gromov--Witten
theory.

The already-owned `InfoGeometry.Cocycle.LogarithmicOrderParameter` file proves
the `H¹` layer:

* positive multiplicative weights;
* logarithmic free energy `F = -log Z`;
* Weyl/log-density normalization.

This file adds the next layer as a Ward-equilibrium interface:

* a Virasoro-style operator family `L n`;
* constraints `L n Z = 0` for `n ≥ -1`;
* an explicitly supplied logarithmic transform law converting the linear
  partition constraint into a free-energy balance equation.

The analytic formula for a genuine GW partition function, descendant
insertions, KdV hierarchy, or Virasoro differential operators is deliberately
not asserted here.  Those belong in later geometry/GW owner modules.
-/

noncomputable section

namespace VirasoroWardEquilibrium

open InfoGeometry.Cocycle

/-! ## Abstract Virasoro constraint data -/

/--
Abstract Virasoro Ward datum.

`Op` is the operator algebra carrier for the Virasoro generators, `Partition`
is the carrier where the partition function lives, and `Value` is the scalar or
operator-valued readout of applying a Ward operator.
-/
structure VirasoroConstraintDatum
    (Partition Op Value : Type*) [AddCommGroup Op] [AddCommGroup Value] where
  /-- The formal partition function or partition-vector object. -/
  Z : Partition
  /-- Virasoro generator family `L_n`. -/
  L : ℤ → Op
  /-- Bracket on the operator carrier. -/
  bracket : Op → Op → Op
  /-- Central/anomalous term in the Virasoro bracket. -/
  centralTerm : ℤ → ℤ → Op
  /-- Action/readout of an operator on the partition object. -/
  apply : Op → Partition → Value
  /-- Abstract Virasoro bracket law. -/
  virasoroLaw :
    ∀ m n : ℤ,
      bracket (L m) (L n) = (m - n) • L (m + n) + centralTerm m n
  /-- Ward constraint `L_n Z = 0` for `n ≥ -1`. -/
  constraint :
    ∀ n : ℤ, (-1 : ℤ) ≤ n → apply (L n) Z = 0

namespace VirasoroConstraintDatum

variable {Partition Op Value : Type*} [AddCommGroup Op] [AddCommGroup Value]

/-- Readback of the Virasoro bracket law. -/
theorem virasoro_bracket
    (D : VirasoroConstraintDatum Partition Op Value) (m n : ℤ) :
    D.bracket (D.L m) (D.L n) = (m - n) • D.L (m + n) + D.centralTerm m n :=
  D.virasoroLaw m n

/-- Readback of the Ward constraint. -/
theorem ward_constraint
    (D : VirasoroConstraintDatum Partition Op Value)
    (n : ℤ) (hn : (-1 : ℤ) ≤ n) :
    D.apply (D.L n) D.Z = 0 :=
  D.constraint n hn

end VirasoroConstraintDatum

/-! ## Free-energy Ward balance -/

/--
Free-energy form of a Ward equation after the logarithmic transformation
`Z ↦ F = -log Z`.

The field `logTransformLaw` is the intentionally explicit interface for the
analytic step

```text
L_n Z = 0  ⟹  V_n(F) + Q_n(∇F) + A_n = 0.
```

This module proves the algebraic consequence of that interface; it does not
construct the differential operators.
-/
structure FreeEnergyWardBalance (Value : Type*) [AddCommGroup Value] where
  /-- Linear partition-side Ward variation, e.g. `L_n Z` after readout. -/
  partitionVariation : ℤ → Value
  /-- Linear free-energy variation term. -/
  linearVariation : ℤ → Value
  /-- Quadratic/backreaction term produced by `Z = exp(-F)`. -/
  quadraticBackreaction : ℤ → Value
  /-- Central/anomalous Ward term. -/
  anomalyTerm : ℤ → Value
  /-- Logarithmic transform law from partition variation to free-energy balance. -/
  logTransformLaw :
    ∀ n : ℤ,
      partitionVariation n =
        linearVariation n + quadraticBackreaction n + anomalyTerm n
  /-- Virasoro Ward constraint on the partition-side variation. -/
  wardConstraint :
    ∀ n : ℤ, (-1 : ℤ) ≤ n → partitionVariation n = 0

namespace FreeEnergyWardBalance

variable {Value : Type*} [AddCommGroup Value]

/--
Virasoro Ward equilibrium in free-energy form:
linear variation plus quadratic backreaction plus anomaly vanishes.
-/
theorem forceBalance_eq_zero
    (B : FreeEnergyWardBalance Value) (n : ℤ) (hn : (-1 : ℤ) ≤ n) :
    B.linearVariation n + B.quadraticBackreaction n + B.anomalyTerm n = 0 := by
  rw [← B.logTransformLaw n]
  exact B.wardConstraint n hn

/-- Equivalent sign convention: the anomaly balances the noncentral variation. -/
theorem anomalyTerm_eq_neg_linear_plus_quadratic
    (B : FreeEnergyWardBalance Value) (n : ℤ) (hn : (-1 : ℤ) ≤ n) :
    B.anomalyTerm n = -(B.linearVariation n + B.quadraticBackreaction n) := by
  have h := B.forceBalance_eq_zero n hn
  rw [eq_neg_iff_add_eq_zero]
  simpa [add_assoc, add_comm, add_left_comm] using h

end FreeEnergyWardBalance

/-! ## GW partition-weight bridge -/

/--
GW/Virasoro Ward equilibrium packet.

The field `gwWeight` is only the positive multiplicative partition-weight
interface from `LogarithmicOrderParameter`; it is not a construction of
Gromov--Witten invariants.  `freeEnergy_eq` records the convention
`F = -log Z` at a selected parameter.
-/
structure GWVirasoroWardEquilibrium
    (G Partition Op Value : Type*) [Group G] [AddCommGroup Op] [AddCommGroup Value] where
  /-- Positive multiplicative GW-like partition weight. -/
  gwWeight : GWPartitionWeight G
  /-- Parameter where the scalar free energy is read. -/
  parameter : G
  /-- Scalar free-energy readout. -/
  freeEnergy : ℝ
  /-- Convention `F = -log Z` for the supplied GW partition weight. -/
  freeEnergy_eq : freeEnergy = GWPartitionWeight.gwFreeEnergy gwWeight parameter
  /-- Virasoro Ward constraint datum on the partition side. -/
  ward : VirasoroConstraintDatum Partition Op Value
  /-- Free-energy balance datum after logarithmic transformation. -/
  balance : FreeEnergyWardBalance Value

namespace GWVirasoroWardEquilibrium

variable {G Partition Op Value : Type*} [Group G] [AddCommGroup Op] [AddCommGroup Value]

/-- The GW free energy is the negative logarithm of the positive partition weight. -/
theorem freeEnergy_eq_negative_log_weight
    (E : GWVirasoroWardEquilibrium G Partition Op Value) :
    E.freeEnergy = -Real.log (E.gwWeight.c E.parameter) := by
  rw [E.freeEnergy_eq]
  rfl

/-- Virasoro constraint readback from the partition-side datum. -/
theorem ward_constraint
    (E : GWVirasoroWardEquilibrium G Partition Op Value)
    (n : ℤ) (hn : (-1 : ℤ) ≤ n) :
    E.ward.apply (E.ward.L n) E.ward.Z = 0 :=
  E.ward.ward_constraint n hn

/--
Main abstract theorem: Virasoro constraints become free-energy Ward
equilibrium once the logarithmic transform law is supplied.
-/
theorem virasoro_constraint_as_freeEnergy_balance
    (E : GWVirasoroWardEquilibrium G Partition Op Value)
    (n : ℤ) (hn : (-1 : ℤ) ≤ n) :
    E.balance.linearVariation n +
        E.balance.quadraticBackreaction n +
        E.balance.anomalyTerm n =
      0 :=
  E.balance.forceBalance_eq_zero n hn

end GWVirasoroWardEquilibrium

end VirasoroWardEquilibrium
