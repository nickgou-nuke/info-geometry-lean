/-
InfoGeometry/OperatorAlgebra/AffineVirasoroExceptionalBridge.lean

Bridge between exceptional E8-type ledgers and affine/Virasoro boundary
accounting.

The finite exceptional ledger records hidden charge/memory. The affine
extension records loop/helical modes. The Virasoro extension records
reparametrization stress-energy and central charge.

This file supplies a concrete linear bridge.  It does not assert that an
exceptional finite algebra is isomorphic to a Virasoro algebra.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
import InfoGeometry.OperatorAlgebra.SuperVirasoroExtension
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge

open FiveGradedInformationLedger
open SuperVirasoroExtension

/-! ## 1. Exceptional/affine/Virasoro bridge -/

/--
Linear bridge between a finite ledger, its affine/current extension, and a
Virasoro boundary ledger.

The intended architecture is:

```text
finite E8-type ledger
  -> loop/current extension
  -> affine central extension
  -> Sugawara/Virasoro stress tensor
  -> central charge readout
```

The maps are data.  Any injectivity, surjectivity, Lie compatibility, Sugawara
identity, or representation-theoretic equivalence must be proved separately
for a concrete model.
-/
structure ExceptionalAffineVirasoroBridge
    (Finite Affine Vir State Charge : Type*)
    [AddCommGroup Finite] [Module ℝ Finite]
    [AddCommGroup Affine] [Module ℝ Affine]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Charge] [Module ℝ Charge] where
  /-- Map from finite exceptional data to affine/current modes. -/
  finiteToAffine : Finite →ₗ[ℝ] Affine

  /-- Linear realization of affine/current modes in the Virasoro carrier. -/
  affineToVirasoro : Affine →ₗ[ℝ] Vir

  /-- Virasoro datum used for the stress-energy/central-charge ledger. -/
  virasoro : VirasoroAlgebraDatum Vir

  /-- Select the finite-ledger datum carried by a boundary state. -/
  stateToFiniteLedger : State → Finite

  /-- Read hidden finite-grade memory as a charge. -/
  finiteHiddenMemoryReadout : Finite →ₗ[ℝ] Charge

namespace ExceptionalAffineVirasoroBridge

variable
    {Finite Affine Vir State Charge : Type*}
    [AddCommGroup Finite] [Module ℝ Finite]
    [AddCommGroup Affine] [Module ℝ Affine]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Charge] [Module ℝ Charge]

variable (B : ExceptionalAffineVirasoroBridge Finite Affine Vir State Charge)

/-- The actual finite-to-Virasoro map supplied by the two bridge stages. -/
def finiteToVirasoro : Finite →ₗ[ℝ] Vir :=
  B.affineToVirasoro.comp B.finiteToAffine

@[simp]
theorem finiteToVirasoro_apply (x : Finite) :
    B.finiteToVirasoro x =
      B.affineToVirasoro (B.finiteToAffine x) :=
  rfl

/--
Canonical boundary charge induced by the finite exceptional ledger.

This preserves the historical readout API without postulating an independent
map and an equality field.  Identifying this charge with a concrete Sugawara
central charge remains a separate representation-theoretic theorem.
-/
def centralChargeReadout : State → Charge :=
  fun s => B.finiteHiddenMemoryReadout (B.stateToFiniteLedger s)

/-- Hidden grade-memory readout transported from the finite ledger. -/
def hiddenGradeMemoryReadout : State → Charge :=
  fun s => B.finiteHiddenMemoryReadout (B.stateToFiniteLedger s)

/-- Compatibility name for the canonical finite-ledger hidden-memory readout. -/
abbrev calibratedHiddenGradeMemoryReadout : State → Charge :=
  B.hiddenGradeMemoryReadout

/-- The two historical readout names unfold to the same canonical map. -/
theorem centralCharge_eq_hiddenGradeMemory
    (s : State) :
    B.centralChargeReadout s = B.calibratedHiddenGradeMemoryReadout s :=
  rfl

/-- The Virasoro central generator commutes inside the Virasoro ledger. -/
theorem virasoro_central_commutes
    (X : Vir) :
    ⁅B.virasoro.centralCharge, X⁆ = 0 :=
  B.virasoro.central_commutes X

end ExceptionalAffineVirasoroBridge

/-! ## 2. Bridge readout -/

/--
Affine/Virasoro exceptional bridge readout.

This captures the precise compatibility:

```text
the historical boundary-charge and hidden-memory names denote the same
finite-ledger projection.  It does not assert an exceptional Sugawara theorem.
```
-/
theorem exceptionalAffineVirasoroBridgeOwnerTarget :
  ∀ (Finite Affine Vir State Charge : Type*)
    [AddCommGroup Finite] [Module ℝ Finite]
    [AddCommGroup Affine] [Module ℝ Affine]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
      [AddCommGroup Charge] [Module ℝ Charge],
  ∀ B : ExceptionalAffineVirasoroBridge Finite Affine Vir State Charge,
  ∀ s : State,
    B.centralChargeReadout s = B.calibratedHiddenGradeMemoryReadout s := by
  intro Finite Affine Vir State Charge _ _ _ _ _ _ _ _ _ _ _ _ B s
  exact B.centralCharge_eq_hiddenGradeMemory s

/-- Packet readout for one exceptional affine/Virasoro bridge. -/
theorem exceptionalAffineVirasoroBridge_packet
    (Finite Affine Vir State Charge : Type*)
    [AddCommGroup Finite] [Module ℝ Finite]
    [AddCommGroup Affine] [Module ℝ Affine]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Charge] [Module ℝ Charge]
    (B : ExceptionalAffineVirasoroBridge Finite Affine Vir State Charge)
    (s : State) :
    B.centralChargeReadout s = B.calibratedHiddenGradeMemoryReadout s :=
  exceptionalAffineVirasoroBridgeOwnerTarget Finite Affine Vir State Charge B s

end InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge
