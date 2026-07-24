import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.SuperchargeCentralChargeClosure
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.KKTNoetherCharges

Noether-charge owner for the repo-native supercharge split lane.

Core law:
from `Q² = H + Z`, `[Q, C] = 0`, and `[Z, C] = 0`, deduce `[H, C] = 0`.

This file exports:
- a generic doubled-operator theorem,
- a projected Drazin specialization,
- and a CPT/root central-split specialization.
-/

namespace InfoGeometry.Canonical.KKTNoetherCharges

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.SuperchargeCentralChargeClosure
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein

section Generic

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

omit [CompleteSpace H] in
/-- Bridge between commutator vanishing and commutation. -/
@[rep_depth krein]
theorem drazinCommutator_eq_zero_iff_commute
    (A B : EndH) :
    DrazinSupercharge.commutatorK A B = 0 ↔ Commute A B := by
  unfold DrazinSupercharge.commutatorK DrazinSupercharge.commutator
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h.eq

omit [CompleteSpace H] in
/--
Noether law on the operatorial split lane:
if `Q² = H + Z` and `C` commutes with `Q` and `Z`, then `C` commutes with `H`.
-/
@[rep_depth krein]
theorem noether_charge_of_supercharge_split
    (Q Hk Z C : EndH)
    (hSplit : Q * Q = Hk + Z)
    (hQC : Commute Q C)
    (hZC : Commute Z C) :
    Commute Hk C := by
  have hQ2C : (Q * Q) * C = C * (Q * Q) := by
    calc
      (Q * Q) * C = Q * (Q * C) := by simp [mul_assoc]
      _ = Q * (C * Q) := by rw [hQC.eq]
      _ = (Q * C) * Q := by simp [mul_assoc]
      _ = (C * Q) * Q := by rw [hQC.eq]
      _ = C * (Q * Q) := by simp [mul_assoc]
  have hSum : (Hk + Z) * C = C * (Hk + Z) := by
    simpa [hSplit] using hQ2C
  have hHCZ : Hk * C + Z * C = C * Hk + C * Z := by
    simpa [mul_add, add_mul, add_assoc] using hSum
  have hHC : Hk * C = C * Hk := by
    have hSub : Hk * C + Z * C - Z * C = C * Hk + C * Z - Z * C := by
      exact congrArg (fun T : EndH => T - Z * C) hHCZ
    rw [hZC.eq] at hSub
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  exact hHC

omit [CompleteSpace H] in
/--
Commutator form of `noether_charge_of_supercharge_split`.
-/
@[rep_depth krein]
theorem noether_commutator_of_supercharge_split
    (Q Hk Z C : EndH)
    (hSplit : Q * Q = Hk + Z)
    (hQC : DrazinSupercharge.commutatorK Q C = 0)
    (hZC : DrazinSupercharge.commutatorK Z C = 0) :
    DrazinSupercharge.commutatorK Hk C = 0 := by
  have hQC' : Commute Q C :=
    (drazinCommutator_eq_zero_iff_commute (A := Q) (B := C)).1 hQC
  have hZC' : Commute Z C :=
    (drazinCommutator_eq_zero_iff_commute (A := Z) (B := C)).1 hZC
  have hHC : Commute Hk C :=
    noether_charge_of_supercharge_split (Q := Q) (Hk := Hk) (Z := Z) (C := C) hSplit hQC' hZC'
  exact (drazinCommutator_eq_zero_iff_commute (A := Hk) (B := C)).2 hHC

end Generic

section DrazinLane

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Projected Drazin specialization of the Noether split law.
-/
@[rep_depth krein]
theorem drazin_noether_charge_of_superHamiltonian_split
    (CIK : CertifiedInverseKernel E)
    {Hk Z C : EndH}
    (hSplit : DrazinSupercharge.CertifiedInverseKernel.superHamiltonian CIK = Hk + Z)
    (hQC : Commute (DrazinSupercharge.CertifiedInverseKernel.supercharge CIK) C)
    (hZC : Commute Z C) :
    Commute Hk C := by
  have hSplitQ :
      (DrazinSupercharge.CertifiedInverseKernel.supercharge CIK)
          * (DrazinSupercharge.CertifiedInverseKernel.supercharge CIK)
        =
      Hk + Z := by
    simpa [DrazinSupercharge.CertifiedInverseKernel.superHamiltonian] using hSplit
  exact
    noether_charge_of_supercharge_split
      (Q := DrazinSupercharge.CertifiedInverseKernel.supercharge CIK)
      (Hk := Hk) (Z := Z) (C := C) hSplitQ hQC hZC

/--
Commutator form of the projected Drazin Noether split law.
-/
@[rep_depth krein]
theorem drazin_noether_commutator_of_superHamiltonian_split
    (CIK : CertifiedInverseKernel E)
    {Hk Z C : EndH}
    (hSplit : DrazinSupercharge.CertifiedInverseKernel.superHamiltonian CIK = Hk + Z)
    (hQC :
      DrazinSupercharge.commutatorK
        (DrazinSupercharge.CertifiedInverseKernel.supercharge CIK) C = 0)
    (hZC : DrazinSupercharge.commutatorK Z C = 0) :
    DrazinSupercharge.commutatorK Hk C = 0 := by
  have hSplitQ :
      (DrazinSupercharge.CertifiedInverseKernel.supercharge CIK)
          * (DrazinSupercharge.CertifiedInverseKernel.supercharge CIK)
        =
      Hk + Z := by
    simpa [DrazinSupercharge.CertifiedInverseKernel.superHamiltonian] using hSplit
  exact
    noether_commutator_of_supercharge_split
      (Q := DrazinSupercharge.CertifiedInverseKernel.supercharge CIK)
      (Hk := Hk) (Z := Z) (C := C) hSplitQ hQC hZC

end DrazinLane

section RootLane

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Root/CPT specialization:
if a charge commutes with the CPT supercharge, it commutes with the extracted
kinetic part in the central split `Q² = H + Z`.
-/
@[rep_depth transport]
theorem cpt_noether_charge_of_central_split
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (C : EndH)
    (hQC :
      Commute
        (InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp (E := E))
        C) :
    Commute
      (cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX)
      C := by
  have hSplit :
      (InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp (E := E)).comp
        (InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp (E := E))
        =
      cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX
        + operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX := by
    exact
      cptSupercharge_sq_eq_kinetic_plus_centralChargeOperator
        (A := A) (B := B) (E := E) X hX
  have hZC :
      Commute
        (operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX)
        C := by
    exact operatorialCentralChargeOperator_commute (A := A) (B := B) (E := E) X hX C
  exact
    noether_charge_of_supercharge_split
      (Q := InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp (E := E))
      (Hk := cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX)
      (Z := operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX)
      (C := C)
      hSplit hQC hZC

/--
Commutator form of `cpt_noether_charge_of_central_split`.
-/
@[rep_depth transport]
theorem cpt_noether_commutator_of_central_split
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (C : EndH)
    (hQC :
      DrazinSupercharge.commutatorK
        (InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp (E := E))
        C = 0) :
    DrazinSupercharge.commutatorK
      (cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX)
      C = 0 := by
  have hSplit :
      (InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp (E := E)).comp
        (InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp (E := E))
        =
      cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX
        + operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX := by
    exact
      cptSupercharge_sq_eq_kinetic_plus_centralChargeOperator
        (A := A) (B := B) (E := E) X hX
  have hZC :
      DrazinSupercharge.commutatorK
        (operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX)
        C = 0 := by
    exact
      (drazinCommutator_eq_zero_iff_commute
        (A := operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX)
        (B := C)).2
        (operatorialCentralChargeOperator_commute (A := A) (B := B) (E := E) X hX C)
  exact
    noether_commutator_of_supercharge_split
      (Q := InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp (E := E))
      (Hk := cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX)
      (Z := operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX)
      (C := C)
      hSplit hQC hZC

end RootLane

end InfoGeometry.Canonical.KKTNoetherCharges
