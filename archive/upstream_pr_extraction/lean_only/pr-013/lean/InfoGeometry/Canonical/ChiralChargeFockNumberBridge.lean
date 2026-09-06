import InfoGeometry.Canonical.ClosureDrazinBridge
import InfoGeometry.Canonical.GlobalChiralDecomposition
import InfoGeometry.Canonical.GrandCanonicalFockNumberBridge
import InfoGeometry.Canonical.OperatorLightconeCoordinates
import InfoGeometry.Canonical.OperatorSpacetimeObservables
import InfoGeometry.Canonical.SuperchargeCARCCRBridge

/-!
# InfoGeometry.Canonical.ChiralChargeFockNumberBridge

Reconciliation surface for chiral polarization, supercharge defects, and Fock
number coupling.

This file deliberately does not identify all charge notions. It records the
source-owned spine:

- `P₊ - P₋` is the Krein signed polarization readout (`ε` channel),
- `Γ_G = P_R - P_L` is the Drazin/KKT chiral polarization,
- `Q_D = [P_D, Γ_G]` is the chiral defect/supercharge lane,
- `N_B = a†_B a_B` is the Fock occupation operator used by `H - μN_B`.

Any theorem equating `N_B` with a chiral defect, central charge, or finite count
profile requires an additional representation/occupation-readout theorem.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ChiralChargeFockNumberBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.ClosureDrazinBridge
open InfoGeometry.Canonical.GrandCanonicalFockNumberBridge
open InfoGeometry.Canonical.DrazinPenroseDilationKKT
open InfoGeometry.Canonical.GlobalChiralDecomposition
open InfoGeometry.Canonical.OperatorLightconeCoordinates
open InfoGeometry.Canonical.OperatorSpacetimeObservables
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.ChiralOperatorConeClosure

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Krein signed polarization readout: `ε` is the `P₊ - P₋` channel. -/
@[rep_depth transport]
theorem krein_signed_polarization_readout
    (ψ : H₂) :
    epsilonObservable (E := E) ψ =
      lightconePlusCoordinate (E := E) ψ - lightconeMinusCoordinate (E := E) ψ :=
  epsilonObservable_eq_lightconePlus_sub_lightconeMinus (E := E) ψ

/-- Drazin/KKT signed chiral polarization: `Γ_G = P_R - P_L`. -/
@[rep_depth krein]
theorem drazin_signed_chiral_polarization
    (K : DPDKKT H₂) :
    K.GammaG = K.P_R - K.P_L :=
  GlobalChiralDecomposition.chiralRangeDomain_decomposition (E := E) K

/-- Drazin supercharge is the commutator defect of the chiral polarization. -/
@[rep_depth krein]
theorem drazin_supercharge_eq_chiral_polarization_defect
    (C : ConstructiveClosureDrazinData (E := H₂)) :
    DrazinSupercharge.CertifiedInverseKernel.supercharge C.kernel =
      DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.GammaG :=
  C.supercharge_eq_commutator_P_D_GammaG

/-- The Drazin supercharge lies in the spectral chiral operator cone. -/
@[rep_depth krein]
theorem drazin_supercharge_mem_chiral_operator_cone
    (C : ConstructiveClosureDrazinData (E := H₂)) :
    IsInChiralOperatorCone C.kernel
      (DrazinSupercharge.CertifiedInverseKernel.supercharge C.kernel) :=
  C.supercharge_mem_chiralCone

/-- Drazin chiral defect is the right-minus-left anomaly channel. -/
@[rep_depth krein]
theorem drazin_chiral_defect_eq_right_minus_left
    (C : ConstructiveClosureDrazinData (E := H₂)) :
    DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.GammaG =
      C.kernel.rightChiralAnomaly - C.kernel.chiralAnomaly :=
  C.commutator_P_D_GammaG_eq_sub_anomalies

/-- Primitive doubled-carrier supercharges close by `[J, ε] = 2Q`. -/
@[rep_depth krein]
theorem primitive_supercharge_commutator_eq_two_cpt :
    CCRBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = (2 : ℝ) • cptSuperchargeOp (E := E) :=
  parity_modular_supercharge_ccrBracket_eq_two_cpt (E := E)

/-- Primitive doubled-carrier supercharges have vanishing odd-odd CAR channel. -/
@[rep_depth krein]
theorem primitive_supercharge_anticommutator_zero :
    CARBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = 0 :=
  parity_modular_supercharge_car_zero (E := E)

/-- Fock occupation is the ordered creation-after-annihilation operator. -/
@[rep_depth transport]
theorem fock_occupation_eq_creation_after_annihilation
    (B : BogoliubovMixingParams) :
    bogoliubovNumberOperator (E := E) B =
      (bogoliubovCreation (E := E) B).comp (bogoliubovAnnihilation (E := E) B) := by
  rfl

/-- Chemical potential couples to the Fock occupation operator in the `H - μN_B` lane. -/
@[rep_depth thermo]
theorem chemical_potential_couples_to_fock_occupation
    (B : BogoliubovMixingParams) (μ : ℝ) :
    (fockNumberGauge (E := E) B).gaugeOf μ =
      μ • bogoliubovNumberOperator (E := E) B :=
  fockNumberGauge_is_mu_times_numberOperator (E := E) B μ

/--
Reconciliation package: the three lanes are simultaneously available, but
remain distinct objects unless an explicit representation theorem identifies
their readouts.
-/
@[rep_depth transport]
structure ChiralChargeFockNumberReconciliation
    (C : ConstructiveClosureDrazinData (E := H₂))
    (B : BogoliubovMixingParams)
    (ψ : H₂) where
  kreinSignedPolarization :
    epsilonObservable (E := E) ψ =
      lightconePlusCoordinate (E := E) ψ - lightconeMinusCoordinate (E := E) ψ
  drazinSuperchargeDefect :
    DrazinSupercharge.CertifiedInverseKernel.supercharge C.kernel =
      DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.GammaG
  drazinRightMinusLeft :
    DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.GammaG =
      C.kernel.rightChiralAnomaly - C.kernel.chiralAnomaly
  fockNumberOccupation :
    bogoliubovNumberOperator (E := E) B =
      (bogoliubovCreation (E := E) B).comp (bogoliubovAnnihilation (E := E) B)

/--
Closure package for the chiral light-cone operator algebra across the current
owner lanes.

This records the same signed-polarization pattern at each level:
light-cone `P₊ - P₋`, KKT/TKK `P_R - P_L`, Drazin supercharge
`[P_D, Γ_G]`, and the primitive super-CAR/CCR closure.  The Fock number lane is
included only as the occupation operator coupled by `μ`; it is not identified
with the chiral defect without a representation theorem.
-/
@[rep_depth transport]
structure ChiralLightconeKKTClosure
    (C : ConstructiveClosureDrazinData (E := H₂))
    (B : BogoliubovMixingParams)
    (ψ : H₂) where
  lightconePolarization :
    epsilonObservable (E := E) ψ =
      lightconePlusCoordinate (E := E) ψ - lightconeMinusCoordinate (E := E) ψ
  kktChiralPolarization :
    (C.toDPDKKT).GammaG = (C.toDPDKKT).P_R - (C.toDPDKKT).P_L
  superchargeCommutatorClosure :
    DrazinSupercharge.CertifiedInverseKernel.supercharge C.kernel =
      DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.GammaG
  superchargeRightMinusLeftClosure :
    DrazinSupercharge.commutator C.kernel.spectralProjector C.kernel.GammaG =
      C.kernel.rightChiralAnomaly - C.kernel.chiralAnomaly
  primitiveCCRClosure :
    CCRBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = (2 : ℝ) • cptSuperchargeOp (E := E)
  primitiveCARClosure :
    CARBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = 0
  fockOccupation :
    bogoliubovNumberOperator (E := E) B =
      (bogoliubovCreation (E := E) B).comp (bogoliubovAnnihilation (E := E) B)

/-- Canonical constructor for the reconciliation package from existing owners. -/
@[rep_depth transport]
def ChiralChargeFockNumberReconciliation.ofOwners
    (C : ConstructiveClosureDrazinData (E := H₂))
    (B : BogoliubovMixingParams)
    (ψ : H₂) :
    ChiralChargeFockNumberReconciliation (E := E) C B ψ where
  kreinSignedPolarization :=
    krein_signed_polarization_readout (E := E) ψ
  drazinSuperchargeDefect :=
    drazin_supercharge_eq_chiral_polarization_defect (E := E) C
  drazinRightMinusLeft :=
    drazin_chiral_defect_eq_right_minus_left (E := E) C
  fockNumberOccupation :=
    fock_occupation_eq_creation_after_annihilation (E := E) B

/-- Canonical constructor for the chiral light-cone/KKT closure package. -/
@[rep_depth transport]
def ChiralLightconeKKTClosure.ofOwners
    (C : ConstructiveClosureDrazinData (E := H₂))
    (B : BogoliubovMixingParams)
    (ψ : H₂) :
    ChiralLightconeKKTClosure (E := E) C B ψ where
  lightconePolarization :=
    krein_signed_polarization_readout (E := E) ψ
  kktChiralPolarization :=
    drazin_signed_chiral_polarization (E := E) C.toDPDKKT
  superchargeCommutatorClosure :=
    drazin_supercharge_eq_chiral_polarization_defect (E := E) C
  superchargeRightMinusLeftClosure :=
    drazin_chiral_defect_eq_right_minus_left (E := E) C
  primitiveCCRClosure :=
    primitive_supercharge_commutator_eq_two_cpt (E := E)
  primitiveCARClosure :=
    primitive_supercharge_anticommutator_zero (E := E)
  fockOccupation :=
    fock_occupation_eq_creation_after_annihilation (E := E) B

end Core

end InfoGeometry.Canonical.ChiralChargeFockNumberBridge
