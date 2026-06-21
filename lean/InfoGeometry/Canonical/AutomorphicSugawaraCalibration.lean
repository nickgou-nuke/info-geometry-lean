import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Automorphic.HeckePurification
import InfoGeometry.Automorphic.ProjectedLFunction
import InfoGeometry.Automorphic.LanglandsSugawaraBridge

/-!
# InfoGeometry.Canonical.AutomorphicSugawaraCalibration

Canonical wrapper for the existing automorphic/Sugawara calibration theorems.

This file does not add new analytic content. It re-exports the already-native
bridge readouts under a canonical owner-facing namespace.
-/

noncomputable section

namespace InfoGeometry.Canonical.AutomorphicSugawaraCalibration

open InfoGeometry.Automorphic
open InfoGeometry.Automorphic.SiegelResonance
open InfoGeometry.Automorphic.LFunctionResonance
open InfoGeometry.Automorphic.RoelckeSelbergSpectral
open InfoGeometry.Automorphic.HeckePurification
open InfoGeometry.Automorphic.HeckePurification.HeckeSugawaraIntertwining
open InfoGeometry.OperatorAlgebra.ExceptionalVirasoroBridge
open InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge
open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
open InfoGeometry.OperatorAlgebra.HorizonKMS

universe uBulk uBoundary uHecke

/-- Canonical re-export of the raw-to-cuspidal projection theorem. -/
theorem cuspidalLFunction_eq_raw_of_siegel_zero
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (Λ : AutomorphicLFunctional Bulk)
    (F : Bulk)
    (hF : W.siegel F = 0) :
    cuspidalLFunction W Λ F = rawLFunction Λ F :=
  W.cuspidalLFunction_eq_raw_of_siegel_zero Λ F hF

/-- Canonical re-export of the projected-L evaluation theorem. -/
theorem projectedL_eval_eq_projected
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (P : ProjectedAutomorphicLFunctionWitness W)
    (s : ℂ) :
    P.L s =
      P.functional.coeff s (W.cuspidalProjector P.bulkState) :=
  P.eval_eq_projected s

/-- Canonical re-export of the projected-L resonance/zero theorem. -/
theorem projectedL_resonance_iff_zero
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (P : ProjectedAutomorphicLFunctionWitness W)
    (s : ℂ) :
    IsAutomorphicResonance P.L s ↔
      P.functional.coeff s (W.cuspidalProjector P.bulkState) = 0 :=
  P.resonance_iff_projected_zero s

/-- Canonical re-export of the projected-L owner target. -/
theorem projectedAutomorphicLFunctionOwnerTarget :
    ProjectedAutomorphicLFunctionOwnerTarget := by
  intro Bulk _ _ Boundary _ _ W Λ F
  exact ⟨{
    functional := Λ
    bulkState := F
    L := cuspidalLFunction W Λ F
    L_eq_projected := rfl
  }⟩

/--
Canonical re-export of the Hecke/Sugawara scalar calibration theorem.
-/
theorem hecke_sugawara_scalar_calibration
    {Bulk : Type uBulk} {Boundary : Type uBoundary} {HeckeIndex : Type uHecke}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {R : RoelckeSelbergSpectralDatum W HeckeIndex}
    {J L Obs Memory Finite AffineAlg Vir State Charge : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg] [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Charge] [Module ℝ Charge]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {B : HorizonExceptionalVirasoroBridge J L Obs Memory Finite AffineAlg A}
    {EAV : ExceptionalAffineVirasoroBridge Finite AffineAlg Vir State Charge}
    {charge_eval : Charge → ℂ}
    {L_func : AutomorphicLFunctionDatum HeckeIndex}
    (H : HeckeSugawaraIntertwining R B EAV charge_eval L_func)
    (chi : JointEigenvalue HeckeIndex)
    (P : CuspidalEigenpacket R chi)
    (s : State) :
    charge_eval (EAV.centralChargeReadout s) = L_func.value chi 0 :=
  H.purified_charge_eq_l_value chi P s

/-- Canonical re-export of the hidden grade-memory / Hecke L-value theorem. -/
theorem hecke_hiddenGradeMemory_calibration
    {Bulk : Type uBulk} {Boundary : Type uBoundary} {HeckeIndex : Type uHecke}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {R : RoelckeSelbergSpectralDatum W HeckeIndex}
    {J L Obs Memory Finite AffineAlg Vir State Charge : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg] [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Charge] [Module ℝ Charge]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {B : HorizonExceptionalVirasoroBridge J L Obs Memory Finite AffineAlg A}
    {EAV : ExceptionalAffineVirasoroBridge Finite AffineAlg Vir State Charge}
    {charge_eval : Charge → ℂ}
    {L_func : AutomorphicLFunctionDatum HeckeIndex}
    (H : HeckeSugawaraIntertwining R B EAV charge_eval L_func)
    (chi : JointEigenvalue HeckeIndex)
    (P : CuspidalEigenpacket R chi)
    (s : State) :
    charge_eval (EAV.hiddenGradeMemoryReadout s) = L_func.value chi 0 :=
  H.hiddenGradeMemory_eq_l_value chi P s

/--
Canonical re-export of the bridge rewrite theorem at projected L-value zero.
-/
theorem langlands_sugawara_bridge_readout
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {P : ProjectedAutomorphicLFunctionWitness W}
    {Finite Affine Vir State : Type*}
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (B : LanglandsSugawaraBridge P Finite Affine Vir State)
    (hspectral : B.spectralPoint = 0)
    (hcompleted : B.completedL = P.L) :
    B.affineVirasoro.centralChargeReadout B.state = P.L 0 :=
  B.centralCharge_eq_projectedL_zero_of_match hspectral hcompleted

end InfoGeometry.Canonical.AutomorphicSugawaraCalibration
