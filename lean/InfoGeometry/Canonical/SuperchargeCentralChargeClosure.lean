import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Canonical.SuperchargeGapHessianBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SuperchargeCentralChargeClosure

Closure package for the currently-owned operatorial supercharge lane.

This file does not postulate a new “gap = charge” ontology. It only places the
existing owners on one transport slice:

- `SuperchargeGapHessianBridge` supplies the CPT-supercharge CCR anchor, the
  first odd-odd gap seed landing, and the second Hessian/curvature landing;
- `OperatorialCentralCharge` supplies the KK/Fredholm analytical-index owner
  and its transport-protected nonvanishing law.

The result is a single closure theorem surface for downstream DIII/topological
transport files.
-/

namespace InfoGeometry.Canonical.SuperchargeCentralChargeClosure

open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.SuperchargeGapHessianBridge
open InfoGeometry.Canonical.SuperchargeGapBridge
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.SuperchargeTransportBridge
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein

section Core

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/-- Local alias for the owned CPT gap/Hessian closure proposition. -/
@[rep_depth transport]
def cptGapHessianClosure
    (V : BogoliubovVielbeinBundle (E := E)) : Prop :=
  ((paritySuperchargeOp (E := E)).comp (modularSuperchargeOp (E := E))
      - (modularSuperchargeOp (E := E)).comp (paritySuperchargeOp (E := E))
      = (2 : ℝ) • cptSuperchargeOp (E := E))
    ∧
  (transportedParityModularGapSeed (E := E) V
      =
    CARBracket (E := E)
      (transportCommutator (E := E) V.connectionGenerator (paritySuperchargeOp (E := E)))
      (modularSuperchargeOp (E := E)))
    ∧
  (let X := V.connectionGenerator;
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    operatorInformationHessian (E := E) X (paritySuperchargeOp (E := E)))
    ∧
  (let X := V.connectionGenerator;
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    operatorInformationMetricPart (E := E) X X (paritySuperchargeOp (E := E))
      + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) X X
          (paritySuperchargeOp (E := E)))

/--
On every Bogoliubov transport slice, the operatorial KK index is exactly the
operatorial central charge.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_eq_operatorialCentralCharge_on_cpt_lane
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX := by
  exact operatorialCentralCharge_eq_transport_slice
    (A := A) (B := B) (E := E) V X hX hEven t

/--
Closure package for the CPT-supercharge lane:

1. primitive `J/ε` CCR anchor,
2. first transport landing as the odd-odd gap seed,
3. second transport landing as the operatorial Hessian,
4. Hessian split into metric plus half-curvature,
5. transported analytical index equals the operatorial central charge,
6. nonzero operatorial central charge forces nonvanishing transported index.
-/
@[rep_depth transport]
theorem cpt_gap_hessian_centralCharge_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    cptGapHessianClosure (E := E) V
      ∧
    (quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 →
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact transported_gapSeed_hessian_curvature_cpt_package (E := E) V
  · exact quasilatticeAnalyticalIndex_eq_operatorialCentralCharge_on_cpt_lane
      (A := A) (B := B) (E := E) V X hX hEven t
  · intro hCentral
    exact quasilatticeSlice_ne_zero_of_operatorialCentralCharge_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven hCentral t

end Core

end InfoGeometry.Canonical.SuperchargeCentralChargeClosure
