import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Canonical.CentralChargeKKTParityBridge
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
open InfoGeometry.Canonical.CentralChargeKKTParityBridge
open InfoGeometry.Canonical.ChiralDefectIndexBridge
open InfoGeometry.Canonical.KKTCore
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

/-- Root-name form of the same transported gap/Hessian closure proposition. -/
@[rep_depth transport]
def rootGapHessianClosure
    (V : BogoliubovVielbeinBundle (E := E)) : Prop :=
  ((modular_j (E := E)).comp (spectral_epsilon (E := E))
      - (spectral_epsilon (E := E)).comp (modular_j (E := E))
      = (2 : ℝ) • complex_i (E := E))
    ∧
  (transportedParityModularGapSeed (E := E) V
      =
    CARBracket (E := E)
      (transportCommutator (E := E) V.connectionGenerator (modular_j (E := E)))
      (spectral_epsilon (E := E)))
    ∧
  (let X := V.connectionGenerator;
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    operatorInformationHessian (E := E) X (modular_j (E := E)))
    ∧
  (let X := V.connectionGenerator;
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    operatorInformationMetricPart (E := E) X X (modular_j (E := E))
      + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) X X
          (modular_j (E := E)))

/-- The root-name and bilingual CPT-name closure propositions are equivalent. -/
@[rep_depth transport]
theorem rootGapHessianClosure_iff_cptGapHessianClosure
    (V : BogoliubovVielbeinBundle (E := E)) :
    rootGapHessianClosure (E := E) V ↔ cptGapHessianClosure (E := E) V := by
  constructor <;> intro h
  · rcases h with ⟨hCCR, hGap, hHess, hSplit⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [cptSuperchargeOp_eq_complex_i] using hCCR
    · simpa using hGap
    · simpa using hHess
    · simpa using hSplit
  · rcases h with ⟨hCCR, hGap, hHess, hSplit⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [cptSuperchargeOp_eq_complex_i] using hCCR
    · simpa using hGap
    · simpa using hHess
    · simpa using hSplit

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

/--
Parity/KKT extension of the CPT-supercharge closure:

1. keeps the existing transported CPT gap/Hessian closure package,
2. upgrades nonzero `Z₂` central-charge parity to transported chiral mismatch,
3. and carries the same Dirac carrier through the KKT odd split with
   grade-zero odd-odd commutator once `gradeCLM = eps`.
-/
@[rep_depth transport]
theorem cpt_gap_hessian_parity_kkt_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    cptGapHessianClosure (E := E) V
      ∧
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
      V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧
    X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
      ∧
    IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) := by
  rcases cpt_gap_hessian_centralCharge_closure
      (A := A) (B := B) (E := E) V X hX hEven t with ⟨hGap, _, _⟩
  have hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
        V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) :=
    transportedChiralKernelDimMismatch_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven t hParity
  have hKKT :
      X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
        ∧ IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) :=
    dirac_kkt_odd_split_and_commutator_isGZero_of_gradeCLM_eq_eps
      (A := A) (B := B) (E := E) X hGrade
  exact ⟨hGap, hMismatch, hKKT.1, hKKT.2⟩

/--
Extended closure package:
the concrete oscillator/CAR spine, transported gap/Hessian closure, and
transported central-charge/index closure are carried on the same lane.
-/
@[rep_depth transport]
theorem cpt_gap_hessian_centralCharge_with_oscillator_spine
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (CARBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = 0
      ∧ CCRBracket (E := E)
          (paritySuperchargeOp (E := E))
          (modularSuperchargeOp (E := E))
        = (2 : ℝ) • cptSuperchargeOp (E := E)
      ∧ (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E))
          = -(ContinuousLinearMap.id ℝ (DoubledSpace E))
      ∧ CARBracket (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARAnnihilation (E := E))
        = 0
      ∧ CARBracket (E := E)
          (concreteCARCreation (E := E))
          (concreteCARCreation (E := E))
        = 0
      ∧ CARBracket (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
        = ContinuousLinearMap.id ℝ (DoubledSpace E))
      ∧
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
  rcases cpt_gap_hessian_centralCharge_closure
      (A := A) (B := B) (E := E) V X hX hEven t with
    ⟨hGap, hIdx, hNz⟩
  exact ⟨harmonic_oscillator_spine (E := E), hGap, hIdx, hNz⟩

/--
Root-name form of the full supercharge/gap/Hessian/central-charge closure
package.
-/
@[rep_depth transport]
theorem root_gap_hessian_centralCharge_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    rootGapHessianClosure (E := E) V
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
  rcases cpt_gap_hessian_centralCharge_closure
      (A := A) (B := B) (E := E) V X hX hEven t with ⟨hGap, hIdx, hNz⟩
  refine ⟨?_, hIdx, hNz⟩
  exact (rootGapHessianClosure_iff_cptGapHessianClosure (E := E) V).2 hGap

/--
Root-name parity/KKT extension of the transported supercharge closure.
-/
@[rep_depth transport]
theorem root_gap_hessian_parity_kkt_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    rootGapHessianClosure (E := E) V
      ∧
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
      V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧
    X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
      ∧
    IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) := by
  rcases cpt_gap_hessian_parity_kkt_closure
      (A := A) (B := B) (E := E) V X hX hEven t hParity hGrade with
    ⟨hGap, hMismatch, hSplit, hCommZero⟩
  refine ⟨?_, hMismatch, hSplit, hCommZero⟩
  exact (rootGapHessianClosure_iff_cptGapHessianClosure (E := E) V).2 hGap

/--
Root-name Lichnerowicz/charge closure on the transported supercharge lane:

1. the second transported parity-supercharge variation is the repo-native
   Laplace term `operatorInformationMetricPart` plus half the curvature
   correction,
2. the transported analytical index equals the operatorial central charge,
3. nonzero operatorial central charge forces nonvanishing transported index.
-/
@[rep_depth transport]
theorem root_supercharge_lichnerowicz_centralCharge_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (let X := V.connectionGenerator;
      deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
        =
      operatorInformationMetricPart (E := E) X X (modular_j (E := E))
        + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) X X
            (modular_j (E := E)))
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
  rcases root_gap_hessian_centralCharge_closure
      (A := A) (B := B) (E := E) V X hX hEven t with ⟨hRoot, hIdx, hNz⟩
  rcases hRoot with ⟨_, _, _, hLich⟩
  exact ⟨hLich, hIdx, hNz⟩

end Core

end InfoGeometry.Canonical.SuperchargeCentralChargeClosure
