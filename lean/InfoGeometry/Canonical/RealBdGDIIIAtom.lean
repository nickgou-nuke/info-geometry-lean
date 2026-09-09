import InfoGeometry.Canonical.ProjectorEquivariance
import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Canonical.CentralChargeKKTParityBridge
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.SuperchargeCentralChargeClosure
import InfoGeometry.Canonical.TopologicalInvariantInvariance
import InfoGeometry.Canonical.DIIICommutatorInitialization
import InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv
import InfoGeometry.Canonical.AnalyticalIndexCore
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.RealBdGDIIIAtom

Canonical DIII proxy package on the doubled real BdG carrier.

This file does not introduce a second DIII ontology. It reuses the repo-owned
operators already stabilized elsewhere:

- `T := K = Jε` as the real-linear time-reversal proxy,
- `C := J` as the particle-hole proxy,
- `S := -ε` as the induced chiral proxy,
- the concrete `u_-`,`u_+` CAR pair from the split-`Cl(1,1)` realization,
- and the existing CPT gap/Hessian/central-charge closure lane.

The raw `Physics/DIIISymmetryAtom` file stays quarantined; this file is the
owner-respecting canonical closure surface.
-/

namespace InfoGeometry.Canonical.RealBdGDIIIAtom

open InfoGeometry.Canonical.AnalyticalIndex
open InfoGeometry.Canonical.ChiralDefectIndexBridge
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Canonical.RealBdG
open InfoGeometry.Canonical.CentralChargeKKTParityBridge
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.SuperchargeCentralChargeClosure
open InfoGeometry.Canonical.TopologicalInvariantInvariance
open InfoGeometry.Canonical.DIIICommutatorInitialization
open InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Narrow real-linear proxy package for the DIII atom on the doubled carrier. -/
structure DIIISymmetryProxy where
  T : EndH
  C : EndH
  S : EndH
  T_sq : T.comp T = -(ContinuousLinearMap.id ℝ H₂)
  C_sq : C.comp C = ContinuousLinearMap.id ℝ H₂
  TC_eq_S : T.comp C = S
  CT_eq_neg_S : C.comp T = -S

/-- The canonical CPT supercharge agrees with the real BdG `K` axis. -/
@[rep_depth krein, simp] theorem cptSuperchargeOp_eq_modularK :
    cptSuperchargeOp (E := E) = modularK (E := E) := by
  calc
    cptSuperchargeOp (E := E) = dilationOperator (E := E) := by
      exact cptSuperchargeOp_eq_dilationOperator (E := E)
    _ = complex_i (E := E) := dilationOperator_eq_complex_i (E := E)
    _ = modularK (E := E) := by
      exact (modularK_eq_modularComplexI (E := E)).symm

@[rep_depth krein, simp] theorem cptSuperchargeOp_eq_modularK_root :
    cptSuperchargeOp (E := E) = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by
  calc
    cptSuperchargeOp (E := E) = modularK (E := E) := cptSuperchargeOp_eq_modularK (E := E)
    _ = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by
      rfl

/-- Canonical DIII proxy package on the doubled real BdG atom. -/
@[rep_depth transport]
noncomputable def canonicalDIIIProxy : DIIISymmetryProxy (E := E) where
  T := cptSuperchargeOp (E := E)
  C := paritySuperchargeOp (E := E)
  S := -(modularSuperchargeOp (E := E))
  T_sq := cptSuperchargeOp_sq (E := E)
  C_sq := by
    change (modular_j (E := E)).comp (modular_j (E := E)) = ContinuousLinearMap.id ℝ H₂
    exact modular_j_involution (E := E)
  TC_eq_S := by
    calc
      (cptSuperchargeOp (E := E)).comp (paritySuperchargeOp (E := E))
          = (complex_i (E := E)).comp (modular_j (E := E)) := by
              simp [paritySuperchargeOp]
      _ = -(spectral_epsilon (E := E)) := by
            exact complex_i_comp_modular_j (E := E)
      _ = -(modularSuperchargeOp (E := E)) := by rfl
  CT_eq_neg_S := by
    calc
      (paritySuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E))
          = (modular_j (E := E)).comp (complex_i (E := E)) := by
              simp [paritySuperchargeOp]
      _ = spectral_epsilon (E := E) := by
            exact modular_j_comp_complex_i (E := E)
      _ = -(-(modularSuperchargeOp (E := E))) := by
            simp [modularSuperchargeOp]

/-- The canonical DIII proxy has chiral operator `S = -ε`. -/
@[rep_depth transport, simp] theorem canonicalDIIIProxy_S_eq_neg_modularSuperchargeOp :
    (canonicalDIIIProxy (E := E)).S = -(modularSuperchargeOp (E := E)) := rfl

@[rep_depth transport, simp] theorem canonicalDIIIProxy_S_eq_neg_spectral_epsilon :
    (canonicalDIIIProxy (E := E)).S = -(spectral_epsilon (E := E)) := by
  rfl

/-- The canonical DIII proxy has time-reversal proxy `T = K`. -/
@[rep_depth transport, simp] theorem canonicalDIIIProxy_T_eq_cptSuperchargeOp :
    (canonicalDIIIProxy (E := E)).T = cptSuperchargeOp (E := E) := rfl

@[rep_depth transport, simp] theorem canonicalDIIIProxy_T_eq_modularK :
    (canonicalDIIIProxy (E := E)).T = modularK (E := E) := by
  rw [canonicalDIIIProxy_T_eq_cptSuperchargeOp (E := E)]
  exact cptSuperchargeOp_eq_modularK (E := E)

@[rep_depth transport, simp] theorem canonicalDIIIProxy_T_eq_complex_i :
    (canonicalDIIIProxy (E := E)).T = complex_i (E := E) := by
  rw [canonicalDIIIProxy_T_eq_modularK (E := E)]
  exact modularK_eq_complex_i (E := E)

/-- The canonical DIII proxy has particle-hole proxy `C = J`. -/
@[rep_depth transport, simp] theorem canonicalDIIIProxy_C_eq_paritySuperchargeOp :
    (canonicalDIIIProxy (E := E)).C = paritySuperchargeOp (E := E) := rfl

@[rep_depth transport, simp] theorem canonicalDIIIProxy_C_eq_modular_j :
    (canonicalDIIIProxy (E := E)).C = modular_j (E := E) := by
  rfl

/-- Packaged symmetry laws for the canonical DIII proxy. -/
@[rep_depth transport]
theorem canonicalDIIIProxy_laws :
    let P := canonicalDIIIProxy (E := E)
    P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
      ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
      ∧ P.T.comp P.C = P.S
      ∧ P.C.comp P.T = -P.S := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (canonicalDIIIProxy (E := E)).T_sq
  · exact (canonicalDIIIProxy (E := E)).C_sq
  · exact (canonicalDIIIProxy (E := E)).TC_eq_S
  · exact (canonicalDIIIProxy (E := E)).CT_eq_neg_S

/-- Root-name packaged symmetry laws for the canonical DIII proxy. -/
@[rep_depth transport]
theorem canonicalDIIIProxy_root_laws :
    let P := canonicalDIIIProxy (E := E)
    P.T = complex_i (E := E)
      ∧ P.C = modular_j (E := E)
      ∧ P.S = -(spectral_epsilon (E := E))
      ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
      ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
      ∧ P.T.comp P.C = -(spectral_epsilon (E := E))
      ∧ P.C.comp P.T = spectral_epsilon (E := E) := by
  refine ⟨canonicalDIIIProxy_T_eq_complex_i (E := E), canonicalDIIIProxy_C_eq_modular_j (E := E),
    canonicalDIIIProxy_S_eq_neg_spectral_epsilon (E := E), ?_, ?_, ?_, ?_⟩
  · exact (canonicalDIIIProxy (E := E)).T_sq
  · exact (canonicalDIIIProxy (E := E)).C_sq
  · simpa [canonicalDIIIProxy_S_eq_neg_spectral_epsilon (E := E)] using
      (canonicalDIIIProxy (E := E)).TC_eq_S
  · simpa [canonicalDIIIProxy_S_eq_neg_spectral_epsilon (E := E)] using
      (canonicalDIIIProxy (E := E)).CT_eq_neg_S

/--
The canonical DIII proxy instantiates the thin `TopologicalClassDIII` package
on every real BdG datum whose chiral lane is `J`.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum
    (X : RealBdGDatum (E := E))
    (hChiral : X.chiral = modular_j (E := E)) :
    TopologicalClassDIII (E := E)
      X.H
      (canonicalDIIIProxy (E := E)).T
      (canonicalDIIIProxy (E := E)).C := by
  have hBase :
      TopologicalClassDIII (E := E) X.H (modularK (E := E)) (modular_j (E := E)) :=
    topologicalClassDIII_of_realBdGDatum (E := E) X hChiral
  simpa [canonicalDIIIProxy_T_eq_modularK (E := E), canonicalDIIIProxy_C_eq_modular_j (E := E)] using hBase

/--
Canonical DIII commutator packet on a real BdG datum:
`[T,H]=0` and `{C,H}=0`, with `T,C` taken from `canonicalDIIIProxy`.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_commutator_packet_of_realBdGDatum
    (X : RealBdGDatum (E := E))
    (hChiral : X.chiral = modular_j (E := E)) :
    endCommutator
        (E := E)
        (canonicalDIIIProxy (E := E)).T
        X.H = 0
      ∧
    endAnticommutator
        (E := E)
        (canonicalDIIIProxy (E := E)).C
        X.H = 0 := by
  letI :
      TopologicalClassDIII (E := E)
        X.H
        (canonicalDIIIProxy (E := E)).T
        (canonicalDIIIProxy (E := E)).C :=
    canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum (E := E) X hChiral
  have hComm :
      endCommutator
          (E := E)
          (canonicalDIIIProxy (E := E)).T
          X.H = 0 :=
    commutator_T_H_eq_zero
      (E := E)
      (H := X.H)
      (T := (canonicalDIIIProxy (E := E)).T)
      (P := (canonicalDIIIProxy (E := E)).C)
  have hAnti :
      endAnticommutator
          (E := E)
          (canonicalDIIIProxy (E := E)).C
          X.H = 0 :=
    anticommutator_P_H_eq_zero
      (E := E)
      (H := X.H)
      (T := (canonicalDIIIProxy (E := E)).T)
      (P := (canonicalDIIIProxy (E := E)).C)
  exact ⟨hComm, hAnti⟩

/-- The canonical time-reversal proxy swaps positive chiral vectors to negative ones. -/
@[rep_depth transport]
theorem canonicalDIIIProxy_T_maps_plus_to_minus
    {v : H₂} (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) ((canonicalDIIIProxy (E := E)).T v) := by
  simpa [canonicalDIIIProxy] using cptSuperchargeOp_maps_plus_to_minus (E := E) hv

/-- The canonical time-reversal proxy swaps negative chiral vectors to positive ones. -/
@[rep_depth transport]
theorem canonicalDIIIProxy_T_maps_minus_to_plus
    {v : H₂} (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) ((canonicalDIIIProxy (E := E)).T v) := by
  simpa [canonicalDIIIProxy] using cptSuperchargeOp_maps_minus_to_plus (E := E) hv

/-- The canonical DIII atom carries the concrete split-`Cl(1,1)` CAR pair. -/
@[rep_depth transport]
theorem canonicalDIIIProxy_concreteCARPair :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
      (concreteCARAnnihilation (E := E))
      (concreteCARCreation (E := E)) := by
  exact concrete_car_pair

/-- The concrete DIII atom realizes the mixed CAR identity `{u_-,u_+} = 1`. -/
@[rep_depth transport]
theorem canonicalDIIIProxy_concreteCAR :
    CARBracket (E := E)
        (concreteCARAnnihilation (E := E))
        (concreteCARCreation (E := E))
      = ContinuousLinearMap.id ℝ H₂ := by
  exact concrete_car_minus_plus (E := E)

section FixedGrading

variable [FiniteDimensional ℝ E]

/--
With the DIII chiral proxy `S = -ε`, the fixed-grading analytical index is the
negated `ε`-graded analytical index.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_fixedGradingIndexSign
    (D : EndH) :
    InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex D.toLinearMap
      ((canonicalDIIIProxy (E := E)).S.toLinearMap)
      =
    -InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex D.toLinearMap
      ((modularSuperchargeOp (E := E)).toLinearMap) := by
  simpa [canonicalDIIIProxy] using
    (analyticalIndex_neg_grading_eq_neg
      (V := H₂)
      (D := D.toLinearMap)
      (Γ := (modularSuperchargeOp (E := E)).toLinearMap))

end FixedGrading

end Core

section Closure

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Canonical DIII atom closure on a transport slice:

1. the DIII proxy symmetry laws,
2. the concrete split-`Cl(1,1)` CAR pair,
3. the existing CPT gap/Hessian/central-charge closure.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_transport_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (let P := canonicalDIIIProxy (E := E);
      P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
        ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
        ∧ P.T.comp P.C = P.S
        ∧ P.C.comp P.T = -P.S)
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
      ∧ (cptGapHessianClosure (E := E) V
          ∧
        (quasilatticeAnalyticalIndex V X t
            (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
          =
        InfoGeometry.Canonical.OperatorialCentralCharge.operatorialCentralCharge
          (A := A) (B := B) (E := E) X hX)
          ∧
        (InfoGeometry.Canonical.OperatorialCentralCharge.operatorialCentralCharge
            (A := A) (B := B) (E := E) X hX ≠ 0 →
          quasilatticeAnalyticalIndex V X t
              (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
            ≠ 0)) := by
  refine ⟨canonicalDIIIProxy_laws (E := E), canonicalDIIIProxy_concreteCARPair, ?_⟩
  exact cpt_gap_hessian_centralCharge_closure
    (A := A) (B := B) (E := E) V X hX hEven t

/--
Root-name form of the canonical DIII atom closure on a transport slice.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_transport_root_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (let P := canonicalDIIIProxy (E := E);
      P.T = complex_i (E := E)
        ∧ P.C = modular_j (E := E)
        ∧ P.S = -(spectral_epsilon (E := E))
        ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
        ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
        ∧ P.T.comp P.C = -(spectral_epsilon (E := E))
        ∧ P.C.comp P.T = spectral_epsilon (E := E))
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
      ∧ (rootGapHessianClosure (E := E) V
          ∧
        (quasilatticeAnalyticalIndex V X t
            (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
          =
        InfoGeometry.Canonical.OperatorialCentralCharge.operatorialCentralCharge
          (A := A) (B := B) (E := E) X hX)
          ∧
        (InfoGeometry.Canonical.OperatorialCentralCharge.operatorialCentralCharge
            (A := A) (B := B) (E := E) X hX ≠ 0 →
          quasilatticeAnalyticalIndex V X t
              (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
            ≠ 0)) := by
  refine ⟨canonicalDIIIProxy_root_laws (E := E), canonicalDIIIProxy_concreteCARPair, ?_⟩
  exact root_gap_hessian_centralCharge_closure
    (A := A) (B := B) (E := E) V X hX hEven t

/--
Root-name DIII/commutator closure on a transport slice:

1. canonical DIII proxy root laws,
2. concrete split-`Cl(1,1)` CAR pair,
3. nonzero transported analytical index forces nonzero transport commutator with
   `ε` under source/sink boundary identification.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_transport_root_index_commutator_closure
    [FiniteDimensional ℝ E]
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0)
    (hBoundary :
      S.boundaryGenerator = InfoGeometry.Canonical.VortexAnomalyLink.sourceVortexSeed (E := E) V
        ∨ S.boundaryGenerator = InfoGeometry.Canonical.VortexAnomalyLink.sinkVortexSeed (E := E) V) :
    (let P := canonicalDIIIProxy (E := E);
      P.T = complex_i (E := E)
        ∧ P.C = modular_j (E := E)
        ∧ P.S = -(spectral_epsilon (E := E))
        ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
        ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
        ∧ P.T.comp P.C = -(spectral_epsilon (E := E))
        ∧ P.C.comp P.T = spectral_epsilon (E := E))
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
      ∧
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
        V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 := by
  refine ⟨canonicalDIIIProxy_root_laws (E := E), canonicalDIIIProxy_concreteCARPair, ?_⟩
  exact
    quasilatticeAnalyticalIndex_ne_zero_transportCommutator_spectral_epsilon_ne_zero_of_boundaryGenerator_eq_source_or_sink_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E)
      V X hX hEven t M P0 S hA hplus hminus hodd hBoundaryOnZeroModes hIndexNonzero hBoundary

/--
Root-name DIII/commutator closure on a transport slice, central-charge-native
form:

1. canonical DIII proxy root laws,
2. concrete split-`Cl(1,1)` CAR pair,
3. nonzero operatorial central charge forces nonzero transport commutator with
   `ε` under source/sink boundary identification.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_transport_root_centralCharge_commutator_closure
    [FiniteDimensional ℝ E]
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hCentral :
      InfoGeometry.Canonical.OperatorialCentralCharge.operatorialCentralCharge
        (A := A) (B := B) (E := E) X hX ≠ 0)
    (hBoundary :
      S.boundaryGenerator = InfoGeometry.Canonical.VortexAnomalyLink.sourceVortexSeed (E := E) V
        ∨ S.boundaryGenerator = InfoGeometry.Canonical.VortexAnomalyLink.sinkVortexSeed (E := E) V) :
    (let P := canonicalDIIIProxy (E := E);
      P.T = complex_i (E := E)
        ∧ P.C = modular_j (E := E)
        ∧ P.S = -(spectral_epsilon (E := E))
        ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
        ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
        ∧ P.T.comp P.C = -(spectral_epsilon (E := E))
        ∧ P.C.comp P.T = spectral_epsilon (E := E))
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
      ∧
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
        V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 := by
  refine ⟨canonicalDIIIProxy_root_laws (E := E), canonicalDIIIProxy_concreteCARPair, ?_⟩
  exact
    operatorialCentralCharge_ne_zero_transportCommutator_spectral_epsilon_ne_zero_of_boundaryGenerator_eq_source_or_sink_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E)
      V X hX hEven t M P0 S hA hplus hminus hodd hBoundaryOnZeroModes hCentral hBoundary

/--
Parity-lifted DIII/KKT closure on a transport slice:

1. canonical DIII proxy symmetry laws,
2. concrete split-`Cl(1,1)` CAR pair,
3. nonzero `Z₂` central-charge parity forces transported chiral mismatch,
4. and the same Dirac carrier admits the KKT odd split with grade-zero
   odd-odd commutator once `gradeCLM = eps`.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_transport_parity_kkt_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    (let P := canonicalDIIIProxy (E := E);
      P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
        ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
        ∧ P.T.comp P.C = P.S
        ∧ P.C.comp P.T = -P.S)
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
      ∧
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
        V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧
      X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
      ∧
      IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) := by
  rcases cpt_gap_hessian_parity_kkt_closure
      (A := A) (B := B) (E := E) V X hX hEven t hParity hGrade with
    ⟨_, hMismatch, hSplit, hCommZero⟩
  exact ⟨canonicalDIIIProxy_laws (E := E), canonicalDIIIProxy_concreteCARPair,
    hMismatch, hSplit, hCommZero⟩

/--
Root-name parity-lifted DIII/KKT closure on a transport slice.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_transport_root_parity_kkt_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    (let P := canonicalDIIIProxy (E := E);
      P.T = complex_i (E := E)
        ∧ P.C = modular_j (E := E)
        ∧ P.S = -(spectral_epsilon (E := E))
        ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
        ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
        ∧ P.T.comp P.C = -(spectral_epsilon (E := E))
        ∧ P.C.comp P.T = spectral_epsilon (E := E))
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
      ∧
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
        V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧
      X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
      ∧
      IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) := by
  rcases root_gap_hessian_parity_kkt_closure
      (A := A) (B := B) (E := E) V X hX hEven t hParity hGrade with
    ⟨_, hMismatch, hSplit, hCommZero⟩
  exact ⟨canonicalDIIIProxy_root_laws (E := E), canonicalDIIIProxy_concreteCARPair,
    hMismatch, hSplit, hCommZero⟩

/--
Root-name parity/boundary/KKT/head-superbracket closure on a transport slice.

This is the single DIII-facing entry point that reuses the topological package
layer instead of duplicating parity-to-boundary and KKT/head algebra arguments.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_transport_root_parity_boundary_kkt_headSuperBracket_closure
    [FiniteDimensional ℝ E]
    (n : ℕ)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    (let P := canonicalDIIIProxy (E := E);
      P.T = complex_i (E := E)
        ∧ P.C = modular_j (E := E)
        ∧ P.S = -(spectral_epsilon (E := E))
        ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
        ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
        ∧ P.T.comp P.C = -(spectral_epsilon (E := E))
        ∧ P.C.comp P.T = spectral_epsilon (E := E))
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
      ∧ S.boundaryScale ≠ 0
      ∧ InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          (A := A) (B := B) (E := E)
          V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧ X.F =
          InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F
          + InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F
      ∧ InfoGeometry.Canonical.KKTCore.IsGZero X.cl11
          (InfoGeometry.Canonical.KKTCore.commutator
            (InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F)
            (InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F))
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n
          * InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n = 0
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n
          * InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n = 0
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headAnticommutator
          (InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n)
          (InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n) = 1
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headCommutator
          (InfoGeometry.Canonical.SplitCliffordHeadLift.headJTensor n)
          (InfoGeometry.Canonical.SplitCliffordHeadLift.headKTensor n)
          = (2 : ℝ) • InfoGeometry.Canonical.SplitCliffordHeadLift.headEpsTensor n := by
  rcases
      operatorialCentralChargeParity_ne_zero_boundaryScale_kkt_and_headSuperBracket_package_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) n V X hX hEven t M P0 S hA hplus hminus hodd
        hBoundaryOnZeroModes hParity hGrade with
    ⟨hBoundary, hMismatch, hSplit, hCommZero, hNullMinusSq, hNullPlusSq, hCAR, hJK⟩
  exact ⟨canonicalDIIIProxy_root_laws (E := E), canonicalDIIIProxy_concreteCARPair,
    hBoundary, hMismatch, hSplit, hCommZero, hNullMinusSq, hNullPlusSq, hCAR, hJK⟩

/--
Root-name parity/boundary-generator/KKT/head-superbracket closure on a
transport slice.

This is the generator-facing variant of
`canonicalDIIIProxy_transport_root_parity_boundary_kkt_headSuperBracket_closure`:
it exports the localized boundary obstruction directly as
`S.boundaryGenerator ≠ 0`.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_transport_root_parity_boundaryGenerator_kkt_headSuperBracket_closure
    [FiniteDimensional ℝ E]
    (n : ℕ)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    (let P := canonicalDIIIProxy (E := E);
      P.T = complex_i (E := E)
        ∧ P.C = modular_j (E := E)
        ∧ P.S = -(spectral_epsilon (E := E))
        ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
        ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
        ∧ P.T.comp P.C = -(spectral_epsilon (E := E))
        ∧ P.C.comp P.T = spectral_epsilon (E := E))
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
      ∧ S.boundaryGenerator ≠ 0
      ∧ InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          (A := A) (B := B) (E := E)
          V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧ X.F =
          InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F
          + InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F
      ∧ InfoGeometry.Canonical.KKTCore.IsGZero X.cl11
          (InfoGeometry.Canonical.KKTCore.commutator
            (InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F)
            (InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F))
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n
          * InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n = 0
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n
          * InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n = 0
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headAnticommutator
          (InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n)
          (InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n) = 1
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headCommutator
          (InfoGeometry.Canonical.SplitCliffordHeadLift.headJTensor n)
          (InfoGeometry.Canonical.SplitCliffordHeadLift.headKTensor n)
          = (2 : ℝ) • InfoGeometry.Canonical.SplitCliffordHeadLift.headEpsTensor n := by
  rcases
      canonicalDIIIProxy_transport_root_parity_boundary_kkt_headSuperBracket_closure
        (A := A) (B := B) (E := E) n V X hX hEven t M P0 S hA hplus hminus hodd
        hBoundaryOnZeroModes hParity hGrade with
    ⟨hProxy, hCARPair, hBoundaryScale, hMismatch, hSplit, hCommZero, hNullMinusSq, hNullPlusSq,
      hCAR, hJK⟩
  have hBoundaryGen : S.boundaryGenerator ≠ 0 :=
    (boundaryScale_ne_zero_iff_boundaryGenerator_ne_zero (S := S)).mp hBoundaryScale
  exact ⟨hProxy, hCARPair,
    hBoundaryGen, hMismatch, hSplit, hCommZero, hNullMinusSq,
    hNullPlusSq, hCAR, hJK⟩

/--
Root-name parity/vorticity/KKT/head-superbracket closure on a transport slice.

This is the vorticity-facing variant of
`canonicalDIIIProxy_transport_root_parity_boundaryGenerator_kkt_headSuperBracket_closure`:
it exports the localized boundary observable directly as
`coriolisVorticity S ≠ 0`.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_transport_root_parity_vorticity_kkt_headSuperBracket_closure
    [FiniteDimensional ℝ E]
    (n : ℕ)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    (let P := canonicalDIIIProxy (E := E);
      P.T = complex_i (E := E)
        ∧ P.C = modular_j (E := E)
        ∧ P.S = -(spectral_epsilon (E := E))
        ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
        ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
        ∧ P.T.comp P.C = -(spectral_epsilon (E := E))
        ∧ P.C.comp P.T = spectral_epsilon (E := E))
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
      ∧ InfoGeometry.Canonical.SpinorModularBridge.coriolisVorticity S ≠ 0
      ∧ InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          (A := A) (B := B) (E := E)
          V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧ X.F =
          InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F
          + InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F
      ∧ InfoGeometry.Canonical.KKTCore.IsGZero X.cl11
          (InfoGeometry.Canonical.KKTCore.commutator
            (InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F)
            (InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F))
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n
          * InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n = 0
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n
          * InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n = 0
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headAnticommutator
          (InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n)
          (InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n) = 1
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headCommutator
          (InfoGeometry.Canonical.SplitCliffordHeadLift.headJTensor n)
          (InfoGeometry.Canonical.SplitCliffordHeadLift.headKTensor n)
          = (2 : ℝ) • InfoGeometry.Canonical.SplitCliffordHeadLift.headEpsTensor n := by
  rcases
      canonicalDIIIProxy_transport_root_parity_boundaryGenerator_kkt_headSuperBracket_closure
        (A := A) (B := B) (E := E) n V X hX hEven t M P0 S hA hplus hminus hodd
        hBoundaryOnZeroModes hParity hGrade with
    ⟨hProxy, hCARPair, hBoundaryGen, hMismatch, hSplit, hCommZero, hNullMinusSq, hNullPlusSq,
      hCAR, hJK⟩
  have hVort : InfoGeometry.Canonical.SpinorModularBridge.coriolisVorticity S ≠ 0 := by
    rw [InfoGeometry.Canonical.SpinorModularBridge.boundaryGenerator_is_vorticity (S := S)]
    exact hBoundaryGen
  exact ⟨hProxy, hCARPair, hVort, hMismatch, hSplit, hCommZero, hNullMinusSq,
    hNullPlusSq, hCAR, hJK⟩

/--
Root-name parity/vortex-witness/KKT/head-superbracket closure on a transport
slice.

This strengthens the vorticity-facing closure by exporting a localized boundary
vortex witness directly:
`∃ v, IsDanglingZeroMode S v ∧ coriolisVorticity S v ≠ 0`.
-/
@[rep_depth transport]
theorem canonicalDIIIProxy_transport_root_parity_vortexWitness_kkt_headSuperBracket_closure
    [FiniteDimensional ℝ E]
    (n : ℕ)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    (let P := canonicalDIIIProxy (E := E);
      P.T = complex_i (E := E)
        ∧ P.C = modular_j (E := E)
        ∧ P.S = -(spectral_epsilon (E := E))
        ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
        ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
        ∧ P.T.comp P.C = -(spectral_epsilon (E := E))
        ∧ P.C.comp P.T = spectral_epsilon (E := E))
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
      ∧ (∃ v : H₂,
            InfoGeometry.Canonical.SpinorModularBridge.IsDanglingZeroMode S v
              ∧ InfoGeometry.Canonical.SpinorModularBridge.coriolisVorticity S v ≠ 0)
      ∧ InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
          (A := A) (B := B) (E := E)
          V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧ X.F =
          InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F
          + InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F
      ∧ InfoGeometry.Canonical.KKTCore.IsGZero X.cl11
          (InfoGeometry.Canonical.KKTCore.commutator
            (InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F)
            (InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F))
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n
          * InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n = 0
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n
          * InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n = 0
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headAnticommutator
          (InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n)
          (InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n) = 1
      ∧ InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headCommutator
          (InfoGeometry.Canonical.SplitCliffordHeadLift.headJTensor n)
          (InfoGeometry.Canonical.SplitCliffordHeadLift.headKTensor n)
          = (2 : ℝ) • InfoGeometry.Canonical.SplitCliffordHeadLift.headEpsTensor n := by
  rcases
      canonicalDIIIProxy_transport_root_parity_vorticity_kkt_headSuperBracket_closure
        (A := A) (B := B) (E := E) n V X hX hEven t M P0 S hA hplus hminus hodd
        hBoundaryOnZeroModes hParity hGrade with
    ⟨hProxy, hCARPair, _, hMismatch, hSplit, hCommZero, hNullMinusSq, hNullPlusSq, hCAR, hJK⟩
  have hWitness :
      ∃ v : H₂,
          InfoGeometry.Canonical.SpinorModularBridge.IsDanglingZeroMode S v
            ∧ InfoGeometry.Canonical.SpinorModularBridge.coriolisVorticity S v ≠ 0 :=
    operatorialCentralChargeParity_ne_zero_exists_localizedBoundaryVortex_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hParity
  exact ⟨hProxy, hCARPair, hWitness, hMismatch, hSplit, hCommZero, hNullMinusSq,
    hNullPlusSq, hCAR, hJK⟩

end Closure

end InfoGeometry.Canonical.RealBdGDIIIAtom
