import InfoGeometry.Canonical.GrassmannianCartanInteroperability
import InfoGeometry.Canonical.KahlerAtiyahCartanForms
import InfoGeometry.Canonical.KahlerAtiyahSpinConnection
import InfoGeometry.Canonical.ZornAssociatorKreinBridge
import InfoGeometry.Canonical.ZornThreeGeneratorObstruction
import InfoGeometry.Canonical.Cl11LeftRightDoubleBridge
import InfoGeometry.Canonical.Cl11BipartiteDiracBridge
import InfoGeometry.Canonical.Cl11BipartiteOrderOneCondition
import InfoGeometry.Canonical.Cl11BipartiteSpectralCurvature
import InfoGeometry.Canonical.Cl11BipartitePolynomialSpectralAction
import InfoGeometry.Canonical.CartanBladePolynomialSpectralAction
import InfoGeometry.Canonical.ChiralBipartiteDiracNetworkBridge
import InfoGeometry.Canonical.NonlinearTwinWaveOpticsBridge
import InfoGeometry.Canonical.ClusterMutationIndexBridge
import InfoGeometry.Canonical.BipartiteCuntzUHFBridge
import InfoGeometry.Canonical.CantorCuntzFractalBridge
import InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge

import InfoGeometry.Categorical.ArtinGarsideCenterBridge
import InfoGeometry.Categorical.UniversalArtinBraidRepresentation
import InfoGeometry.Categorical.BraidPermutationQuotient
import InfoGeometry.Categorical.BraidGroup3S3QuotientBridge
import InfoGeometry.Categorical.MajoranaUniversalB3Bridge
import InfoGeometry.Categorical.FibonacciUniversalB3Bridge

import InfoGeometry.Lie.ZornPeirceDerivationStabilizer
import InfoGeometry.Physics.EightStateTraceRatio

/-!
# PR 185 theorem-bearing consolidation

This file is an import-level consolidation of the theorem-bearing modules
added or extended on PR #185.

It intentionally avoids a vacuous theorem such as `True` as a proxy for
compilation or theory closure.  Instead, the packet below re-exports concrete
closed statements from the imported modules.

Still-open theorem debt includes:
* equality of the braid permutation kernel with the repository pure-braid
  presentation;
* an explicit abstract graded-Clifford equivalence
    Cl(1,1) gradedTensor Cl(1,1) ~= Cl(2,2)
  matched to the native stage-two matrix carrier;
* matrix trace versus Berezin/top-degree exterior readout normalization;
* analytic Seeley--DeWitt / heat-kernel identification;
* a generic Kasteleyn Pfaffian to amplituhedron canonical-form theorem;
* a dynamical Manakov soliton theorem identifying the proposed Kerr/optical
  physical interpretation.

Those are not asserted here.
-/

namespace InfoGeometry.PR185

open InfoGeometry.Categorical
open InfoGeometry.Categorical.BraidPermutationQuotient
open InfoGeometry.Canonical
open InfoGeometry.Canonical.Cl11BipartiteDiracBridge
open InfoGeometry.Canonical.Cl11BipartiteOrderOneCondition
open InfoGeometry.Canonical.Cl11BipartiteSpectralCurvature
open InfoGeometry.Canonical.Cl11BipartitePolynomialSpectralAction
open InfoGeometry.Canonical.ChiralBipartiteDiracNetworkBridge
open InfoGeometry.Canonical.NonlinearTwinWaveOpticsBridge

/-- Concrete finite braid-permutation quotient packet. -/
theorem braid_permutation_packet (m : ℕ) :
    Function.Surjective (braidToPerm m) ∧
      Subgroup.normalClosure (generatorSquares m) ≤
        (braidToPerm m).ker := by
  exact ⟨braidToPerm_surjective m,
    normalClosure_generatorSquares_le_kernel m⟩

/-- Every conjugate of a standard generator square is in the intrinsic pure
braid kernel. -/
theorem pure_conjugate_square_packet
    (m : ℕ) (w : Braid.braid_group (m + 1)) (i : Fin m) :
    w * (Braid.σ' m i) ^ 2 * w⁻¹ ∈ pureBraidSubgroup m :=
  conjugate_generatorSquare_mem_pureBraidSubgroup m w i

/-- Finite left/right order-zero and order-one packet for the bipartite
Cl(1,1) matrix system. -/
theorem bipartite_order_one_packet
    (DL a : Cl11BipartiteOrderOneCondition.StageOne)
    (betaR DR b : Cl11BipartiteOrderOneCondition.Atom)
    (heven : betaR * b = b * betaR) :
    commutator (embedLeft a) (embedRight b) = 0 ∧
    commutator
        (commutator (compositeDirac DL betaR DR) (embedLeft a))
        (embedRight b) = 0 ∧
    commutator
        (commutator (compositeDirac DL betaR DR) (embedRight b))
        (embedLeft a) = 0 :=
  bipartite_order_packet DL a betaR DR b heven

/-- Covariant Dirac-square trace invariance packet. -/
theorem quadratic_spectral_trace_packet
    (u : Units Cl11BipartiteSpectralCurvature.StageOne)
    (D A : Cl11BipartiteSpectralCurvature.StageOne) :
    covariantSquare D (gaugeTransform u D A) =
        unitConjugate u (covariantSquare D A) ∧
      Matrix.trace (covariantSquare D (gaugeTransform u D A)) =
        Matrix.trace (covariantSquare D A) := by
  exact ⟨covariantSquare_gauge_covariant u D A,
    trace_covariantSquare_gauge_invariant u D A⟩

/-- Exact finite polynomial tensor-sum spectral trace decomposition. -/
theorem polynomial_tensor_sum_packet
    (c0 c1 c2 : ℝ)
    (DeltaL : Cl11BipartitePolynomialSpectralAction.StageOne)
    (DeltaR : Cl11BipartitePolynomialSpectralAction.Atom) :
    polynomialSpectralAction c0 c1 c2 (tensorSum DeltaL DeltaR) =
      4 * c0 +
      2 * c1 * (Matrix.trace DeltaL + Matrix.trace DeltaR) +
      2 * c2 *
        (Matrix.trace (DeltaL * DeltaL) +
          Matrix.trace DeltaL * Matrix.trace DeltaR +
          Matrix.trace (DeltaR * DeltaR)) :=
  polynomialSpectralAction_tensorSum c0 c1 c2 DeltaL DeltaR

/-- Exact finite graph Dirac-Hodge packet. -/
theorem graph_dirac_packet
    {v e : Type*}
    [Fintype v] [Fintype e] [DecidableEq v] [DecidableEq e]
    (B : Matrix e v ℝ) :
    Dplus B * Dplus B = 0 ∧
      Dminus B * Dminus B = 0 ∧
      Dnet B * Dnet B = networkLaplacian B := by
  exact ⟨Dplus_sq_zero B,
    Dminus_sq_zero B,
    Dnet_sq_eq_networkLaplacian B⟩

/-- Exact finite twin-wave symmetry/frequency packet. -/
theorem twin_wave_packet
    (gSelf gCross omega : ℝ)
    (s : TwinDensity) :
    crossPhaseEnergy gCross (sheetSwap s) =
        crossPhaseEnergy gCross s ∧
      coupledDensityEnergy gSelf gCross (sheetSwap s) =
        coupledDensityEnergy gSelf gCross s ∧
      omega - (-omega) = 2 * omega :=
  nonlinear_twin_wave_packet gSelf gCross omega s

/-- Exact finite eight-state trace ratio retained as a pure representation
trace identity. -/
theorem eight_state_ratio_packet :
    InfoGeometry.Physics.EightStateTraceRatio.traceT3Sq /
        InfoGeometry.Physics.EightStateTraceRatio.traceQSq =
      (3 : ℚ) / 8 :=
  InfoGeometry.Physics.EightStateTraceRatio.trace_ratio_eq_three_eighths

/-- Exact plabic count identity and cluster-move invariance packet. -/
theorem cluster_count_index_packet
    (s : InfoGeometry.Canonical.ClusterMutationIndexBridge.PlabicCounts) :
    s.helicityDefect = s.colorIndex ∧
    (s.squareMove).colorIndex = s.colorIndex ∧
    (s.bubbleReduction).colorIndex = s.colorIndex := by
  exact ⟨
    InfoGeometry.Canonical.ClusterMutationIndexBridge.PlabicCounts.helicityDefect_eq_colorIndex s,
    InfoGeometry.Canonical.ClusterMutationIndexBridge.PlabicCounts.squareMove_colorIndex s,
    InfoGeometry.Canonical.ClusterMutationIndexBridge.PlabicCounts.bubbleReduction_colorIndex s
  ⟩

/-- Native Cuntz/UHF interoperability packet: left/right commutation and
normalized trace preservation along finite matrix-tower transitions. -/
theorem cuntz_uhf_packet
    {n : ℕ}
    (a b x : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg n)
    {i j : ℕ} (hij : i ≤ j)
    (A : InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.MatrixStage i) :
    InfoGeometry.Algebra.CuntzLeftRightCommutant.leftMultiplication n a
        (InfoGeometry.Algebra.CuntzLeftRightCommutant.rightMultiplication n b x) =
      InfoGeometry.Algebra.CuntzLeftRightCommutant.rightMultiplication n b
        (InfoGeometry.Algebra.CuntzLeftRightCommutant.leftMultiplication n a x) ∧
    InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.matrixTraceState j
        (InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteMap hij A) =
      InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.matrixTraceState i A := by
  exact ⟨
    InfoGeometry.Canonical.BipartiteCuntzUHFBridge.cuntz_left_right_commute a b x,
    InfoGeometry.Canonical.BipartiteCuntzUHFBridge.normalized_trace_transition hij A
  ⟩

/-- Native Cantor/Cuntz packet: binary cylinder refinement and dyadic KMS weight. -/
theorem cantor_cuntz_packet
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (w : List Bool) (beta : ℝ)
    (hEq : 2 * Real.exp (-beta * 1) = 1) :
    InfoGeometry.Canonical.CantorCuntzFractalBridge.cylinderProjection C (w ++ [false]) +
        InfoGeometry.Canonical.CantorCuntzFractalBridge.cylinderProjection C (w ++ [true]) =
      InfoGeometry.Canonical.CantorCuntzFractalBridge.cylinderProjection C w ∧
    beta = Real.log 2 := by
  exact ⟨
    InfoGeometry.Canonical.CantorCuntzFractalBridge.cylinder_children_sum C w,
    InfoGeometry.Canonical.CantorCuntzFractalBridge.kms_beta_eq_log_two beta hEq
  ⟩

/-- G2 CK architecture packet: scalar-separated noncommutative realization
and degree-three adjacency eigenvector. -/
theorem g2_ck_scalar_separation_packet
    (G : InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.G2TransitionDatum)
    (i : InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.G2Vertex) :
    (G.adjacency (R := ℤ)).mulVec (fun _ => (1 : ℤ)) i = 3 ∧
    G.theta (G.theta i) = i := by
  exact ⟨
    InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.G2TransitionDatum.adjacency_mulVec_one_eq_three G i,
    InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.G2TransitionDatum.theta_sq G i
  ⟩

/-- Concrete G2 double-star CK packet. -/
theorem g2_concrete_ck_packet
    (i : InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.G2Vertex) :
    (InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.A_G2_int.mulVec
      (fun _ => (1 : ℤ))) i = 3 ∧
    InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.garsideTheta
      (InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.garsideTheta i) = i ∧
    InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.G2BoundaryMatrix.det = -1456 := by
  exact ⟨
    InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.G2TransitionDatum.adjacency_mulVec_one_eq_three
      InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.concreteG2TransitionDatum i,
    InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.garsideTheta_involutive i,
    InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge.G2BoundaryMatrix_det
  ⟩

end InfoGeometry.PR185
