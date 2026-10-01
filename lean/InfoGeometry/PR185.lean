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

end InfoGeometry.PR185
