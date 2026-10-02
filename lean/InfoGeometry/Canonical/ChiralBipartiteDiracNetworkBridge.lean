import Mathlib.Tactic

import InfoGeometry.Streaming.BipartiteGraphDirac
import InfoGeometry.Canonical.DiscreteDiracHodgeChiral
import InfoGeometry.Physics.CPTGlobalPinKleinDescent
import InfoGeometry.Projective.PenroseDAGAmplituhedronRosetta

/-!
# Chiral bipartite Dirac-network interoperability

This module exposes the repository's existing finite graph Dirac-Hodge owner
in the chiral two-step language

  D_+ = d,
  D_- = δ,
  D_net = D_+ + D_-.

No parallel graph algebra is introduced.

Closed here:
* D_+^2 = 0 and D_-^2 = 0;
* D_net^2 = {D_+,D_-};
* explicit Laplacian blocks B^T B and B B^T;
* oddness with respect to the existing vertex/edge grading;
* the existing Klein two-cycle holonomy readout is exposed separately;
* Penrose/amplituhedron comparison remains explicit Rosetta-carrier data.

No theorem identifies a generic Penrose spin network with a plabic graph,
identifies a Kasteleyn Pfaffian with an amplituhedron canonical form, or
upgrades the finite two-cycle sign law to a general Pin^- spin-structure
classification.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralBipartiteDiracNetworkBridge

open InfoGeometry.Streaming.BipartiteGraphDirac
open InfoGeometry.Canonical.DiscreteDiracHodgeChiral
open InfoGeometry.Projective.PenroseDAGAmplituhedronRosetta

variable {v e : Type*}
variable [Fintype v] [Fintype e] [DecidableEq v] [DecidableEq e]

abbrev Cochain := InfoGeometry.Streaming.BipartiteGraphDirac.Cochain v e
abbrev EndCochain := Module.End ℝ Cochain

/-- Chiral raising step, using the repository-owned graph differential. -/
def Dplus (B : Matrix e v ℝ) : EndCochain :=
  differential B

/-- Chiral lowering step, using the repository-owned graph codifferential. -/
def Dminus (B : Matrix e v ℝ) : EndCochain :=
  codifferential B

/-- Total network Dirac-Hodge operator. -/
def Dnet (B : Matrix e v ℝ) : EndCochain :=
  Dplus B + Dminus B

/-- Cross-sheet anticommutator / Hodge Laplacian. -/
def networkLaplacian (B : Matrix e v ℝ) : EndCochain :=
  Dplus B * Dminus B + Dminus B * Dplus B

@[simp] theorem Dplus_sq_zero (B : Matrix e v ℝ) :
    Dplus B * Dplus B = 0 := by
  exact differential_sq B

@[simp] theorem Dminus_sq_zero (B : Matrix e v ℝ) :
    Dminus B * Dminus B = 0 := by
  exact codifferential_sq B

theorem Dnet_eq_graphDirac (B : Matrix e v ℝ) :
    Dnet B = graphDirac B := by
  rfl

/-- The network square is exactly the chiral anticommutator. -/
theorem Dnet_sq_eq_networkLaplacian (B : Matrix e v ℝ) :
    Dnet B * Dnet B = networkLaplacian B := by
  simpa [Dnet, networkLaplacian, Dplus, Dminus] using
    (graphDirac_sq B)

/-- Pointwise form of the two Laplacian blocks B^T B and B B^T. -/
theorem Dnet_square_blocks
    (B : Matrix e v ℝ) (x : Cochain) :
    (Dnet B * Dnet B) x =
      (B.transpose.mulVec (B.mulVec x.1),
        B.mulVec (B.transpose.mulVec x.2)) := by
  rw [Dnet_eq_graphDirac]
  exact graphDirac_square_blocks B x

/-- The total network Dirac is odd for the existing cochain grading. -/
theorem Dnet_odd (B : Matrix e v ℝ) :
    Dnet B * grading = -(grading * Dnet B) := by
  rw [Dnet_eq_graphDirac]
  exact graphDirac_odd B

/-- The network Laplacian is grading-even. -/
theorem networkLaplacian_even (B : Matrix e v ℝ) :
    networkLaplacian B * grading = grading * networkLaplacian B := by
  have hodd : Dnet B * grading = -(grading * Dnet B) :=
    Dnet_odd B
  have hsq : Dnet B * Dnet B = networkLaplacian B :=
    Dnet_sq_eq_networkLaplacian B
  calc
    networkLaplacian B * grading
        = (Dnet B * Dnet B) * grading := by rw [hsq]
    _ = grading * (Dnet B * Dnet B) := by
      exact square_commutes_chirality_of_anticommutes (Dnet B) grading hodd
    _ = grading * networkLaplacian B := by rw [hsq]

/-! ## Exact finite two-cycle readouts -/

/-- Scalar sign model: one orientation-reversing traversal contributes -1. -/
def singleTraversalSign : ℝ := -1

/-- Two such sign traversals restore +1.  This is only the scalar sign law. -/
theorem doubleTraversalSign_eq_one :
    singleTraversalSign * singleTraversalSign = 1 := by
  norm_num [singleTraversalSign]

/-- Existing repository matrix-level Klein two-cycle holonomy. -/
theorem klein_two_cycle_matrix_holonomy :
    InfoGeometry.Topology.BraidMatrix *
        InfoGeometry.Topology.TwistedBraidMatrix = 1 :=
  InfoGeometry.Physics.CPTGlobalPinKleinDescent.classical_klein_two_cycle_holonomy

/-! ## Rosetta boundary: comparison data, not asserted equivalence -/

/-- Any supplied Rosetta carrier gives an explicit equivalence from the
Penrose-net lane to the amplituhedron lane.  The geometry of that equivalence
is data, not inferred from the graph-Dirac theorems above. -/
def penroseToAmplituhedronEquiv
    (R : RosettaCarrier) :
    R.Carrier RosettaLane.penroseNet ≃
      R.Carrier RosettaLane.amplituhedron :=
  R.laneEquiv RosettaLane.penroseNet RosettaLane.amplituhedron

@[simp] theorem penroseToAmplituhedron_sameInCommon
    (R : RosettaCarrier)
    (x : R.Carrier RosettaLane.penroseNet) :
    R.SameInCommon x (penroseToAmplituhedronEquiv R x) := by
  exact R.laneEquiv_sameInCommon
    RosettaLane.penroseNet RosettaLane.amplituhedron x

end InfoGeometry.Canonical.ChiralBipartiteDiracNetworkBridge
