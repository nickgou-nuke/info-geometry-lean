import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Core.GrandCanonical
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Topology.CantorDiracOperator

/-!
# InfoGeometry.Topology.CantorDiracGrandCanonical

Finite grand-canonical ensemble attached to the Cantor Dirac thermal scale.

This file keeps the Gibbs Hamiltonian on the even thermal side of the Cantor
Dirac story.  The odd Dirac operator is not used as the Gibbs Hamiltonian.
Instead, the finite binary-cylinder occupancy model is equipped with an even
thermal energy readout derived from the Cantor Dirac scale.

Theorems here are the finite grand-canonical wrappers:

* partition positivity;
* Gibbs normalization;
* `β` and `μ` derivative readbacks for the log-partition potential;
* Hessian / response readbacks;
* mixed-response symmetry.

No infinite limit, no analytic continuation, and no RH claim is made.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Topology.CantorDiracGrandCanonical

open InfoGeometry.Topology.CantorDiracOperator

/-! ## 1. Finite Cantor occupancy carrier -/

/-- Binary words at a finite Cantor level. -/
abbrev CantorState (n : ℕ) :=
  InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n

instance (n : ℕ) : Fintype (CantorState n) := by
  dsimp [CantorState]
  infer_instance

instance (n : ℕ) : Nonempty (CantorState n) := by
  dsimp [CantorState]
  infer_instance

/-- Occupation number of a finite Cantor binary word. -/
@[rep_depth thermo]
def occupancy {n : ℕ} (w : CantorState n) : ℝ :=
  ∑ i : Fin n, if w i then 1 else 0

/-! ## 2. Finite Cantor grand-canonical packet -/

/--
Finite grand-canonical packet on the Cantor cylinder carrier.

`scale` is the even thermal Hamiltonian scale induced by the Cantor Dirac
block at the chosen cutoff.  The energy observable is the scaled occupancy.
-/
@[rep_depth thermo]
structure CantorGrandCanonicalPacket where
  cutoff : ℕ
  scale : CantorDiracScale

namespace CantorGrandCanonicalPacket

/-- Finite Cantor state carrier for the packet. -/
@[rep_depth thermo]
abbrev State (B : CantorGrandCanonicalPacket) := CantorState B.cutoff

/-- The two-parameter grand-canonical data associated to the Cantor packet. -/
@[rep_depth thermo]
def params (B : CantorGrandCanonicalPacket) :
    InfoGeometry.GrandCanonical.GrandCanonicalTwoParam (State B) where
  energy := fun w => B.scale B.cutoff * occupancy w
  number := occupancy

/-- Canonical `β, μ` partition function. -/
@[rep_depth thermo]
def partition (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.partitionGC (params B) β μ

/-- Log-partition potential. -/
@[rep_depth thermo]
def potential (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.potentialGC (params B) β μ

/-- Gibbs weight of a Cantor state. -/
@[rep_depth thermo]
def gibbsWeight (B : CantorGrandCanonicalPacket) (β μ : ℝ) (w : State B) : ℝ :=
  InfoGeometry.GrandCanonical.gibbsWeightGC (params B) β μ w

/-- Mean shifted observable `E - μN`. -/
@[rep_depth thermo]
def meanShift (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.meanShift (params B) β μ

/-- Mean particle number. -/
@[rep_depth thermo]
def meanNumber (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.meanNumber (params B) β μ

/-- First `β`-response of the potential. -/
@[rep_depth thermo]
def betaResponse (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaResponse (params B) β μ

/-- First `μ`-response of the potential. -/
@[rep_depth thermo]
def muResponse (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muResponse (params B) β μ

/-- Second `β`-derivative of the potential. -/
@[rep_depth thermo]
def betaHessian (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaHessian (params B) β μ

/-- Second `μ`-derivative of the potential. -/
@[rep_depth thermo]
def muHessian (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muHessian (params B) β μ

/-- Mixed derivative `∂_μ ∂_β`. -/
@[rep_depth thermo]
def betaMuHessian (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaMuHessian (params B) β μ

/-- Mixed derivative `∂_β ∂_μ`. -/
@[rep_depth thermo]
def muBetaHessian (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muBetaHessian (params B) β μ

/-- Thermodynamic response matrix. -/
@[rep_depth thermo]
def responseMatrix (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    InfoGeometry.GrandCanonical.ResponseMatrix2 :=
  InfoGeometry.GrandCanonical.responseMatrix (params B) β μ

/-- Spinodal condition in the Cantor grand-canonical packet. -/
@[rep_depth thermo]
def spinodal2D (B : CantorGrandCanonicalPacket) (β μ : ℝ) : Prop :=
  InfoGeometry.GrandCanonical.Spinodal2D (params B) β μ

end CantorGrandCanonicalPacket

end InfoGeometry.Topology.CantorDiracGrandCanonical
