/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralSkewIncidence
import InfoGeometry.Canonical.FinitePlabicKasteleyn
import Mathlib.Algebra.Ring.Parity

/-!
# Neutral incidence pairings on supplied finite bipartite graphs

The graph and Kasteleyn signing are inputs. Edge weights are the actual neutral
pairings of opposite incidence states, and feed the native edge-sum matrix and
block Dirac operator. Operator addition adds these weights. The real mirror
negates the Dirac operator and preserves its square; a product of edge weights
acquires the sign determined by the number of edges. No planar embedding or
physical CPT operation is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.DiracBipartitePairing

open scoped BigOperators
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralSkewIncidence
open InfoGeometry.Twistor.RealTwistorIncidence
open InfoGeometry.Canonical.FinitePlabicKasteleyn

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {G : FinitePlabicGraph}

/-- An edge is weighted by the neutral pairing of its white positive-graph
state and black negative-graph state, in that order. -/
def diracPairingWeight (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E)
    (e : G.Edge) : ℝ :=
  canonicalNeutralBilin
    (incidenceMap P (white (G.whiteEndpoint e)))
    (incidenceMap (-P) (black (G.blackEndpoint e)))

/-- Evaluation-skewness turns the cross-pairing into twice evaluation. -/
theorem diracPairingWeight_of_skew (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (hP : ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ))
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E)
    (e : G.Edge) :
    diracPairingWeight P white black e =
      2 * black (G.blackEndpoint e) (P (white (G.whiteEndpoint e))) :=
  incidence_cross_pairing P hP _ _

/-- Addition of operators adds the actual edge pairings, without a skewness
assumption. This is parallel addition of couplings on the same supplied graph. -/
theorem diracPairingWeight_add (P Q : Module.Dual ℝ E →ₗ[ℝ] E)
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E)
    (e : G.Edge) :
    diracPairingWeight (P + Q) white black e =
      diracPairingWeight P white black e + diracPairingWeight Q white black e := by
  simp only [diracPairingWeight, canonicalNeutralBilin_apply, incidenceMap_apply,
    LinearMap.add_apply, LinearMap.neg_apply, map_add, map_neg]
  ring

/-- Swapping both graph signs negates every edge pairing. -/
@[simp] theorem diracPairingWeight_neg (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E)
    (e : G.Edge) :
    diracPairingWeight (-P) white black e = -diracPairingWeight P white black e := by
  simp only [diracPairingWeight, canonicalNeutralBilin_apply, incidenceMap_apply,
    LinearMap.neg_apply, map_neg]
  ring

/-- The sign swap of the edge weight is induced by the native real mirror
on both endpoint states. -/
theorem diracPairingWeight_mirror (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E)
    (e : G.Edge) :
    canonicalNeutralBilin
        (diracMirror (incidenceMap P (white (G.whiteEndpoint e))))
        (diracMirror (incidenceMap (-P) (black (G.blackEndpoint e)))) =
      diracPairingWeight (-P) white black e := by
  rw [diracMirror_anti_isometry, diracPairingWeight_neg]
  rfl

/-- The native signed edge-sum matrix respects operator addition. -/
theorem pairing_edgeSumMatrix_add (S : KasteleynSigning G)
    (P Q : Module.Dual ℝ E →ₗ[ℝ] E)
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E) :
    edgeSumMatrix S (diracPairingWeight (P + Q) white black) =
      edgeSumMatrix S (diracPairingWeight P white black) +
        edgeSumMatrix S (diracPairingWeight Q white black) := by
  have hweights : diracPairingWeight (P + Q) white black =
      fun e => diracPairingWeight P white black e +
        diracPairingWeight Q white black e := by
    funext e
    exact diracPairingWeight_add P Q white black e
  rw [hweights, edgeSumMatrix_add]

/-- The native signed edge-sum matrix is odd under the mirror sign swap. -/
theorem pairing_edgeSumMatrix_neg (S : KasteleynSigning G)
    (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E) :
    edgeSumMatrix S (diracPairingWeight (-P) white black) =
      -edgeSumMatrix S (diracPairingWeight P white black) := by
  have hweights : diracPairingWeight (-P) white black =
      fun e => (-1 : ℝ) * diracPairingWeight P white black e := by
    funext e
    simp
  rw [hweights, edgeSumMatrix_smul]
  exact neg_one_smul ℝ _

/-- The real block Dirac operator itself changes sign. -/
theorem pairing_edgeSumDirac_neg (S : KasteleynSigning G)
    (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E) :
    edgeSumDirac S (diracPairingWeight (-P) white black) =
      -edgeSumDirac S (diracPairingWeight P white black) := by
  have hweights : diracPairingWeight (-P) white black =
      fun e => (-1 : ℝ) * diracPairingWeight P white black e := by
    funext e
    simp
  rw [hweights, edgeSumDirac_smul S (-1 : ℝ) (by simp)]
  exact neg_one_smul ℝ _

/-- The square of the native block Dirac operator is mirror invariant. -/
theorem pairing_edgeSumDirac_sq_neg (S : KasteleynSigning G)
    (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E) :
    edgeSumDirac S (diracPairingWeight (-P) white black) *
        edgeSumDirac S (diracPairingWeight (-P) white black) =
      edgeSumDirac S (diracPairingWeight P white black) *
        edgeSumDirac S (diracPairingWeight P white black) := by
  simp only [pairing_edgeSumDirac_neg, neg_mul_neg]

/-- A product of all edge pairings carries the exact edge-count parity sign. -/
theorem pairing_edgeProduct_neg (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E) :
    (∏ e : G.Edge, diracPairingWeight (-P) white black e) =
      (-1 : ℝ) ^ Fintype.card G.Edge *
        ∏ e : G.Edge, diracPairingWeight P white black e := by
  calc
    (∏ e : G.Edge, diracPairingWeight (-P) white black e) =
        ∏ e : G.Edge, (-1 : ℝ) * diracPairingWeight P white black e := by
      apply Finset.prod_congr rfl
      intro e _
      simp
    _ = (∏ _e : G.Edge, (-1 : ℝ)) *
        ∏ e : G.Edge, diracPairingWeight P white black e := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by simp

/-- Even edge count is a sufficient condition for invariance of the product.
No parity condition is needed for invariance of the Dirac square above. -/
theorem pairing_edgeProduct_neg_of_even (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (white : G.White → Module.Dual ℝ E) (black : G.Black → Module.Dual ℝ E)
    (hEven : Even (Fintype.card G.Edge)) :
    (∏ e : G.Edge, diracPairingWeight (-P) white black e) =
      ∏ e : G.Edge, diracPairingWeight P white black e := by
  rw [pairing_edgeProduct_neg, hEven.neg_one_pow, one_mul]

end InfoGeometry.Canonical.DiracBipartitePairing
