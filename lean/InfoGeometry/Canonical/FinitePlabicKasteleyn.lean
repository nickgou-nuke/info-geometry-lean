import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.PlabicDiracKrein

/-!
# Finite bipartite plabic data and Kasteleyn edge sums

`FinitePlabicGraph` stores finite black and white vertex types, finite edge
identities with their endpoints, and supplied cyclic face-boundary edge lists.
Edge identities are separate from endpoint pairs, so parallel edges are
allowed. The face lists are combinatorial input; this definition does not
claim or construct a planar embedding.

`KasteleynSigning` is an integer sign on edges whose product around each
supplied even face boundary is `(-1)^(length / 2 + 1)`. `edgeSumMatrix`
forms the weighted signed sum of all edges between each black/white pair.
-/

noncomputable section

namespace InfoGeometry.Canonical.FinitePlabicKasteleyn

open scoped BigOperators

/-- Finite bipartite graph data with explicit even face-boundary edge lists.
The edge type records edge identities, rather than only endpoint pairs. -/
structure FinitePlabicGraph where
  Black : Type
  White : Type
  Edge : Type
  Face : Type
  [blackFintype : Fintype Black]
  [whiteFintype : Fintype White]
  [edgeFintype : Fintype Edge]
  [faceFintype : Fintype Face]
  [blackDecidableEq : DecidableEq Black]
  [whiteDecidableEq : DecidableEq White]
  [edgeDecidableEq : DecidableEq Edge]
  [faceDecidableEq : DecidableEq Face]
  blackEndpoint : Edge → Black
  whiteEndpoint : Edge → White
  faceBoundary : Face → List Edge
  faceBoundary_even : ∀ f, Even (faceBoundary f).length

attribute [instance] FinitePlabicGraph.blackFintype FinitePlabicGraph.whiteFintype
  FinitePlabicGraph.edgeFintype FinitePlabicGraph.faceFintype
  FinitePlabicGraph.blackDecidableEq FinitePlabicGraph.whiteDecidableEq
  FinitePlabicGraph.edgeDecidableEq FinitePlabicGraph.faceDecidableEq

variable (G : FinitePlabicGraph)

/-- A Kasteleyn signing for the explicit face-boundary data of `G`. -/
structure KasteleynSigning where
  sign : G.Edge → ℤ
  sign_sq : ∀ e, sign e * sign e = 1
  face_product : ∀ f,
    ((G.faceBoundary f).map sign).prod =
      (-1 : ℤ) ^ ((G.faceBoundary f).length / 2 + 1)

variable {G}

/-- The signed, weighted sum over all edge identities joining `b` to `w`.
Rows are white vertices and columns are black vertices, matching the existing
`PlabicDiracKrein.diracDHK` convention. -/
def edgeSumMatrix {R : Type*} [CommRing R] (S : KasteleynSigning G)
    (weight : G.Edge → R) : Matrix G.White G.Black R :=
  fun w b => ∑ e : G.Edge,
    if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w
    then (S.sign e : R) * weight e else 0

@[simp] theorem edgeSumMatrix_apply {R : Type*} [CommRing R]
    (S : KasteleynSigning G) (weight : G.Edge → R) (w : G.White) (b : G.Black) :
    edgeSumMatrix S weight w b = ∑ e : G.Edge,
      if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w
      then (S.sign e : R) * weight e else 0 := rfl

/-- Signed edge sums are additive in the edge weights. -/
theorem edgeSumMatrix_add {R : Type*} [CommRing R]
    (S : KasteleynSigning G) (weight₁ weight₂ : G.Edge → R) :
    edgeSumMatrix S (fun e => weight₁ e + weight₂ e) =
      edgeSumMatrix S weight₁ + edgeSumMatrix S weight₂ := by
  classical
  ext w b
  simp only [edgeSumMatrix, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp [mul_add]

/-- If no edge has the selected endpoints, the corresponding matrix entry is
zero. -/
theorem edgeSumMatrix_eq_zero_of_no_edge {R : Type*} [CommRing R]
    (S : KasteleynSigning G) (weight : G.Edge → R)
    (w : G.White) (b : G.Black)
    (h : ∀ e, G.blackEndpoint e ≠ b ∨ G.whiteEndpoint e ≠ w) :
    edgeSumMatrix S weight w b = 0 := by
  classical
  simp only [edgeSumMatrix]
  apply Finset.sum_eq_zero
  intro e he
  have hn : ¬ (G.blackEndpoint e = b ∧ G.whiteEndpoint e = w) := by
    intro hp
    rcases h e with hb | hw
    · exact hb hp.1
    · exact hw hp.2
  simp [hn]

/-- The edge-sum matrix can be used directly as the coupling matrix of the
repository's bipartite block Dirac operator. -/
abbrev edgeSumDirac {R : Type*} [CommRing R] [StarRing R]
    (S : KasteleynSigning G) (weight : G.Edge → R) :
    Matrix (G.Black ⊕ G.White) (G.Black ⊕ G.White) R :=
  InfoGeometry.Canonical.PlabicDiracKrein.diracDHK (edgeSumMatrix S weight)

/-- The block square of the Kasteleyn-coupled Dirac operator is the pair of
Gram matrices of the weighted edge-sum matrix. -/
theorem edgeSumDirac_sq {R : Type*} [CommRing R] [StarRing R]
    (S : KasteleynSigning G) (weight : G.Edge → R) :
    edgeSumDirac S weight * edgeSumDirac S weight =
      Matrix.fromBlocks
        ((edgeSumMatrix S weight).conjTranspose * (edgeSumMatrix S weight)) 0 0
        ((edgeSumMatrix S weight) * (edgeSumMatrix S weight).conjTranspose) :=
  InfoGeometry.Canonical.PlabicDiracKrein.diracDHK_sq (edgeSumMatrix S weight)

end InfoGeometry.Canonical.FinitePlabicKasteleyn
