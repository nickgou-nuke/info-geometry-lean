/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.FinitePlabicKasteleyn
import InfoGeometry.Holography.PlabicKreinTwistedClusterMutation
import InfoGeometry.Topology.DirectedPathMonoidTransport

/-!
# Matrix representation of the local `Cl11Op` carrier

The local `Cl11Op` carrier is an explicit four-coordinate algebra. This file
gives its `2 × 2` matrix representation and proves algebra compatibility and
path-product transport. Its finite Plabic incidence subdivision is a
combinatorial construction from existing graph data; it does not construct a
planar embedding. The characteristic-polynomial result concerns conjugation
by the explicit `edgeTransport` and does not identify it with a square move.
-/

namespace InfoGeometry.Holography.PlabicKrein

open InfoGeometry.Topology

namespace Cl11Op

variable {R : Type*} [CommRing R]

@[simp] theorem one_mul (A : Cl11Op R) : mul one A = A := by
  ext <;> simp [mul, one]

@[simp] theorem mul_one (A : Cl11Op R) : mul A one = A := by
  ext <;> simp [mul, one]

instance : Monoid (Cl11Op R) where
  one := one
  mul := mul
  one_mul := one_mul
  mul_one := mul_one
  mul_assoc := by
    intro A B C
    change Cl11Op.mul (Cl11Op.mul A B) C = Cl11Op.mul A (Cl11Op.mul B C)
    ext <;> simp [Cl11Op.mul] <;> ring

/-- The canonical matrix representation of a local `Cl11Op`. -/
def toMatrix (A : Cl11Op R) : Matrix (Fin 2) (Fin 2) R :=
  !![A.m11, A.m12; A.m21, A.m22]

/-- Coordinate inverse for the matrix representation. -/
def ofMatrix (M : Matrix (Fin 2) (Fin 2) R) : Cl11Op R :=
  ⟨M 0 0, M 0 1, M 1 0, M 1 1⟩

omit [CommRing R] in
theorem toMatrix_injective :
    Function.Injective (toMatrix : Cl11Op R → Matrix (Fin 2) (Fin 2) R) := by
  intro A B h
  apply Cl11Op.ext
  · simpa [toMatrix] using congrFun (congrFun h 0) 0
  · simpa [toMatrix] using congrFun (congrFun h 0) 1
  · simpa [toMatrix] using congrFun (congrFun h 1) 0
  · simpa [toMatrix] using congrFun (congrFun h 1) 1

omit [CommRing R] in
theorem ofMatrix_toMatrix (A : Cl11Op R) : ofMatrix (toMatrix A) = A := by
  ext <;> rfl

omit [CommRing R] in
theorem toMatrix_ofMatrix (M : Matrix (Fin 2) (Fin 2) R) :
    toMatrix (ofMatrix M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The local `Cl11Op` carrier and its `2 × 2` matrix carrier are equivalent. -/
def toMatrixEquiv : Cl11Op R ≃ Matrix (Fin 2) (Fin 2) R where
  toFun := toMatrix
  invFun := ofMatrix
  left_inv := ofMatrix_toMatrix
  right_inv := toMatrix_ofMatrix

theorem toMatrix_zero : toMatrix (zero : Cl11Op R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMatrix_one : toMatrix (one : Cl11Op R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, one]

/-- Matrix representatives of the black projector and upper nilpotent edge. -/
def matrixBlack : Matrix (Fin 2) (Fin 2) R :=
  toMatrix (nodeBlack (1 : R))

def matrixEdge : Matrix (Fin 2) (Fin 2) R :=
  toMatrix (edgeTwist (1 : R))

/-- The matrix realization exposes explicit noncommutativity over a
nontrivial coefficient ring. -/
theorem matrixBlack_mul_edge_ne [Nontrivial R] :
    matrixBlack (R := R) * matrixEdge (R := R) ≠
      matrixEdge (R := R) * matrixBlack (R := R) := by
  intro h
  have hentry := congrFun (congrFun h 0) 1
  simp [matrixBlack, matrixEdge, toMatrix, nodeBlack, edgeTwist,
    Matrix.mul_apply, Fin.sum_univ_two] at hentry

theorem toMatrix_add (A B : Cl11Op R) :
    toMatrix (add A B) = toMatrix A + toMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMatrix_mul (A B : Cl11Op R) :
    toMatrix (mul A B) = toMatrix A * toMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem toMatrixEquiv_map_mul (A B : Cl11Op R) :
    toMatrixEquiv (mul A B) = toMatrixEquiv A * toMatrixEquiv B :=
  toMatrix_mul A B

/-- Conjugation by the local `edgeTransport` preserves the characteristic
polynomial of every represented operator. The proof uses its actual
two-sided inverse in the finite matrix representation; it does not assert
that a general plabic square move is implemented by this conjugation. -/
theorem matrix_edgeTransport_charpoly_invariant (w : R) (A : Cl11Op R) :
    Matrix.charpoly
        (toMatrix (mul (mul (edgeTransport w) A) (edgeTransportInv w))) =
      Matrix.charpoly (toMatrix A) := by
  rw [toMatrix_mul, toMatrix_mul]
  let T := toMatrix (edgeTransport w)
  let B := toMatrix A
  let Tinv := toMatrix (edgeTransportInv w)
  have hTinv : Tinv * T = 1 := by
    change toMatrix (edgeTransportInv w) * toMatrix (edgeTransport w) = 1
    rw [← toMatrix_mul]
    rw [edgeTransportInv_mul, toMatrix_one]
  change Matrix.charpoly ((T * B) * Tinv) = Matrix.charpoly B
  calc
    Matrix.charpoly ((T * B) * Tinv) =
        Matrix.charpoly (T * (B * Tinv)) := by rw [Matrix.mul_assoc]
    _ = Matrix.charpoly ((B * Tinv) * T) :=
      Matrix.charpoly_mul_comm T (B * Tinv)
    _ = Matrix.charpoly B := by
      rw [Matrix.mul_assoc, hTinv, Matrix.mul_one]

theorem toMatrix_pathProduct
    {G : ChiralDigraph}
    (edgeWeight : ∀ u v : G.Vertex, G.edge u v → Cl11Op R)
    {u v : G.Vertex} (p : DirectedPath G u v) :
    toMatrix (DirectedPath.product edgeWeight p) =
      DirectedPath.product (fun a b h => toMatrix (edgeWeight a b h)) p := by
  induction p with
  | refl => exact toMatrix_one
  | cons h p ih =>
      simp only [DirectedPath.product]
      change toMatrix (Cl11Op.mul _ _) = _
      rw [toMatrix_mul, ih]

open InfoGeometry.Canonical.FinitePlabicKasteleyn

/-- Directed incidence edges for the subdivision of a finite bipartite graph. -/
def plabicIncidenceEdge (G : FinitePlabicGraph)
    (x y : G.Black ⊕ (G.Edge ⊕ G.White)) : Prop :=
  match x, y with
  | .inl b, .inr (.inl e) => b = G.blackEndpoint e
  | .inr (.inl e), .inr (.inr w) => G.whiteEndpoint e = w
  | .inr (.inr w), .inr (.inl e) => G.whiteEndpoint e = w
  | .inr (.inl e), .inl b => G.blackEndpoint e = b
  | _, _ => False

/-- Black and white vertices form one chiral sector, while edge-identity
vertices form the other sector of the incidence subdivision. -/
def plabicIncidenceSector (G : FinitePlabicGraph)
    (x : G.Black ⊕ (G.Edge ⊕ G.White)) : ChiralSector :=
  match x with
  | .inl _ => ChiralSector.left
  | .inr (.inl _) => ChiralSector.right
  | .inr (.inr _) => ChiralSector.left

/-- The incidence subdivision of a finite bipartite Plabic graph. Edge
identities are vertices of the subdivision, so parallel original edges remain
distinct. The two orientations encode both directions of a bipartite walk. -/
noncomputable def plabicIncidenceDigraph (G : FinitePlabicGraph) : ChiralDigraph where
  Vertex := G.Black ⊕ (G.Edge ⊕ G.White)
  edge := plabicIncidenceEdge G
  edge_decidable := by
    intro x y
    classical
    exact Classical.propDecidable _
  sector := plabicIncidenceSector G
  allowedTransition := fun s t => s ≠ t
  transition_decidable := fun _ _ => inferInstance
  edge_allowed := by
    intro x y h
    cases x with
    | inl b =>
        cases y with
        | inl b' => cases h
        | inr yw =>
            cases yw with
            | inl e =>
                change ChiralSector.left ≠ ChiralSector.right
                decide
            | inr w => cases h
    | inr xe =>
        cases xe with
        | inl e =>
            cases y with
            | inl b =>
                change ChiralSector.right ≠ ChiralSector.left
                decide
            | inr yw =>
                cases yw with
                | inl e' => cases h
                | inr w =>
                    change ChiralSector.right ≠ ChiralSector.left
                    decide
        | inr w =>
            cases y with
            | inl b => cases h
            | inr yw =>
                cases yw with
                | inl e =>
                    change ChiralSector.left ≠ ChiralSector.right
                    decide
                | inr w' => cases h

/-- The forward two-step path associated to an edge identity. -/
def plabicEdgeForwardPath (G : FinitePlabicGraph) (e : G.Edge) :
    DirectedPath (plabicIncidenceDigraph G)
      (Sum.inl (G.blackEndpoint e)) (Sum.inr (Sum.inr (G.whiteEndpoint e))) :=
  DirectedPath.cons
    (show (plabicIncidenceDigraph G).edge
      (Sum.inl (G.blackEndpoint e)) (Sum.inr (Sum.inl e)) from by
        change G.blackEndpoint e = G.blackEndpoint e
        rfl)
    (DirectedPath.cons
      (show (plabicIncidenceDigraph G).edge
        (Sum.inr (Sum.inl e)) (Sum.inr (Sum.inr (G.whiteEndpoint e))) from by
          change G.whiteEndpoint e = G.whiteEndpoint e
          rfl)
      (DirectedPath.refl _))

/-- The reverse two-step path associated to an edge identity. -/
def plabicEdgeReversePath (G : FinitePlabicGraph) (e : G.Edge) :
    DirectedPath (plabicIncidenceDigraph G)
      (Sum.inr (Sum.inr (G.whiteEndpoint e))) (Sum.inl (G.blackEndpoint e)) :=
  DirectedPath.cons
    (show (plabicIncidenceDigraph G).edge
      (Sum.inr (Sum.inr (G.whiteEndpoint e))) (Sum.inr (Sum.inl e)) from by
        change G.whiteEndpoint e = G.whiteEndpoint e
        rfl)
    (DirectedPath.cons
      (show (plabicIncidenceDigraph G).edge
        (Sum.inr (Sum.inl e)) (Sum.inl (G.blackEndpoint e)) from by
          change G.blackEndpoint e = G.blackEndpoint e
          rfl)
      (DirectedPath.refl _))

/-- The edge-operator labels on the incidence subdivision. Forward and
reverse traversals use the existing upper and lower off-diagonal entries of
the `Cl11Op` matrix carrier; the second half of each subdivided edge is the
identity. -/
def plabicPathOperatorWeight (G : FinitePlabicGraph)
    (S : KasteleynSigning G) (weight : G.Edge → R) :
    ∀ x y : (plabicIncidenceDigraph G).Vertex,
      (plabicIncidenceDigraph G).edge x y → Cl11Op R
  | .inl _, .inr (.inl e), _ =>
      edgeTwist ((S.sign e : R) * weight e)
  | .inr (.inl _), .inr (.inr _), _ => one
  | .inr (.inr _), .inr (.inl _), _ => one
  | .inr (.inl e), .inl _, _ => ⟨0, 0, (S.sign e : R) * weight e, 0⟩
  | _, _, _ => one

/-- A forward path along one finite Plabic edge reads out its signed edge
operator in the existing `Cl11Op` carrier. -/
theorem plabicEdgeForwardPath_product (G : FinitePlabicGraph)
    (S : KasteleynSigning G) (weight : G.Edge → R) (e : G.Edge) :
    DirectedPath.product (plabicPathOperatorWeight G S weight)
        (plabicEdgeForwardPath G e) =
      edgeTwist ((S.sign e : R) * weight e) := by
  simp only [plabicEdgeForwardPath, DirectedPath.product,
    plabicPathOperatorWeight, plabicIncidenceDigraph]
  change Cl11Op.mul (edgeTwist ((S.sign e : R) * weight e))
    (Cl11Op.mul Cl11Op.one Cl11Op.one) = _
  calc
    Cl11Op.mul (edgeTwist ((S.sign e : R) * weight e))
        (Cl11Op.mul Cl11Op.one Cl11Op.one) =
      Cl11Op.mul (edgeTwist ((S.sign e : R) * weight e)) Cl11Op.one := by
        rw [Cl11Op.one_mul]
    _ = edgeTwist ((S.sign e : R) * weight e) := Cl11Op.mul_one _

/-- A reverse path along one finite Plabic edge reads out the reverse
off-diagonal operator in the same matrix carrier. -/
theorem plabicEdgeReversePath_product (G : FinitePlabicGraph)
    (S : KasteleynSigning G) (weight : G.Edge → R) (e : G.Edge) :
    DirectedPath.product (plabicPathOperatorWeight G S weight)
        (plabicEdgeReversePath G e) =
      ⟨0, 0, (S.sign e : R) * weight e, 0⟩ := by
  simp only [plabicEdgeReversePath, DirectedPath.product,
    plabicPathOperatorWeight, plabicIncidenceDigraph]
  change Cl11Op.mul Cl11Op.one
    (Cl11Op.mul (⟨0, 0, (S.sign e : R) * weight e, 0⟩ : Cl11Op R)
      Cl11Op.one) = _
  calc
    Cl11Op.mul Cl11Op.one
        (Cl11Op.mul (⟨0, 0, (S.sign e : R) * weight e, 0⟩ : Cl11Op R)
          Cl11Op.one) =
      Cl11Op.mul Cl11Op.one
        (⟨0, 0, (S.sign e : R) * weight e, 0⟩ : Cl11Op R) := by
          rw [Cl11Op.mul_one]
    _ = _ := Cl11Op.one_mul _

/-- Summing the upper-right path readouts over the edge identities with fixed
endpoints recovers the existing signed Plabic edge-sum matrix entry. This is a
finite combinatorial readout; it does not assert a square-move identity. -/
theorem edgeSumMatrix_eq_sum_forwardPath_m12
    (G : FinitePlabicGraph) (S : KasteleynSigning G)
    (weight : G.Edge → R) (w : G.White) (b : G.Black) :
    edgeSumMatrix S weight w b =
      ∑ e : G.Edge,
        if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w then
          (DirectedPath.product (plabicPathOperatorWeight G S weight)
            (plabicEdgeForwardPath G e)).m12
        else 0 := by
  classical
  rw [edgeSumMatrix_apply]
  apply Finset.sum_congr rfl
  intro e he
  by_cases h : G.blackEndpoint e = b ∧ G.whiteEndpoint e = w
  · simp [h, plabicEdgeForwardPath_product, Cl11Op.edgeTwist]
  · simp [h]

/-- The same signed edge-sum entry is recovered from the lower-left readout
of the corresponding white-to-black incidence paths. This is a finite path
identity for the chosen `Cl11Op` labels; it does not identify reverse labels
with adjoints of forward labels. -/
theorem edgeSumMatrix_eq_sum_reversePath_m21
    (G : FinitePlabicGraph) (S : KasteleynSigning G)
    (weight : G.Edge → R) (w : G.White) (b : G.Black) :
    edgeSumMatrix S weight w b =
      ∑ e : G.Edge,
        if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w then
          (DirectedPath.product (plabicPathOperatorWeight G S weight)
            (plabicEdgeReversePath G e)).m21
        else 0 := by
  classical
  rw [edgeSumMatrix_apply]
  apply Finset.sum_congr rfl
  intro e he
  by_cases h : G.blackEndpoint e = b ∧ G.whiteEndpoint e = w
  · simp [h, plabicEdgeReversePath_product]
  · simp [h]

/-- The white-to-black block entry of the existing Plabic Dirac operator is
the same finite sum of forward-path readouts as its coupling matrix entry. -/
theorem edgeSumDirac_whiteBlack_eq_sum_forwardPath_m12
    (G : FinitePlabicGraph) (S : KasteleynSigning G)
    [StarRing R] (weight : G.Edge → R) (w : G.White) (b : G.Black) :
    edgeSumDirac S weight (Sum.inr w) (Sum.inl b) =
      ∑ e : G.Edge,
        if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w then
          (DirectedPath.product (plabicPathOperatorWeight G S weight)
            (plabicEdgeForwardPath G e)).m12
        else 0 := by
  rw [edgeSumDirac]
  rw [InfoGeometry.Canonical.PlabicDiracKrein.diracDHK,
    Matrix.fromBlocks_apply₂₁]
  exact edgeSumMatrix_eq_sum_forwardPath_m12 G S weight w b

/-- The white-to-black entry of the Plabic Dirac block is also the sum of the
lower-left readouts along the corresponding reverse incidence paths. -/
theorem edgeSumDirac_whiteBlack_eq_sum_reversePath_m21
    (G : FinitePlabicGraph) (S : KasteleynSigning G)
    [StarRing R] (weight : G.Edge → R) (w : G.White) (b : G.Black) :
    edgeSumDirac S weight (Sum.inr w) (Sum.inl b) =
      ∑ e : G.Edge,
        if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w then
          (DirectedPath.product (plabicPathOperatorWeight G S weight)
            (plabicEdgeReversePath G e)).m21
        else 0 := by
  rw [edgeSumDirac]
  rw [InfoGeometry.Canonical.PlabicDiracKrein.diracDHK,
    Matrix.fromBlocks_apply₂₁]
  exact edgeSumMatrix_eq_sum_reversePath_m21 G S weight w b

/-- The characteristic polynomial of a directed path's operator product is
unchanged when every edge label is conjugated by the same local
`edgeTransport`. This is a path-level consequence of the existing matrix
representation and inverse laws; it does not identify a Plabic square move
with this conjugation. -/
theorem matrix_edgeTransport_pathProduct_charpoly_invariant
    {G : ChiralDigraph} (w : R)
    (edgeWeight : ∀ u v : G.Vertex, G.edge u v → Cl11Op R)
    {u v : G.Vertex} (p : DirectedPath G u v) :
    Matrix.charpoly
        (toMatrix (DirectedPath.product
          (fun a b h =>
            edgeTransport w * edgeWeight a b h * edgeTransportInv w) p)) =
      Matrix.charpoly (toMatrix (DirectedPath.product edgeWeight p)) := by
  rw [DirectedPath.product_conjugate
    (edgeTransport w) (edgeTransportInv w)
    (edgeTransport_mul_inv w) (edgeTransportInv_mul w)]
  exact matrix_edgeTransport_charpoly_invariant w (DirectedPath.product edgeWeight p)

/-- The matrix representation commutes with descent of compatible path
products through the presented path quotient. -/
theorem toMatrix_presentedPathProduct
    {G : ChiralDigraph} (P : DirectedPathPresentation G)
    (edgeWeight : ∀ u v : G.Vertex, G.edge u v → Cl11Op R)
    (hcompat : ProductCompatible P edgeWeight)
    {u v : G.Vertex} (p : PresentedPathClass P u v) :
    toMatrix (PresentedPathClass.product P edgeWeight hcompat p) =
      PresentedPathClass.product
        P (fun a b h => toMatrix (edgeWeight a b h))
        (by
          intro a b p q h
          simpa only [toMatrix_pathProduct edgeWeight p,
            toMatrix_pathProduct edgeWeight q] using congrArg toMatrix (hcompat h)) p := by
  refine Quot.inductionOn p ?_
  intro p'
  exact toMatrix_pathProduct edgeWeight p'

end Cl11Op

end InfoGeometry.Holography.PlabicKrein
