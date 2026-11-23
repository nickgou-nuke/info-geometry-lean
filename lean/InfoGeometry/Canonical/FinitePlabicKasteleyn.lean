/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
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

/-- Combinatorial data for an orientation-reversing symmetry of a finite
bipartite graph with supplied face boundaries.  The endpoint laws make this a
graph automorphism, and `faceBoundary_reverse` says the chosen cyclic boundary
lists are carried to the reversed lists.  A Klein deck transformation can
instantiate this structure when it acts on a finite plabic model. -/
structure OrientationReversingPlabicEquiv (G : FinitePlabicGraph) where
  black : Equiv.Perm G.Black
  white : Equiv.Perm G.White
  edge : Equiv.Perm G.Edge
  face : Equiv.Perm G.Face
  blackEndpoint_map : ∀ e, G.blackEndpoint (edge e) = black (G.blackEndpoint e)
  whiteEndpoint_map : ∀ e, G.whiteEndpoint (edge e) = white (G.whiteEndpoint e)
  faceBoundary_reverse : ∀ f,
    G.faceBoundary (face f) = ((G.faceBoundary f).map edge).reverse

namespace OrientationReversingPlabicEquiv

variable {G : FinitePlabicGraph}

/-- Pulling a Kasteleyn signing back along an orientation-reversing graph
equivalence preserves its face-curvature condition.  Reversing a boundary
changes its orientation but not the product of its integer edge signs. -/
def transportSigning (τ : OrientationReversingPlabicEquiv G)
    (S : KasteleynSigning G) : KasteleynSigning G where
  sign e := S.sign (τ.edge e)
  sign_sq e := S.sign_sq (τ.edge e)
  face_product f := by
    have hf := S.face_product (τ.face f)
    rw [τ.faceBoundary_reverse] at hf
    simp only [List.map_reverse, List.prod_reverse, List.map_map,
      List.length_reverse, List.length_map] at hf
    change ((G.faceBoundary f).map (S.sign ∘ τ.edge)).prod = _
    exact hf

@[simp] theorem transportSigning_sign (τ : OrientationReversingPlabicEquiv G)
    (S : KasteleynSigning G) (e : G.Edge) :
    (τ.transportSigning S).sign e = S.sign (τ.edge e) := rfl

end OrientationReversingPlabicEquiv

/-- A color-reversing symmetry of finite bipartite graph data. The endpoint
maps exchange the black and white types, and the image of each oriented face
boundary agrees with the reversed boundary up to cyclic rotation. The edge and
face maps are involutions; a corresponding infinite-lattice glide-square
translation remains a separate action-level statement. -/
structure ColorReversingPlabicEquiv (G : FinitePlabicGraph) where
  blackToWhite : G.Black ≃ G.White
  edge : Equiv.Perm G.Edge
  face : Equiv.Perm G.Face
  blackEndpoint_map : ∀ e,
    G.whiteEndpoint (edge e) = blackToWhite (G.blackEndpoint e)
  whiteEndpoint_map : ∀ e,
    G.blackEndpoint (edge e) = blackToWhite.symm (G.whiteEndpoint e)
  edge_sq : ∀ e, edge (edge e) = e
  face_sq : ∀ f, face (face f) = f
  faceBoundary_reverse : ∀ f,
    G.faceBoundary (face f) ~r ((G.faceBoundary f).map edge).reverse

namespace ColorReversingPlabicEquiv

variable {G : FinitePlabicGraph}

/-- The induced involution of the total bipartite vertex type, exchanging the
black and white summands. -/
def vertexEquiv (τ : ColorReversingPlabicEquiv G) :
    G.Black ⊕ G.White ≃ G.Black ⊕ G.White where
  toFun
    | Sum.inl b => Sum.inr (τ.blackToWhite b)
    | Sum.inr w => Sum.inl (τ.blackToWhite.symm w)
  invFun
    | Sum.inl b => Sum.inr (τ.blackToWhite b)
    | Sum.inr w => Sum.inl (τ.blackToWhite.symm w)
  left_inv x := by
    cases x with
    | inl b => simp
    | inr w => simp
  right_inv x := by
    cases x with
    | inl b => simp
    | inr w => simp

/-- The canonical bipartite parity readout on black-plus-white vertices. -/
def vertexGrade (G : FinitePlabicGraph) : G.Black ⊕ G.White → ℤ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- A color-reversing seam negates the bipartite grading pointwise. -/
theorem vertexEquiv_negates_grade (τ : ColorReversingPlabicEquiv G)
    (v : G.Black ⊕ G.White) :
    vertexGrade G (τ.vertexEquiv v) = -vertexGrade G v := by
  cases v <;> rfl

/-- Pullback along a color-reversing, orientation-reversing graph equivalence
preserves the Kasteleyn face law.  Cyclic changes of the chosen face-list
basepoint do not affect the sign product. -/
def transportSigning (τ : ColorReversingPlabicEquiv G)
    (S : KasteleynSigning G) : KasteleynSigning G where
  sign e := S.sign (τ.edge e)
  sign_sq e := S.sign_sq (τ.edge e)
  face_product f := by
    have hf := S.face_product (τ.face f)
    have hrot := τ.faceBoundary_reverse f
    have hlen : (G.faceBoundary (τ.face f)).length = (G.faceBoundary f).length := by
      obtain ⟨n, hn⟩ := hrot
      simpa using congrArg List.length hn
    have hprod := (hrot.perm.map S.sign).prod_eq
    have hprod' : ((G.faceBoundary (τ.face f)).map S.sign).prod =
        ((G.faceBoundary f).map (S.sign ∘ τ.edge)).prod := by
      simpa only [List.map_reverse, List.prod_reverse, List.map_map] using hprod
    calc
      ((G.faceBoundary f).map (S.sign ∘ τ.edge)).prod =
          ((G.faceBoundary (τ.face f)).map S.sign).prod := hprod'.symm
      _ = (-1 : ℤ) ^ ((G.faceBoundary f).length / 2 + 1) := by
        rw [hf, hlen]

@[simp] theorem transportSigning_sign (τ : ColorReversingPlabicEquiv G)
    (S : KasteleynSigning G) (e : G.Edge) :
    (τ.transportSigning S).sign e = S.sign (τ.edge e) := rfl

end ColorReversingPlabicEquiv

/-! ### A finite square model of the mod-two Klein seam -/

/-- The Klein glide reduced modulo two.  Since negation is trivial in
`ZMod 2`, this is the order-two map `(u,v) ↦ (u+1,v)`. -/
def kleinGlideModTwo (p : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 :=
  (p.1 + 1, -p.2)

theorem intKleinGlide_reduces_mod_two (u v : ℤ) :
    (((u + 1 : ℤ) : ZMod 2), ((-v : ℤ) : ZMod 2)) =
      kleinGlideModTwo ((u : ZMod 2), (v : ZMod 2)) := by
  simp [kleinGlideModTwo]

/-- Modulo two, the glide-square translation by two is trivial. -/
theorem kleinGlideModTwo_sq (p : ZMod 2 × ZMod 2) :
    kleinGlideModTwo (kleinGlideModTwo p) = p := by
  rcases p with ⟨u, v⟩
  ext
  · change u + 1 + 1 = u
    calc
      u + 1 + 1 = u + (1 + 1) := by ring
      _ = u := by rw [show (1 : ZMod 2) + 1 = 0 by decide]; simp
  · simp [kleinGlideModTwo]

/-- Black vertices at `(0,0)` and `(1,1)` in the two-periodic square lattice. -/
def squareBlackCoordinate (b : Fin 2) : ZMod 2 × ZMod 2 :=
  if b = 0 then (0, 0) else (1, 1)

/-- White vertices at `(1,0)` and `(0,1)` in the two-periodic square lattice. -/
def squareWhiteCoordinate (w : Fin 2) : ZMod 2 × ZMod 2 :=
  if w = 0 then (1, 0) else (0, 1)

/-- The four-edge bipartite square with its cyclic face boundary. -/
def KleinSquareGraph : FinitePlabicGraph where
  Black := Fin 2
  White := Fin 2
  Edge := Fin 4
  Face := Unit
  blackEndpoint e := if e = 0 then 0 else if e = 1 then 1 else if e = 2 then 1 else 0
  whiteEndpoint e := if e = 0 then 0 else if e = 1 then 0 else if e = 2 then 1 else 1
  faceBoundary _ := [0, 1, 2, 3]
  faceBoundary_even _ := ⟨2, by decide⟩

/-- The square seam exchanges black and white vertices and reverses the
orientation of the cyclic square face. -/
def kleinSquareSeam : ColorReversingPlabicEquiv KleinSquareGraph where
  blackToWhite := Equiv.refl (Fin 2)
  edge := Equiv.swap (1 : Fin 4) (3 : Fin 4)
  face := Equiv.refl Unit
  blackEndpoint_map e := by
    fin_cases e <;> decide
  whiteEndpoint_map e := by
    fin_cases e <;> decide
  edge_sq e := by
    change Equiv.swap (1 : Fin 4) 3 (Equiv.swap 1 3 e) = e
    exact Equiv.swap_apply_self (1 : Fin 4) 3 e
  face_sq _ := rfl
  faceBoundary_reverse f := by
    cases f
    exact ⟨1, by decide⟩

/-- The finite seam action has order two, matching the glide after reduction
modulo the two-periodic square lattice. -/
theorem kleinSquareSeam_edge_sq (e : KleinSquareGraph.Edge) :
    kleinSquareSeam.edge (kleinSquareSeam.edge e) = e := by
  exact kleinSquareSeam.edge_sq e

/-- The color-reversing graph equivalence is exactly the mod-two Klein glide
on the chosen black vertex representatives. -/
theorem kleinSquareSeam_agrees_black_mod_two_glide (b : Fin 2) :
    squareWhiteCoordinate (kleinSquareSeam.blackToWhite b) =
      kleinGlideModTwo (squareBlackCoordinate b) := by
  fin_cases b <;> decide

/-- The same seam agrees with the mod-two Klein glide on white vertex
representatives, with its image now in the black class. -/
theorem kleinSquareSeam_agrees_white_mod_two_glide (w : Fin 2) :
    squareBlackCoordinate (kleinSquareSeam.blackToWhite.symm w) =
      kleinGlideModTwo (squareWhiteCoordinate w) := by
  fin_cases w <;> decide

/-- A concrete Kasteleyn signing on the four-edge square. -/
def kleinSquareSigning : KasteleynSigning KleinSquareGraph where
  sign e := if e.val = 3 then -1 else 1
  sign_sq e := by
    fin_cases e <;> norm_num
  face_product f := by
    cases f
    change (([0, 1, 2, 3] : List (Fin 4)).map
      (fun e => if e.val = 3 then -1 else 1)).prod = (-1 : ℤ) ^ 3
    norm_num

/-- The mod-two Klein seam carries the concrete square signing to another
Kasteleyn signing on the same finite graph. -/
def kleinSquareSeamSigning : KasteleynSigning KleinSquareGraph :=
  kleinSquareSeam.transportSigning kleinSquareSigning

theorem kleinSquareSeamSigning_face_law (f : KleinSquareGraph.Face) :
    ((KleinSquareGraph.faceBoundary f).map kleinSquareSeamSigning.sign).prod =
      (-1 : ℤ) ^ ((KleinSquareGraph.faceBoundary f).length / 2 + 1) :=
  kleinSquareSeamSigning.face_product f

variable {G}

/-- The signed, weighted sum over all edge identities joining `b` to `w`.
Rows are white vertices and columns are black vertices, matching the existing
`PlabicDiracKrein.diracDHK` convention. -/
def edgeSumMatrix {R : Type*} [Ring R] (S : KasteleynSigning G)
    (weight : G.Edge → R) : Matrix G.White G.Black R :=
  fun w b => ∑ e : G.Edge,
    if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w
    then (S.sign e : R) * weight e else 0

@[simp] theorem edgeSumMatrix_apply {R : Type*} [Ring R]
    (S : KasteleynSigning G) (weight : G.Edge → R) (w : G.White) (b : G.Black) :
    edgeSumMatrix S weight w b = ∑ e : G.Edge,
      if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w
      then (S.sign e : R) * weight e else 0 := rfl

/-- Signed edge sums are additive in the edge weights. -/
theorem edgeSumMatrix_add {R : Type*} [Ring R]
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

/-- The signed edge-sum matrix is homogeneous in the edge weights. -/
theorem edgeSumMatrix_smul {R : Type*} [Ring R]
    (S : KasteleynSigning G) (r : R) (weight : G.Edge → R) :
    edgeSumMatrix S (fun e => r * weight e) =
      r • edgeSumMatrix S weight := by
  classical
  ext w b
  simp only [edgeSumMatrix, Matrix.smul_apply, smul_eq_mul]
  change (Finset.univ.sum (fun e => if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w then
      (S.sign e : R) * (r * weight e) else 0)) =
    r * (Finset.univ.sum (fun e => if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w then
      (S.sign e : R) * weight e else 0))
  calc
    (Finset.univ.sum (fun e => if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w then
        (S.sign e : R) * (r * weight e) else 0)) =
      Finset.univ.sum (fun e => r * (if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w then
        (S.sign e : R) * weight e else 0)) := by
          apply Finset.sum_congr rfl
          intro e he
          split_ifs
          · rw [← mul_assoc, Int.cast_comm, mul_assoc]
          · rw [mul_zero]
    _ = r * Finset.univ.sum (fun e => if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w then
        (S.sign e : R) * weight e else 0) := by
          exact (Finset.mul_sum Finset.univ
            (fun e => if G.blackEndpoint e = b ∧ G.whiteEndpoint e = w then
              (S.sign e : R) * weight e else 0) r).symm

/-- If no edge has the selected endpoints, the corresponding matrix entry is
zero. -/
theorem edgeSumMatrix_eq_zero_of_no_edge {R : Type*} [Ring R]
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
abbrev edgeSumDirac {R : Type*} [Ring R] [StarRing R]
    (S : KasteleynSigning G) (weight : G.Edge → R) :
    Matrix (G.Black ⊕ G.White) (G.Black ⊕ G.White) R :=
  InfoGeometry.Canonical.PlabicDiracKrein.diracDHK (edgeSumMatrix S weight)

/-- A self-adjoint scalar rescaling of all Kasteleyn edge weights rescales the
block Dirac operator by the same scalar. -/
theorem edgeSumDirac_smul {R : Type*} [CommRing R] [StarRing R]
    (S : KasteleynSigning G) (r : R) (hr : star r = r)
    (weight : G.Edge → R) :
    edgeSumDirac S (fun e => r * weight e) =
      r • edgeSumDirac S weight := by
  unfold edgeSumDirac
  rw [edgeSumMatrix_smul]
  ext i j
  cases i <;> cases j <;>
    simp [PlabicDiracKrein.diracDHK, Matrix.smul_apply,
      Matrix.fromBlocks, Matrix.conjTranspose_smul, hr]

/-- The block square of the Kasteleyn-coupled Dirac operator is the pair of
Gram matrices of the weighted edge-sum matrix. -/
theorem edgeSumDirac_sq {R : Type*} [Ring R] [StarRing R]
    (S : KasteleynSigning G) (weight : G.Edge → R) :
    edgeSumDirac S weight * edgeSumDirac S weight =
      Matrix.fromBlocks
        ((edgeSumMatrix S weight).conjTranspose * (edgeSumMatrix S weight)) 0 0
        ((edgeSumMatrix S weight) * (edgeSumMatrix S weight).conjTranspose) :=
  InfoGeometry.Canonical.PlabicDiracKrein.diracDHK_sq (edgeSumMatrix S weight)

end InfoGeometry.Canonical.FinitePlabicKasteleyn
