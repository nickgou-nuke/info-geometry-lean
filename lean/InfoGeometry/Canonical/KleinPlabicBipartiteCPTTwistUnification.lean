/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra
import InfoGeometry.Canonical.CPTGradingCompass
import InfoGeometry.Canonical.Cl11BipartiteDiracBridge
import InfoGeometry.Canonical.CantorPlabicTwistorBridge
import InfoGeometry.Topology.WallpaperSymmetry
import InfoGeometry.Topology.KleinQuotientDeckInvariants
import InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge

/-!
# InfoGeometry.Canonical.KleinPlabicBipartiteCPTTwistUnification

Literature-grounded unification of the repository's five $\mathbb{Z}/2$-graded
and order-2-twist owners into one common framework without conflating distinct
groups as equalities:

1. **Abstract $\mathbb{Z}/2$-twisted commutant algebra**
   (`KleinBottleTwistedCommutantBridge`): for any order-2 ring automorphism
   `α² = 1` preserving a set `S`, the ordinary and `α`-twisted commutants form
   a $\mathbb{Z}/2$-graded multiplication table (`twisted_mul_twisted_mem_ordinary`,
   `ordinary_mul_twisted_mem_twisted`, `twisted_mul_ordinary_mem_twisted`),
   mirroring $G^2 = T_x$.
2. **Klein-bottle glide on a bipartite rank-2 lattice**
   (`WallpaperSymmetry`): the integral glide `(u, v) ↦ (u + 1, -v)` reverses
   bipartite parity (`integralGlide_flips_color`), while its square
   `(u, v) ↦ (u + 2, v)` preserves parity (`integralGlide_sq_preserves_color`),
   matching `glide_squared_eq_x_translation`.
3. **Kasteleyn (1961) & Tesler (2000) signed bipartite square on the Klein bottle**:
   a concrete 4-vertex bipartite square with Kasteleyn edge signs
   `(+1, +1, +1, -1)` (face product `-1`) yields a real $4 \times 4$ signed
   Dirac–Kasteleyn operator `kasteleynDiracMat` that strictly anticommutes with
   the bipartite chirality involution `bipartiteChiralityMat`, squares to
   `2 • 1` (exact Kasteleyn cross-term cancellation / spectral gap), and
   pulls back directly into `KleinBottleTwistedCommutantBridge.twistedCommutant`
   under the order-2 chirality-conjugation automorphism `kleinSeamConjAut`.
4. **Intertwining with CPT grading, bipartite `Cl(1,1)` Dirac, plabic square
   mutation (Postnikov 2006), and hyperoctahedral `SignedPerm`**:
   - `kleinSeamSignedPerm : SignedPerm 1` realizes the Klein-bottle seam flip
     as an order-2 Boolean automorphism swapping `KreinSector.plus ↔ minus`.
   - The `2 × 2` Kasteleyn hopping block plugs directly into
     `Cl11BipartiteDiracBridge.compositeDirac_sq_decoupled`.
   - `klein_plabic_bipartite_cpt_unification` packages all five verified
     structural readouts together.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinPlabicBipartiteCPTTwistUnification

open scoped Matrix Kronecker
open InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra
open InfoGeometry.Canonical.KreinProjectorLattice
open InfoGeometry.Canonical.CPTGradingCompass
open InfoGeometry.Canonical.Cl11BipartiteDiracBridge
open InfoGeometry.Canonical.CantorPlabicTwistorBridge
open InfoGeometry.Topology.Wallpaper
open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge

/-! ## 1. Abstract $\mathbb{Z}/2$-graded twisted-commutant product laws -/

section TwistedCommutantLaws

variable {R : Type*} [Ring R]

/-- The product of two elements in the `α`-twisted commutant lies in the
ordinary commutant whenever `α² = 1` and `α` preserves `S`
(algebraic analogue of $G^2 = T_x$). -/
theorem twisted_mul_twisted_mem_ordinary
    (S : Set R) (α : R ≃+* R)
    (hα : ∀ a, α (α a) = a) (hS : ∀ a ∈ S, α a ∈ S)
    {x y : R} (hx : x ∈ twistedCommutant S α) (hy : y ∈ twistedCommutant S α) :
    x * y ∈ ordinaryCommutant S := by
  intro a ha
  calc
    (x * y) * a = x * (y * a) := mul_assoc x y a
    _ = x * (α a * y) := by rw [hy a ha]
    _ = (x * α a) * y := (mul_assoc x (α a) y).symm
    _ = (α (α a) * x) * y := by rw [hx (α a) (hS a ha)]
    _ = a * (x * y) := by rw [hα a, mul_assoc]

/-- Left multiplication by an ordinary-commutant element preserves the
`α`-twisted commutant whenever `α` preserves `S`. -/
theorem ordinary_mul_twisted_mem_twisted
    (S : Set R) (α : R ≃+* R) (hS : ∀ a ∈ S, α a ∈ S)
    {x y : R} (hx : x ∈ ordinaryCommutant S) (hy : y ∈ twistedCommutant S α) :
    x * y ∈ twistedCommutant S α := by
  intro a ha
  calc
    (x * y) * a = x * (y * a) := mul_assoc x y a
    _ = x * (α a * y) := by rw [hy a ha]
    _ = (x * α a) * y := (mul_assoc x (α a) y).symm
    _ = (α a * x) * y := by rw [hx (α a) (hS a ha)]
    _ = α a * (x * y) := mul_assoc (α a) x y

/-- Right multiplication by an ordinary-commutant element preserves the
`α`-twisted commutant. -/
theorem twisted_mul_ordinary_mem_twisted
    (S : Set R) (α : R ≃+* R)
    {x y : R} (hx : x ∈ twistedCommutant S α) (hy : y ∈ ordinaryCommutant S) :
    x * y ∈ twistedCommutant S α := by
  intro a ha
  calc
    (x * y) * a = x * (y * a) := mul_assoc x y a
    _ = x * (a * y) := by rw [hy a ha]
    _ = (x * a) * y := (mul_assoc x a y).symm
    _ = (α a * x) * y := by rw [hx a ha]
    _ = α a * (x * y) := mul_assoc (α a) x y

/-- Conjugation by an involution `U` (`U * U = 1`) defines an order-2 ring
automorphism of `R`. -/
def involutionConjAut (U : R) (hU : U * U = 1) : R ≃+* R where
  toFun x := U * x * U
  invFun x := U * x * U
  left_inv x := by
    calc
      U * (U * x * U) * U = (U * U) * x * (U * U) := by simp [mul_assoc]
      _ = x := by rw [hU, one_mul, mul_one]
  right_inv x := by
    calc
      U * (U * x * U) * U = (U * U) * x * (U * U) := by simp [mul_assoc]
      _ = x := by rw [hU, one_mul, mul_one]
  map_mul' x y := by
    calc
      U * (x * y) * U = U * x * (U * U) * y * U := by rw [hU, mul_one]; simp [mul_assoc]
      _ = (U * x * U) * (U * y * U) := by simp [mul_assoc]
  map_add' x y := by
    simp [mul_add, add_mul]

theorem involutionConjAut_involutive (U : R) (hU : U * U = 1) (x : R) :
    involutionConjAut U hU (involutionConjAut U hU x) = x :=
  (involutionConjAut U hU).left_inv x

/-- The involution `U` itself always lies in `twistedCommutant S (involutionConjAut U hU)`
for any subset `S`! -/
theorem involution_mem_twistedCommutant (S : Set R) (U : R) (hU : U * U = 1) :
    U ∈ twistedCommutant S (involutionConjAut U hU) := by
  intro a _
  change U * a = (U * a * U) * U
  rw [mul_assoc, hU, mul_one]

end TwistedCommutantLaws

/-! ## 2. Klein-bottle glide on a bipartite rank-2 lattice $\mathbb{Z}^2$ -/

/-- Bipartite black/white coloring of $\mathbb{Z}^2$: `(u, v) ↦ (u + v) mod 2`. -/
def latticeColor (p : ℤ × ℤ) : Bool :=
  decide (Odd (p.1 + p.2))

/-- Integral bipartite glide reflection `(u, v) ↦ (u + 1, -v)` on the doubled
square lattice (corresponding to `G(x, y) = (x + 1/2, -y)` at half-step). -/
def integralGlide (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 + 1, -p.2)

/-- Crossing the Klein-bottle glide seam strictly flips the bipartite vertex color
(black ↔ white). -/
theorem integralGlide_flips_color (p : ℤ × ℤ) :
    latticeColor (integralGlide p) = !(latticeColor p) := by
  rcases p with ⟨u, v⟩
  unfold latticeColor integralGlide
  have hparity : Odd (u + 1 + -v) ↔ ¬ Odd (u + v) := by
    rw [Int.not_odd_iff_even]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k + v, ?_⟩
      omega
    · rintro ⟨k, hk⟩
      refine ⟨k - v, ?_⟩
      omega
  by_cases h : Odd (u + v)
  · have h' : ¬ Odd (u + 1 + -v) := fun hodd => (hparity.mp hodd) h
    simp [h, h']
  · have h' : Odd (u + 1 + -v) := hparity.mpr h
    simp [h, h']

/-- Applying the Klein-bottle glide twice yields `(u + 2, v)`, which preserves
the bipartite coloring (mirroring `Wallpaper.glide_squared_eq_x_translation`). -/
theorem integralGlide_sq (p : ℤ × ℤ) :
    integralGlide (integralGlide p) = (p.1 + 2, p.2) := by
  rcases p with ⟨u, v⟩
  ext
  · simp [integralGlide]; ring
  · simp [integralGlide]

theorem integralGlide_sq_preserves_color (p : ℤ × ℤ) :
    latticeColor (integralGlide (integralGlide p)) = latticeColor p := by
  rw [integralGlide_flips_color, integralGlide_flips_color, Bool.not_not]

/-! ### Signed nearest-neighbor lattice and the Klein seam gauge law

The finite square model below is not the infinite lattice quotient.  This
section records the local edge-signing law on the actual integral square grid:
each unit face has Kasteleyn product `-1`, and the orientation-reversing glide
pulls the signing back to a vertex-gauge transform.  These are local
combinatorial identities; they do not assert a finite quotient graph or a
classification of its spin structures.
-/

/-- A positively oriented unit edge in the integral square lattice. -/
structure SquareLatticeEdge where
  base : ℤ × ℤ
  vertical : Bool
  deriving DecidableEq, Inhabited

/-- Initial vertex of a positively oriented square-lattice edge. -/
def squareEdgeSource (e : SquareLatticeEdge) : ℤ × ℤ := e.base

/-- Terminal vertex of a positively oriented square-lattice edge. -/
def squareEdgeTarget (e : SquareLatticeEdge) : ℤ × ℤ :=
  if e.vertical then (e.base.1, e.base.2 + 1) else (e.base.1 + 1, e.base.2)

/-- The periodic Kasteleyn signing: horizontal edges have sign `+1`; a
vertical edge based at horizontal coordinate `u` has sign `(-1)^u`. -/
def squareLatticeKasteleynSign (e : SquareLatticeEdge) : ℤ :=
  if e.vertical then signZ e.base.1 else 1

/-- Vertex gauge used to compare the pulled-back signing across the glide. -/
def squareLatticeSeamGauge (p : ℤ × ℤ) : ℤ := signZ p.2

/-- The glide image of an unoriented edge, represented again by a positively
oriented edge.  A vertical edge reverses direction under the reflection, so
its new base is the image of its former terminal vertex. -/
def integralGlideEdge (e : SquareLatticeEdge) : SquareLatticeEdge :=
  if e.vertical then ⟨(e.base.1 + 1, -e.base.2 - 1), true⟩
  else ⟨integralGlide e.base, false⟩

/-- The edge map sends endpoints to the glide images, allowing endpoint order
to reverse precisely on vertical edges. -/
theorem integralGlideEdge_endpoints (e : SquareLatticeEdge) :
    squareEdgeSource (integralGlideEdge e) =
        (if e.vertical then integralGlide (squareEdgeTarget e)
          else integralGlide (squareEdgeSource e)) ∧
      squareEdgeTarget (integralGlideEdge e) =
        (if e.vertical then integralGlide (squareEdgeSource e)
          else integralGlide (squareEdgeTarget e)) := by
  cases e with
  | mk base vertical =>
      cases vertical <;> rcases base with ⟨u, v⟩
      · simp [squareEdgeSource, squareEdgeTarget, integralGlideEdge,
          integralGlide]
      · simp [squareEdgeSource, squareEdgeTarget, integralGlideEdge,
          integralGlide]
        all_goals ring

private theorem squareLattice_sign_sq (n : ℤ) : signZ n * signZ n = 1 := by
  have h : signZ n = 1 ∨ signZ n = -1 := by
    unfold signZ
    split_ifs <;> simp
  rcases h with h | h <;> simp [h]

private theorem squareLattice_sign_one : signZ (1 : ℤ) = -1 := by
  norm_num [signZ]

/-- Across the glide seam, the signed edge weight changes by the coboundary
of `squareLatticeSeamGauge`.  This is the edge-coefficient identity underlying
diagonal gauge conjugation on any finite subgraph where the induced edge
permutation and boundary data are defined. -/
theorem integralGlideEdge_kasteleyn_gauge_law (e : SquareLatticeEdge) :
    squareLatticeKasteleynSign (integralGlideEdge e) =
      squareLatticeSeamGauge (squareEdgeSource e) *
        squareLatticeSeamGauge (squareEdgeTarget e) *
          squareLatticeKasteleynSign e := by
  cases e with
  | mk base vertical =>
      cases vertical <;> rcases base with ⟨u, v⟩
      · simp [integralGlideEdge, integralGlide, squareLatticeKasteleynSign,
          squareLatticeSeamGauge, squareEdgeSource, squareEdgeTarget,
          squareLattice_sign_sq]
      · simp only [integralGlideEdge, squareLatticeKasteleynSign,
          squareLatticeSeamGauge, squareEdgeSource, squareEdgeTarget,
          ite_true]
        have hu : signZ (u + 1) = signZ u * -1 := by
          rw [signZ_add u 1, squareLattice_sign_one]
        have hv : signZ (v + 1) = signZ v * -1 := by
          rw [signZ_add v 1, squareLattice_sign_one]
        rw [hu, hv]
        calc
          signZ u * -1 = signZ v * (signZ v * -1) * signZ u := by
            calc
              signZ u * -1 = signZ u * 1 * -1 := by ring
              _ = signZ u * (signZ v * signZ v) * -1 := by
                rw [squareLattice_sign_sq v]
              _ = signZ v * (signZ v * -1) * signZ u := by ring

/-- Every unit square has Kasteleyn face-sign product `-1`. -/
theorem squareLattice_unitFace_sign_product (u v : ℤ) :
    squareLatticeKasteleynSign ⟨(u, v), false⟩ *
      squareLatticeKasteleynSign ⟨(u + 1, v), true⟩ *
      squareLatticeKasteleynSign ⟨(u, v), true⟩ *
      squareLatticeKasteleynSign ⟨(u, v + 1), false⟩ = -1 := by
  simp [squareLatticeKasteleynSign]
  have hu : signZ (u + 1) = signZ u * -1 := by
    rw [signZ_add u 1, squareLattice_sign_one]
  calc
    signZ (u + 1) * signZ u = (signZ u * -1) * signZ u := by rw [hu]
    _ = (signZ u * signZ u) * -1 := by ring
    _ = -1 := by rw [squareLattice_sign_sq u]; norm_num

/-! ## 3. Kasteleyn (1961) / Tesler (2000) signed bipartite square & Klein twisted commutant -/

/-- Kasteleyn edge signs `(σ_N, σ_E, σ_S, σ_W) = (+1, +1, +1, -1)` around a
single 4-vertex bipartite plabic square. -/
def kasteleynEdgeSigns : Fin 4 → ℤ :=
  ![1, 1, 1, -1]

/-- Kasteleyn odd-parity face law: the product of the four edge signs around
the square face equals `-1` (guaranteeing exact cancellation of cross terms in
$D^2$ and Pfaffian orientation on the Klein-bottle dimer lattice). -/
theorem kasteleyn_face_product_eq_neg_one :
    kasteleynEdgeSigns 0 * kasteleynEdgeSigns 1 *
      kasteleynEdgeSigns 2 * kasteleynEdgeSigns 3 = -1 := by
  decide

/-- Bipartite chirality involution `γ = diag(+1, -1, +1, -1)` on the 4-vertex
bipartite square (white vertices `{0, 2}` have `+1`, black vertices `{1, 3}`
have `-1`). -/
def bipartiteChiralityMat : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1]]

/-- Signed Kasteleyn–Dirac adjacency matrix of the 4-vertex bipartite square
with edge signs `(+1, +1, +1, -1)`:
white-to-black edges `(0,1): +1`, `(2,1): +1`, `(2,3): +1`, `(0,3): -1`
and symmetric black-to-white edges. -/
def kasteleynDiracMat : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![0, 1, 0, -1], ![1, 0, 1, 0], ![0, 1, 0, 1], ![-1, 0, 1, 0]]

/-- Klein-bottle glide-seam swap involution on the 4-vertex square, exchanging
white ↔ black (`0 ↔ 1`, `2 ↔ 3`) with the orientation-reversing sign on the
seam edge. -/
def kleinSeamMat : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, -1, 0]]

theorem bipartiteChiralityMat_sq :
    bipartiteChiralityMat * bipartiteChiralityMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bipartiteChiralityMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem kleinSeamMat_sq :
    kleinSeamMat * kleinSeamMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kleinSeamMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

/-- The Kasteleyn–Dirac operator is strictly odd under the bipartite chirality
grading: `γ * D = -(D * γ)`. -/
theorem kasteleynDirac_anticommutes_chirality :
    bipartiteChiralityMat * kasteleynDiracMat =
      -(kasteleynDiracMat * bipartiteChiralityMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bipartiteChiralityMat, kasteleynDiracMat, Matrix.mul_apply, Fin.sum_univ_four]

/-- **Kasteleyn square-gap theorem**: because the 4-face edge-sign product is
`-1`, all off-diagonal 2-step paths cancel identically, giving `D² = 2 • I₄`. -/
theorem kasteleynDirac_sq_eq_two_one :
    kasteleynDiracMat * kasteleynDiracMat = (2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kasteleynDiracMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

/-- The Klein-bottle seam involution reverses the bipartite chirality grading:
`S * γ * S = -γ`. -/
theorem kleinSeam_conjugates_chirality :
    kleinSeamMat * bipartiteChiralityMat * kleinSeamMat = -bipartiteChiralityMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kleinSeamMat, bipartiteChiralityMat, Matrix.mul_apply, Fin.sum_univ_four]

/-- Explicit non-commutativity witness on `Matrix (Fin 4) (Fin 4) ℝ`:
the bipartite chirality and Kasteleyn–Dirac operator do not commute. -/
theorem bipartiteChirality_kasteleynDirac_noncomm :
    bipartiteChiralityMat * kasteleynDiracMat ≠
      kasteleynDiracMat * bipartiteChiralityMat := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [bipartiteChiralityMat, kasteleynDiracMat, Matrix.mul_apply, Fin.sum_univ_four] at h01

/-- Order-2 ring automorphism of `Matrix (Fin 4) (Fin 4) ℝ` induced by
conjugation by the Klein-bottle seam involution `kleinSeamMat`. -/
def kleinSeamConjAut : Matrix (Fin 4) (Fin 4) ℝ ≃+* Matrix (Fin 4) (Fin 4) ℝ :=
  involutionConjAut kleinSeamMat kleinSeamMat_sq

/-- **Pullback into `KleinBottleTwistedCommutantBridge`**:
both `kleinSeamMat` and `kasteleynDiracMat` lie in the `kleinSeamConjAut`-twisted
commutant of `{bipartiteChiralityMat}`, while their square lies in the ordinary
commutant. -/
theorem kasteleynDirac_mem_klein_twistedCommutant :
    kasteleynDiracMat ∈
      twistedCommutant ({bipartiteChiralityMat} : Set (Matrix (Fin 4) (Fin 4) ℝ))
        kleinSeamConjAut := by
  intro a ha
  rcases Set.mem_singleton_iff.mp ha with rfl
  change kasteleynDiracMat * bipartiteChiralityMat =
    (kleinSeamMat * bipartiteChiralityMat * kleinSeamMat) * kasteleynDiracMat
  rw [kleinSeam_conjugates_chirality, neg_mul, kasteleynDirac_anticommutes_chirality, neg_neg]

theorem kasteleynDirac_sq_mem_ordinaryCommutant :
    kasteleynDiracMat * kasteleynDiracMat ∈
      ordinaryCommutant ({bipartiteChiralityMat} : Set (Matrix (Fin 4) (Fin 4) ℝ)) := by
  intro a ha
  rcases Set.mem_singleton_iff.mp ha with rfl
  rw [kasteleynDirac_sq_eq_two_one]
  simp

/-! ## 4. Intertwining with `Cl(1,1)` CPT grading, bipartite Dirac, plabic mutation, and `SignedPerm` -/

/-- The `2 × 2` real chirality matrix `β_R = diag(1, -1)` realizing the CPT
bivector `B = e₀ e₁` in `Cl(1,1) ≅ Mat₂(ℝ)`. -/
def cptBeta2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1, 0], ![0, -1]]

/-- The `2 × 2` real bipartite hopping matrix `D_R = [[0, 1], [1, 0]]` in
`Cl(1,1) ≅ Mat₂(ℝ)`. -/
def cptHop2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![0, 1], ![1, 0]]

theorem cptBeta2_sq : cptBeta2 * cptBeta2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cptBeta2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem cptBeta2_anticommutes_cptHop2 :
    cptBeta2 * cptHop2 + cptHop2 * cptBeta2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cptBeta2, cptHop2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem cptBeta2_cptHop2_noncomm :
    cptBeta2 * cptHop2 ≠ cptHop2 * cptBeta2 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [cptBeta2, cptHop2, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Plugging `(cptBeta2, cptHop2)` into `Cl11BipartiteDiracBridge.compositeDirac`
satisfies the decoupled bipartite square law for every left operator `DL`. -/
theorem cpt_bipartite_compositeDirac_sq_decoupled (DL : StageOne) :
    compositeDirac DL cptBeta2 cptHop2 * compositeDirac DL cptBeta2 cptHop2 =
      (DL * DL) ⊗ₖ (1 : Atom) + (1 : StageOne) ⊗ₖ (cptHop2 * cptHop2) := by
  exact compositeDirac_sq_decoupled DL cptBeta2 cptHop2 cptBeta2_sq cptBeta2_anticommutes_cptHop2

/-- The Klein-bottle seam chirality swap as an explicit element of the
hyperoctahedral group `SignedPerm 1 = FlipGroup 1 ⋊ S_1`. -/
def kleinSeamSignedPerm : SignedPerm 1 :=
  SemidirectProduct.inl (fun _ => Multiplicative.ofAdd (1 : ZMod 2))

theorem kleinSeamSignedPerm_sq :
    kleinSeamSignedPerm * kleinSeamSignedPerm = 1 := by
  ext i
  · change Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1
    rw [← ofAdd_add]
    have h : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h]
    rfl
  · rfl

/-- Under `instSignedPermAction`, `kleinSeamSignedPerm` swaps `KreinSector.plus`
and `KreinSector.minus` while preserving the Boolean lattice operations
(`signedPerm_meet`, `signedPerm_sup`, `signedPerm_compl`). -/
theorem kleinSeamSignedPerm_swaps_plus_minus :
    (kleinSeamSignedPerm • (fun _ : Fin 1 => KreinSector.plus)) =
        (fun _ : Fin 1 => KreinSector.minus) ∧
      (kleinSeamSignedPerm • (fun _ : Fin 1 => KreinSector.minus)) =
        (fun _ : Fin 1 => KreinSector.plus) := by
  constructor <;> (funext i; fin_cases i; decide)

/-! ## 5. Master Unification Theorem -/

/-- **Klein–Plabic–Bipartite–CPT Twist Unification**:
unites all five repository owners through explicit, type-preserving maps and
identities (no false group equalities):
1. Klein-bottle glide $G^2 = T_x$ (`WallpaperSymmetry`) and bipartite color flip
   (`integralGlide_flips_color`), together with the square-grid Kasteleyn face
   law and the glide's edgewise vertex-gauge twist.
2. The finite Kasteleyn square's odd-parity face product `-1` and mass-gap
   square `D² = 2 • I₄`.
3. Pullback of `kasteleynDiracMat` into `KleinBottleTwistedCommutantBridge.twistedCommutant`
   under the order-2 seam automorphism `kleinSeamConjAut`.
4. CPT `Cl(1,1)` bipartite Dirac decoupling (`Cl11BipartiteDiracBridge`) and
   hyperoctahedral `SignedPerm 1` chirality swap (`FiniteOperatorBooleanAlgebra`).
5. Postnikov plabic square-move involution (`CantorPlabicTwistorBridge`). -/
theorem klein_plabic_bipartite_cpt_unification
    (p : Lattice2D) (q : ℤ × ℤ) (DL : StageOne)
    (M : Matrix (Fin 2) (Fin 4) ℝ)
    (s : InfoGeometry.PlabicCluster.SquareFaceWeights ℝ)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4)) :
    (G (G p) = T_x p) ∧
    (latticeColor (integralGlide q) = !(latticeColor q)) ∧
    (∀ u v, squareLattice_unitFace_sign_product u v) ∧
    (∀ e, integralGlideEdge_kasteleyn_gauge_law e) ∧
    (kasteleynEdgeSigns 0 * kasteleynEdgeSigns 1 *
      kasteleynEdgeSigns 2 * kasteleynEdgeSigns 3 = -1) ∧
    (kasteleynDiracMat * kasteleynDiracMat = (2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) ∧
    (kasteleynDiracMat ∈
      twistedCommutant ({bipartiteChiralityMat} : Set (Matrix (Fin 4) (Fin 4) ℝ))
        kleinSeamConjAut) ∧
    (compositeDirac DL cptBeta2 cptHop2 * compositeDirac DL cptBeta2 cptHop2 =
      (DL * DL) ⊗ₖ (1 : Atom) + (1 : StageOne) ⊗ₖ (cptHop2 * cptHop2)) ∧
    (kleinSeamSignedPerm * kleinSeamSignedPerm = 1) ∧
    (InfoGeometry.PlabicCluster.mutateF_rev
      (InfoGeometry.PlabicCluster.mutateF (cantorSquareSeed M s)) =
      cantorSquareSeed M s) :=
  ⟨glide_squared_eq_x_translation p,
   integralGlide_flips_color q,
   squareLattice_unitFace_sign_product,
   integralGlideEdge_kasteleyn_gauge_law,
   kasteleyn_face_product_eq_neg_one,
   kasteleynDirac_sq_eq_two_one,
   kasteleynDirac_mem_klein_twistedCommutant,
   cpt_bipartite_compositeDirac_sq_decoupled DL,
   kleinSeamSignedPerm_sq,
   cantor_square_mutation_involutive M s hM⟩

end InfoGeometry.Canonical.KleinPlabicBipartiteCPTTwistUnification
