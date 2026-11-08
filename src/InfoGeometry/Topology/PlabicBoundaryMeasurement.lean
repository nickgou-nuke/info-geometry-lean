/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Topology.AmplituhedronGeneralTwistorExpansion
import InfoGeometry.Topology.PlabicCluster
import Mathlib.Tactic

/-!
# Plabic Boundary Measurement & Unipotent Bridge Addition on `Gr(2,4)`

## i. Overview
Formalizes elementary unipotent boundary-bridge additions on $2 \times n$ matrices,
their multilinear Plücker minor expansions, and the four-parameter positive chart
`boundaryMeasurementMatrix` on $\mathrm{Gr}_+(2,4)$.

## ii. Key results
- `minor2_addBridge_of_ne`, `minor2_addBridge_right`, `minor2_addBridge_left`
- `plucker_01`, `plucker_02`, `plucker_03`, `plucker_12`, `plucker_13`, `plucker_23`
- `boundaryMeasurement_plucker_13_eq_two_route_readout` & `boundaryMeasurement_plucker_13_eq_diamond_readout`

## iii. Table of contents
- Elementary unipotent boundary bridge additions
- Positive `Gr(2,4)` boundary measurement matrix and six Plücker minors
- Two-route and diamond DAG Green-function readouts

## iv. References
- Alexander Postnikov, *Total positivity, Grassmannians, and networks* (2006)

#### BUCKET 1 — Proved Kernel Content
- `minor2_addBridge_of_ne`, `minor2_addBridge_right`, `minor2_addBridge_left`
- `plucker_01`, `plucker_02`, `plucker_03`, `plucker_12`, `plucker_13`, `plucker_23`
- `boundaryMeasurement_plucker_13_eq_two_route_readout` & `boundaryMeasurement_plucker_13_eq_diamond_readout`

#### BUCKET 2 — Conditional / Interface Boundaries
- Positivity theorems hold under explicit `0 < tᵢ` parameter hypotheses.

#### BUCKET 3 — Open / Unformalized
- General `Gr(k,n)` plabic graph move equivalence is outside this `Gr(2,4)` chart owner.
-/

open Matrix
open scoped Matrix
open InfoGeometry.Amplituhedron

namespace PlabicBoundaryMeasurement

variable {n : ℕ} {R : Type*} [CommRing R]

/-! ### 2. Boundary Bridge Addition (Elementary Unipotent Shears) -/

/-- Boundary Bridge Addition:
    Adds an on-shell bridge from boundary strand j to i with positive weight t,
    mapping column i to (c_i + t * c_j). -/
def addBridge (C : Matrix (Fin 2) (Fin n) R) (i j : Fin n) (t : R) :
    Matrix (Fin 2) (Fin n) R :=
  fun r c => if c = i then C r i + t * C r j else C r c

/-- Bridge Invariance: Minors of columns disjoint from the bridge target i are unchanged. -/
theorem minor2_addBridge_of_ne (C : Matrix (Fin 2) (Fin n) R) (i j a b : Fin n) (t : R)
    (ha : a ≠ i) (hb : b ≠ i) :
    minor2 (addBridge C i j t) a b = minor2 C a b := by
  dsimp [minor2, addBridge]
  rw [if_neg ha, if_neg ha, if_neg hb, if_neg hb]

/-- Multilinear Bridge Expansion (Right Column):
    Δ_{a, i}(C') = Δ_{a, i}(C) + t * Δ_{a, j}(C). -/
theorem minor2_addBridge_right (C : Matrix (Fin 2) (Fin n) R) (i j a : Fin n) (t : R)
    (ha : a ≠ i) :
    minor2 (addBridge C i j t) a i = minor2 C a i + t * minor2 C a j := by
  dsimp [minor2, addBridge]
  rw [if_neg ha, if_neg ha, if_pos rfl, if_pos rfl]
  ring

/-- Multilinear Bridge Expansion (Left Column):
    Δ_{i, b}(C') = Δ_{i, b}(C) + t * Δ_{j, b}(C). -/
theorem minor2_addBridge_left (C : Matrix (Fin 2) (Fin n) R) (i j b : Fin n) (t : R)
    (hb : b ≠ i) :
    minor2 (addBridge C i j t) i b = minor2 C i b + t * minor2 C j b := by
  dsimp [minor2, addBridge]
  rw [if_pos rfl, if_pos rfl, if_neg hb, if_neg hb]
  ring

/-- Non-Negativity Preservation under Positive Bridge Addition:
    If the original minors are non-negative and the bridge weight t ≥ 0,
    the updated boundary measurement minor is non-negative. -/
theorem minor2_addBridge_right_nonneg (C : Matrix (Fin 2) (Fin n) ℝ) (i j a : Fin n) (t : ℝ)
    (ha : a ≠ i)
    (h_ai : 0 ≤ minor2 C a i) (h_aj : 0 ≤ minor2 C a j) (ht : 0 ≤ t) :
    0 ≤ minor2 (addBridge C i j t) a i := by
  rw [minor2_addBridge_right C i j a t ha]
  have : 0 ≤ t * minor2 C a j := mul_nonneg ht h_aj
  linarith

/-! ### 3. An Explicit Positive Matrix Family in Gr(2, 4)

This file specifies a four-parameter matrix family and proves positivity of
its ordered maximal minors.  No planar network or graph measurement map is
specified here, so the family is not identified with a particular plabic
network's boundary measurement.
-/

/-- An explicit `2 × 4` matrix family parameterized by four real numbers. -/
def boundaryMeasurementMatrix (t₁ t₂ t₃ t₄ : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  !![1, t₁, 0, -t₄;
     0, t₂, 1,  t₃]

/-! ### 4. Exact Evaluation of Its Plücker Coordinates -/

/-- The `(0, 1)` Plücker minor of `boundaryMeasurementMatrix t₁ t₂ t₃ t₄` equals `t₂`. -/
theorem plucker_01 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1 = t₂ := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

/-- The `(0, 2)` Plücker minor of `boundaryMeasurementMatrix t₁ t₂ t₃ t₄` equals `1`. -/
theorem plucker_02 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 2 = 1 := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

/-- The `(0, 3)` Plücker minor of `boundaryMeasurementMatrix t₁ t₂ t₃ t₄` equals `t₃`. -/
theorem plucker_03 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3 = t₃ := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

/-- The `(1, 2)` Plücker minor of `boundaryMeasurementMatrix t₁ t₂ t₃ t₄` equals `t₁`. -/
theorem plucker_12 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2 = t₁ := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

/-- The `(1, 3)` Plücker minor of `boundaryMeasurementMatrix t₁ t₂ t₃ t₄` equals `t₁ * t₃ + t₂ * t₄`. -/
theorem plucker_13 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 = t₁ * t₃ + t₂ * t₄ := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

/-- A three-vertex acyclic weighted network with a direct route of weight
`t₂ * t₄` and a two-edge route of weight `t₁ * t₃`. Its adjacency matrix is
strictly upper triangular, so its finite path-sum matrix is `I + W + W²`. -/
def chartTwoRouteAdjacency (t₁ t₂ t₃ t₄ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, t₁, t₂ * t₄;
     0, 0, t₃;
     0, 0, 0]

/-- The finite path-sum matrix of `chartTwoRouteAdjacency`: the `(0,2)` entry
is the sum of its direct route and its unique two-edge route. -/
def chartTwoRouteGreen (t₁ t₂ t₃ t₄ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, t₁, t₁ * t₃ + t₂ * t₄;
     0, 1, t₃;
     0, 0, 1]

/-- The Green matrix is the exact finite path sum `I + W + W²` for this DAG. -/
theorem chartTwoRouteGreen_eq_path_sum (t₁ t₂ t₃ t₄ : ℝ) :
    chartTwoRouteGreen t₁ t₂ t₃ t₄ =
      1 + chartTwoRouteAdjacency t₁ t₂ t₃ t₄ +
        chartTwoRouteAdjacency t₁ t₂ t₃ t₄ ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [chartTwoRouteGreen, chartTwoRouteAdjacency, pow_two]
  all_goals ring

/-- The `Δ₁₃` minor of the positive `Gr(2,4)` chart is the `(0,2)` entry of
the finite path-sum matrix of `chartTwoRouteAdjacency`. This is a chart-to-DAG
identity; the DAG here is not asserted to be a planar plabic network. -/
theorem boundaryMeasurement_plucker_13_eq_two_route_readout
    (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 =
      chartTwoRouteGreen t₁ t₂ t₃ t₄ 0 2 := by
  rw [plucker_13]
  rfl

/-- The same finite path-sum matrix is a two-sided inverse of `I - W`, giving
the usual terminating resolvent identity for this acyclic three-vertex model. -/
theorem chartTwoRouteGreen_is_resolvent (t₁ t₂ t₃ t₄ : ℝ) :
    (1 - chartTwoRouteAdjacency t₁ t₂ t₃ t₄) *
        chartTwoRouteGreen t₁ t₂ t₃ t₄ = 1 ∧
      chartTwoRouteGreen t₁ t₂ t₃ t₄ *
        (1 - chartTwoRouteAdjacency t₁ t₂ t₃ t₄) = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [chartTwoRouteGreen, chartTwoRouteAdjacency, Matrix.mul_apply,
      Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_three]

/-- A four-vertex diamond DAG with two distinct source-to-sink routes.
The route weights are `t₁ * t₃` and `t₂ * t₄`, matching the two terms in
the `Δ₁₃` boundary-channel decomposition. -/
def chartDiamondAdjacency (t₁ t₂ t₃ t₄ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, t₁, t₂, 0;
     0, 0, 0, t₃;
     0, 0, 0, t₄;
     0, 0, 0, 0]

/-- The path-sum matrix for the diamond DAG. Since all directed paths have
length at most two, the sum terminates at `I + W + W²`. -/
def chartDiamondGreen (t₁ t₂ t₃ t₄ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, t₁, t₂, t₁ * t₃ + t₂ * t₄;
     0, 1, 0, t₃;
     0, 0, 1, t₄;
     0, 0, 0, 1]

/-- The `(0,3)` readout adds the weights of the two distinct directed routes. -/
theorem chartDiamondGreen_eq_path_sum (t₁ t₂ t₃ t₄ : ℝ) :
    chartDiamondGreen t₁ t₂ t₃ t₄ =
      1 + chartDiamondAdjacency t₁ t₂ t₃ t₄ +
        chartDiamondAdjacency t₁ t₂ t₃ t₄ ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [chartDiamondGreen, chartDiamondAdjacency, pow_two]
  all_goals ring

/-- In the four-vertex network, the `Δ₁₃` chart coordinate is the sum of the
two actual source-to-sink path weights, without compressing either route into
a single edge. -/
theorem boundaryMeasurement_plucker_13_eq_diamond_readout
    (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 =
      chartDiamondGreen t₁ t₂ t₃ t₄ 0 3 := by
  rw [plucker_13]
  rfl

/-- The `(2, 3)` Plücker minor of `boundaryMeasurementMatrix t₁ t₂ t₃ t₄` equals `t₄`. -/
theorem plucker_23 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 2 3 = t₄ := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

/-- Positive parameters make all six ordered maximal minors of this matrix
    family strictly positive. -/
theorem boundaryMeasurement_totally_positive {t₁ t₂ t₃ t₄ : ℝ}
    (h1 : 0 < t₁) (h2 : 0 < t₂) (h3 : 0 < t₃) (h4 : 0 < t₄) :
    IsTotallyPositive24 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) := by
  dsimp [IsTotallyPositive24]
  rw [plucker_01, plucker_02, plucker_03, plucker_12, plucker_13, plucker_23]
  refine ⟨h2, zero_lt_one, h3, h1, ?_, h4⟩
  have h13 : 0 < t₁ * t₃ := mul_pos h1 h3
  have h24 : 0 < t₂ * t₄ := mul_pos h2 h4
  exact add_pos h13 h24

/-! ### 6. The Plücker Relation for This Matrix Family -/

/-- The 3-term Grassmann-Plücker identity satisfied by the boundary measurement matrix:
    Δ₀₂ * Δ₁₃ = Δ₀₁ * Δ₂₃ + Δ₀₃ * Δ₁₂. -/
theorem boundaryMeasurement_plucker_relation (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 2 *
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 =
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1 *
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 2 3 +
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3 *
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2 := by
  rw [plucker_02, plucker_13, plucker_01, plucker_23, plucker_03, plucker_12]
  ring

/-- The rational exchange expression associated with the three-term Plücker
    relation.  This definition alone does not assert a cluster mutation. -/
noncomputable def mutatePlucker (Δ_a Δ_b Δ_c Δ_d Δ_orig : ℝ) : ℝ :=
  (Δ_a * Δ_b + Δ_c * Δ_d) / Δ_orig

/-- On a `2 × 4` matrix, the rational exchange expression is exactly the
remaining Plücker minor whenever the denominator minor is nonzero.  This is the
matrix-level exchange identity; it does not identify the matrix operation with
a graph square move. -/
theorem mutatePlucker_eq_minor2_of_plucker_relation
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (h02 : minor2 C 0 2 ≠ 0) :
    mutatePlucker (minor2 C 0 1) (minor2 C 2 3)
        (minor2 C 0 3) (minor2 C 1 2) (minor2 C 0 2) =
      minor2 C 1 3 := by
  dsimp [mutatePlucker]
  rw [div_eq_iff h02]
  simpa [mul_comm] using
    (InfoGeometry.Amplituhedron.plucker_relation_general C 0 1 2 3).symm

/-- For the explicit positive matrix family, the exchange formula recovers
the `Δ₁₃` coordinate from the other five minors. -/
theorem boundaryMeasurement_mutatePlucker_eq_plucker_13
    (t₁ t₂ t₃ t₄ : ℝ) :
    mutatePlucker
        (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1)
        (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 2 3)
        (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3)
        (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2)
        (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 2) =
      minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 := by
  apply mutatePlucker_eq_minor2_of_plucker_relation
  rw [plucker_02]
  norm_num

/-- The positive `Gr(2,4)` matrix chart induces the corresponding cluster face
coordinate: the normalized sum of the opposite Plücker products is the
normalized `Δ₁₃` coordinate.  This connects the matrix chart to the abstract
Ptolemy face-weight formula; it does not identify the chart with a graph. -/
theorem boundaryMeasurement_cluster_face_weight_readout
    {t₁ t₂ t₃ t₄ : ℝ}
    (h1 : 0 < t₁) (h2 : 0 < t₂) (h3 : 0 < t₃) (h4 : 0 < t₄) :
    1 +
      (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1 *
        minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 2 3) *
        (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3 *
          minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2)⁻¹ =
      minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 *
        (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3 *
          minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2)⁻¹ ∧
    0 < minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 := by
  have h_denom :
      minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3 *
        minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2 ≠ 0 := by
    rw [plucker_03, plucker_12]
    exact ne_of_gt (mul_pos h3 h1)
  refine ⟨?_, ?_⟩
  · simpa only [plucker_02, one_mul] using
    (InfoGeometry.PlabicCluster.ptolemy_face_weight_add_one
    (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 2)
    (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3)
    (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1)
    (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3)
    (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 2 3)
    (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2)
    (by
      simpa [plucker_02] using
        boundaryMeasurement_plucker_relation t₁ t₂ t₃ t₄)
    h_denom)
  · rw [plucker_13]
    exact add_pos (mul_pos h1 h3) (mul_pos h2 h4)

/-- Positivity of the rational exchange expression when its four numerator
    coordinates and denominator are positive.  Identifying this expression
    with a graph square move requires a separate boundary-measurement theorem. -/
theorem mutatePlucker_pos {Δ_a Δ_b Δ_c Δ_d Δ_orig : ℝ}
    (ha : 0 < Δ_a) (hb : 0 < Δ_b) (hc : 0 < Δ_c) (hd : 0 < Δ_d) (h_orig : 0 < Δ_orig) :
    0 < mutatePlucker Δ_a Δ_b Δ_c Δ_d Δ_orig := by
  dsimp [mutatePlucker]
  have h_num1 : 0 < Δ_a * Δ_b := mul_pos ha hb
  have h_num2 : 0 < Δ_c * Δ_d := mul_pos hc hd
  have h_sum : 0 < Δ_a * Δ_b + Δ_c * Δ_d := add_pos h_num1 h_num2
  exact div_pos h_sum h_orig

end PlabicBoundaryMeasurement

namespace PlabicBoundaryMeasurement

/-! ### 7. Lie Bracket and Commutator Algebra -/

/-- The Lie bracket [x, y] = x * y - y * x in an associative ring A. -/
def lieBracket {A : Type*} [Ring A] (x y : A) : A :=
  x * y - y * x

/-- Every ring element commutes with itself under `lieBracket`. -/
@[simp] theorem lieBracket_self {A : Type*} [Ring A] (x : A) :
    lieBracket x x = 0 := by
  dsimp [lieBracket]
  abel

/-- The ring commutator `lieBracket` is antisymmetric. -/
theorem lieBracket_antisymm {A : Type*} [Ring A] (x y : A) :
    lieBracket x y = - lieBracket y x := by
  dsimp [lieBracket]
  abel

/-- The ring commutator `lieBracket` is additive in its left argument. -/
theorem lieBracket_add_left {A : Type*} [Ring A] (x y z : A) :
    lieBracket (x + y) z = lieBracket x z + lieBracket y z := by
  dsimp [lieBracket]
  rw [add_mul, mul_add]
  abel

/-- The ring commutator `lieBracket` is additive in its right argument. -/
theorem lieBracket_add_right {A : Type*} [Ring A] (x y z : A) :
    lieBracket x (y + z) = lieBracket x y + lieBracket x z := by
  dsimp [lieBracket]
  rw [mul_add, add_mul]
  abel

/-! ### 8. Elementary Plabic Strand Crossing -/

/-- An elementary 2-strand crossing inside a plabic graph.
    Two incoming strands with charges `inA, inB` cross and exit with transposed
    charges `outA = inB` and `outB = inA`. -/
structure StrandCrossing (A : Type*) [Ring A] where
  inA : A
  inB : A

/-- Outgoing strand A charge after the crossing equals `inB`. -/
def StrandCrossing.outA {A : Type*} [Ring A] (c : StrandCrossing A) : A :=
  c.inB

/-- Outgoing strand B charge after the crossing equals `inA`. -/
def StrandCrossing.outB {A : Type*} [Ring A] (c : StrandCrossing A) : A :=
  c.inA

/-- Master Theorem 1A (Local Level-0 Conservation across Crossing):
    Total flux is conserved at the strand crossing: inA + inB = outA + outB. -/
theorem strand_crossing_level0 {A : Type*} [Ring A] (c : StrandCrossing A) :
    c.inA + c.inB = c.outA + c.outB := by
  dsimp [StrandCrossing.outA, StrandCrossing.outB]
  abel

/-- Master Theorem 1B (Local Level-1 Invariance across Crossing):
    The Lie commutator is preserved up to topological orientation swap. -/
theorem strand_crossing_level1 {A : Type*} [Ring A] (c : StrandCrossing A) :
    lieBracket c.outA c.outB = - lieBracket c.inA c.inB := by
  dsimp [StrandCrossing.outA, StrandCrossing.outB]
  exact lieBracket_antisymm c.inB c.inA

/-! ### 9. 3-Point Boundary Strand Flow (The Triangle Face) -/

/-- Cyclic shift on 3 boundary strands: 0 ↦ 1, 1 ↦ 2, 2 ↦ 0. -/
def cyclicShift3 (i : Fin 3) : Fin 3 :=
  match i with
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- Level-0 total charge for 3 boundary strands. -/
def level0_3 {A : Type*} [Ring A] (E : Fin 3 → A) : A :=
  E 0 + E 1 + E 2

/-- Level-1 bilocal Yangian charge for 3 boundary strands:
    J^{(1)} = [E₀, E₁] + [E₀, E₂] + [E₁, E₂]. -/
def level1_3 {A : Type*} [Ring A] (E : Fin 3 → A) : A :=
  lieBracket (E 0) (E 1) + lieBracket (E 0) (E 2) + lieBracket (E 1) (E 2)

/-- Master Theorem 2 (Cyclic Invariance of 3-Point Yangian Level-1):
    On the Level-0 shell (level0_3 E = 0), the Level-1 Yangian charge is
    strictly invariant under the cyclic flow of boundary strands. -/
theorem yangian_level1_cyclic_invariance_3 {A : Type*} [Ring A] (E : Fin 3 → A)
    (h_onShell : level0_3 E = 0) :
    level1_3 (E ∘ cyclicShift3) = level1_3 E := by
  dsimp [level1_3, cyclicShift3, level0_3, lieBracket] at *
  have h_sub : E 1 + E 2 = - E 0 := by
    calc E 1 + E 2 = - E 0 + (E 0 + E 1 + E 2) := by abel
      _ = - E 0 + 0 := by rw [h_onShell]
      _ = - E 0 := add_zero (- E 0)
  have h_dist : (E 1 + E 2) * E 0 - E 0 * (E 1 + E 2) = 0 := by
    rw [h_sub, neg_mul, mul_neg]
    abel
  have h_exp :
      (E 1 * E 2 - E 2 * E 1 + (E 1 * E 0 - E 0 * E 1) + (E 2 * E 0 - E 0 * E 2)) -
      (E 0 * E 1 - E 1 * E 0 + (E 0 * E 2 - E 2 * E 0) + (E 1 * E 2 - E 2 * E 1)) =
      ((E 1 + E 2) * E 0 - E 0 * (E 1 + E 2)) + ((E 1 + E 2) * E 0 - E 0 * (E 1 + E 2)) := by
    rw [add_mul, mul_add]
    abel
  rw [h_dist, add_zero] at h_exp
  exact sub_eq_zero.mp h_exp

/-! ### 10. 4-Point Boundary Strand Flow (The Amplituhedron Plabic Square Face) -/

/-- Cyclic shift on 4 boundary strands: 0 ↦ 1, 1 ↦ 2, 2 ↦ 3, 3 ↦ 0. -/
def cyclicShift4 (i : Fin 4) : Fin 4 :=
  match i with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 0

/-- Level-0 total charge for 4 boundary strands. -/
def level0_4 {A : Type*} [Ring A] (E : Fin 4 → A) : A :=
  E 0 + E 1 + E 2 + E 3

/-- Level-1 bilocal Yangian charge for 4 boundary strands:
    J^{(1)} = ∑_{0 ≤ i < j ≤ 3} [E_i, E_j]. -/
def level1_4 {A : Type*} [Ring A] (E : Fin 4 → A) : A :=
  lieBracket (E 0) (E 1) + lieBracket (E 0) (E 2) + lieBracket (E 0) (E 3) +
  lieBracket (E 1) (E 2) + lieBracket (E 1) (E 3) +
  lieBracket (E 2) (E 3)

/-- Master Theorem 3 (Cyclic Invariance of 4-Point Yangian Level-1):
    On the 4-point on-shell quadric (level0_4 E = 0), the bilocal Yangian generator
    is invariant under cyclic strand flow around the plabic square. -/
theorem yangian_level1_cyclic_invariance_4 {A : Type*} [Ring A] (E : Fin 4 → A)
    (h_onShell : level0_4 E = 0) :
    level1_4 (E ∘ cyclicShift4) = level1_4 E := by
  dsimp [level1_4, cyclicShift4, level0_4, lieBracket] at *
  have h_sub : E 1 + E 2 + E 3 = - E 0 := by
    calc E 1 + E 2 + E 3 = - E 0 + (E 0 + E 1 + E 2 + E 3) := by abel
      _ = - E 0 + 0 := by rw [h_onShell]
      _ = - E 0 := add_zero (- E 0)
  have h_dist : (E 1 + E 2 + E 3) * E 0 - E 0 * (E 1 + E 2 + E 3) = 0 := by
    rw [h_sub, neg_mul, mul_neg]
    abel
  have h_exp :
      (E 1 * E 2 - E 2 * E 1 + (E 1 * E 3 - E 3 * E 1) + (E 1 * E 0 - E 0 * E 1) + (E 2 * E 3 - E 3 * E 2) + (E 2 * E 0 - E 0 * E 2) + (E 3 * E 0 - E 0 * E 3)) -
      (E 0 * E 1 - E 1 * E 0 + (E 0 * E 2 - E 2 * E 0) + (E 0 * E 3 - E 3 * E 0) + (E 1 * E 2 - E 2 * E 1) + (E 1 * E 3 - E 3 * E 1) + (E 2 * E 3 - E 3 * E 2)) =
      ((E 1 + E 2 + E 3) * E 0 - E 0 * (E 1 + E 2 + E 3)) + ((E 1 + E 2 + E 3) * E 0 - E 0 * (E 1 + E 2 + E 3)) := by
    rw [add_mul, add_mul, mul_add, mul_add]
    abel
  rw [h_dist, add_zero] at h_exp
  exact sub_eq_zero.mp h_exp

/-! ### 11. Cyclic Nearest-Neighbor Boundary Flux -/

/-- Cyclic nearest-neighbor boundary flux on 4 strands:
    F_{cyclic} = [E₀, E₁] + [E₁, E₂] + [E₂, E₃] + [E₃, E₀]. -/
def cyclicFlux4 {A : Type*} [Ring A] (E : Fin 4 → A) : A :=
  lieBracket (E 0) (E 1) + lieBracket (E 1) (E 2) +
  lieBracket (E 2) (E 3) + lieBracket (E 3) (E 0)

/-- Master Theorem 4 (Unconditional Cyclic Invariance of Nearest-Neighbor Boundary Flux):
    The cyclic boundary contour flux is manifestly invariant under cyclic shift
    for any choice of strand charges, even off-shell. -/
theorem cyclicFlux4_shift_invariant {A : Type*} [Ring A] (E : Fin 4 → A) :
    cyclicFlux4 (E ∘ cyclicShift4) = cyclicFlux4 E := by
  dsimp [cyclicFlux4, cyclicShift4]
  abel

/-! ### 12. Plabic Square Move (Urban Renewal) -/

/-- A Plabic Square Move (Urban Renewal):
    Mutates a 4-face in the plabic network, rearranging the 4 internal strands. -/
structure PlabicSquareMove (A : Type*) [Ring A] where
  inCharges : Fin 4 → A
  outCharges : Fin 4 → A

/-- Theorem 5: If a square move conserves Level-0 flux and the incoming strand
    configuration is on-shell (level0 = 0), the outgoing mutated strand
    configuration is also on-shell. -/
theorem square_move_preserves_on_shell {A : Type*} [Ring A]
    (m : PlabicSquareMove A)
    (h_conservation : level0_4 m.inCharges = level0_4 m.outCharges)
    (h_in : level0_4 m.inCharges = 0) :
    level0_4 m.outCharges = 0 := by
  rw [← h_conservation]
  exact h_in

end PlabicBoundaryMeasurement
