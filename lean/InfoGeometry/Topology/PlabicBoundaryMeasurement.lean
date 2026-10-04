
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Topology.AmplituhedronGeneralTwistorExpansion
import Mathlib.Tactic

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

theorem plucker_01 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1 = t₂ := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

theorem plucker_02 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 2 = 1 := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

theorem plucker_03 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3 = t₃ := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

theorem plucker_12 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2 = t₁ := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

theorem plucker_13 (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 = t₁ * t₃ + t₂ * t₄ := by
  dsimp [minor2, boundaryMeasurementMatrix]
  ring

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

/-- Total Positivity Preservation Theorem under Cluster Mutation:
    If all seed Plücker coordinates are strictly positive, the mutated coordinate
    produced by the square move / urban renewal is strictly positive. -/
theorem mutatePlucker_pos {Δ_a Δ_b Δ_c Δ_d Δ_orig : ℝ}
    (ha : 0 < Δ_a) (hb : 0 < Δ_b) (hc : 0 < Δ_c) (hd : 0 < Δ_d) (h_orig : 0 < Δ_orig) :
    0 < mutatePlucker Δ_a Δ_b Δ_c Δ_d Δ_orig := by
  dsimp [mutatePlucker]
  have h_num1 : 0 < Δ_a * Δ_b := mul_pos ha hb
  have h_num2 : 0 < Δ_c * Δ_d := mul_pos hc hd
  have h_sum : 0 < Δ_a * Δ_b + Δ_c * Δ_d := add_pos h_num1 h_num2
  exact div_pos h_sum h_orig

end PlabicBoundaryMeasurement
