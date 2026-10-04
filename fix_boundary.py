import subprocess

lean_code = """
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Matrix
open scoped Matrix

namespace PlabicBoundaryMeasurement

variable {n : ℕ} {R : Type*} [CommRing R]

/-! ### 1. 2x2 Plücker Minors and Fundamental Symmetries -/

/-- The 2x2 Plücker coordinate of columns a and b of a 2 x n matrix C:
    Δ_{a, b}(C) = C_{0, a} C_{1, b} - C_{1, a} C_{0, b}. -/
def minor2 (C : Matrix (Fin 2) (Fin n) R) (a b : Fin n) : R :=
  C 0 a * C 1 b - C 1 a * C 0 b

/-- Skew-symmetry of Plücker coordinates: Δ_{b, a} = - Δ_{a, b}. -/
theorem minor2_skew (C : Matrix (Fin 2) (Fin n) R) (a b : Fin n) :
    minor2 C b a = - minor2 C a b := by
  dsimp [minor2]
  ring

/-- Diagonal vanishing: Δ_{a, a} = 0. -/
theorem minor2_self (C : Matrix (Fin 2) (Fin n) R) (a : Fin n) :
    minor2 C a a = 0 := by
  dsimp [minor2]
  ring

/-- The Universal 3-Term Grassmann-Plücker Relation in Gr(2, n):
    Δ_{a, c} Δ_{b, d} = Δ_{a, b} Δ_{c, d} + Δ_{a, d} Δ_{b, c}. -/
theorem plucker_relation_general (C : Matrix (Fin 2) (Fin n) R) (a b c d : Fin n) :
    minor2 C a c * minor2 C b d =
      minor2 C a b * minor2 C c d + minor2 C a d * minor2 C b c := by
  dsimp [minor2]
  ring

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

/-! ### 3. Canonical Postnikov Boundary Measurement Matrix for Gr(2, 4) -/

/-- Postnikov's canonical boundary measurement matrix in Gr(2, 4)
    parameterized by positive face/edge weights (t₁, t₂, t₃, t₄) > 0. -/
def boundaryMeasurementMatrix (t₁ t₂ t₃ t₄ : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  !![1, t₁, 0, -t₄;
     0, t₂, 1,  t₃]

/-! ### 4. Exact Evaluation of All Plücker Coordinates -/

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

/-! ### 5. Total Positivity of the Amplituhedron Cell -/

/-- Predicate for strict total positivity in Gr(2, 4):
    Every Plücker coordinate of an increasing pair of indices is strictly positive. -/
def IsTotallyPositive24 (C : Matrix (Fin 2) (Fin 4) ℝ) : Prop :=
  0 < minor2 C 0 1 ∧
  0 < minor2 C 0 2 ∧
  0 < minor2 C 0 3 ∧
  0 < minor2 C 1 2 ∧
  0 < minor2 C 1 3 ∧
  0 < minor2 C 2 3

/-- Master Theorem: The Boundary Measurement Map sends any positive network weights
    (t₁, t₂, t₃, t₄) > 0 to a strictly totally positive matrix in Gr_{>0}(2, 4). -/
theorem boundaryMeasurement_totally_positive {t₁ t₂ t₃ t₄ : ℝ}
    (h1 : 0 < t₁) (h2 : 0 < t₂) (h3 : 0 < t₃) (h4 : 0 < t₄) :
    IsTotallyPositive24 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) := by
  dsimp [IsTotallyPositive24]
  rw [plucker_01, plucker_02, plucker_03, plucker_12, plucker_13, plucker_23]
  refine ⟨h2, zero_lt_one, h3, h1, ?_, h4⟩
  have h13 : 0 < t₁ * t₃ := mul_pos h1 h3
  have h24 : 0 < t₂ * t₄ := mul_pos h2 h4
  exact add_pos h13 h24

/-! ### 6. Cluster Mutation Exchange on the Boundary Measurement Cell -/

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

/-- Cluster Mutation of a Plücker coordinate via the exchange relation:
    Δ'_mut = (Δ_a * Δ_b + Δ_c * Δ_d) / Δ_orig. -/
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
"""
with open("lean/InfoGeometry/Topology/PlabicBoundaryMeasurement.lean", "w") as f:
    f.write(lean_code)

res = subprocess.run(["lake", "env", "lean", "lean/InfoGeometry/Topology/PlabicBoundaryMeasurement.lean"], capture_output=True, text=True)
if res.returncode == 0:
    subprocess.run(["sed", "-i", "2iimport InfoGeometry.Topology.PlabicBoundaryMeasurement", "lean/InfoGeometry/Topology/All.lean"])
    subprocess.run(["git", "add", "lean/InfoGeometry/Topology/PlabicBoundaryMeasurement.lean", "lean/InfoGeometry/Topology/All.lean"])
    subprocess.run(["git", "commit", "-m", "feat(Topology): Formalize Plabic Boundary Measurement Total Positivity"])
print(res.stdout)
