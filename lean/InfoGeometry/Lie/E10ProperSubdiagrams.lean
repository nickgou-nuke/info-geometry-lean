import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Lie.E10LorentzianDecomposition

/-!
# E₁₀ Proper Connected Subdiagrams and Strict Hyperbolicity

To establish the strict hyperbolicity of E₁₀, we must verify that its proper
connected subdiagrams are either of finite type (positive definite) or affine
type (positive semidefinite). 

The maximal proper connected subdiagrams are obtained by removing a single leaf
node from the E₁₀ diagram. E₁₀ has three leaves: nodes 1, 3, and 9.
* Deleting node 1 leaves the finite A₉ diagram.
* Deleting node 3 leaves the finite D₉ diagram.
* Deleting node 9 leaves the affine E₈ diagram (also known as E₉).

Any other proper connected subdiagram is strictly contained in one of these three.
Deleting the central node 0 disconnects the graph into finite components 
(A₁ ⊕ A₂ ⊕ A₆), which are trivially positive definite as they are subdiagrams of A₉.

Here we explicitly construct the LDL^T sum-of-squares decompositions for the 
quadratic forms of A₉, D₉, and affine E₈ to formally prove their definiteness 
and identify the affine nullspace.
-/

namespace InfoGeometry.Lie.E10ProperSubdiagrams

open InfoGeometry.Lie.E10
open InfoGeometry.Lie.E10LorentzianDecomposition

/-! ## A₉ Subdiagram (Delete Node 1) -/
noncomputable def A9_b9 (x : Fin 10 → ℝ) : ℝ := x 9 - (1/2 : ℝ) * x 8
noncomputable def A9_b8 (x : Fin 10 → ℝ) : ℝ := x 8 - (2/3 : ℝ) * x 7
noncomputable def A9_b7 (x : Fin 10 → ℝ) : ℝ := x 7 - (3/4 : ℝ) * x 6
noncomputable def A9_b6 (x : Fin 10 → ℝ) : ℝ := x 6 - (4/5 : ℝ) * x 5
noncomputable def A9_b5 (x : Fin 10 → ℝ) : ℝ := x 5 - (5/6 : ℝ) * x 4
noncomputable def A9_b4 (x : Fin 10 → ℝ) : ℝ := x 4 - (6/7 : ℝ) * x 0
noncomputable def A9_b0 (x : Fin 10 → ℝ) : ℝ := x 0 - (7/8 : ℝ) * x 2
noncomputable def A9_b2 (x : Fin 10 → ℝ) : ℝ := x 2 - (8/9 : ℝ) * x 3
noncomputable def A9_b3 (x : Fin 10 → ℝ) : ℝ := x 3

theorem A9_form_eq (x : Fin 10 → ℝ) (h1 : x 1 = 0) :
    cartanQuadraticFormReal x = 
      2 * A9_b9 x ^ 2 +
      (3/2 : ℝ) * A9_b8 x ^ 2 +
      (4/3 : ℝ) * A9_b7 x ^ 2 +
      (5/4 : ℝ) * A9_b6 x ^ 2 +
      (6/5 : ℝ) * A9_b5 x ^ 2 +
      (7/6 : ℝ) * A9_b4 x ^ 2 +
      (8/7 : ℝ) * A9_b0 x ^ 2 +
      (9/8 : ℝ) * A9_b2 x ^ 2 +
      (10/9 : ℝ) * A9_b3 x ^ 2 := by
  rw [cartanQuadraticFormReal_eq_expanded]
  unfold A9_b9 A9_b8 A9_b7 A9_b6 A9_b5 A9_b4 A9_b0 A9_b2 A9_b3 cartanFormExpanded
  rw [h1]
  ring

theorem A9_positive_definite (x : Fin 10 → ℝ) (h1 : x 1 = 0) 
    (hq : cartanQuadraticFormReal x = 0) : ∀ i, x i = 0 := by
  have heq := A9_form_eq x h1
  rw [hq] at heq
  
  generalize hy9 : A9_b9 x = y9
  generalize hy8 : A9_b8 x = y8
  generalize hy7 : A9_b7 x = y7
  generalize hy6 : A9_b6 x = y6
  generalize hy5 : A9_b5 x = y5
  generalize hy4 : A9_b4 x = y4
  generalize hy0 : A9_b0 x = y0
  generalize hy2 : A9_b2 x = y2
  generalize hy3 : A9_b3 x = y3
  
  have p9 : 0 ≤ 2 * y9 ^ 2 := by positivity
  have p8 : 0 ≤ (3/2 : ℝ) * y8 ^ 2 := by positivity
  have p7 : 0 ≤ (4/3 : ℝ) * y7 ^ 2 := by positivity
  have p6 : 0 ≤ (5/4 : ℝ) * y6 ^ 2 := by positivity
  have p5 : 0 ≤ (6/5 : ℝ) * y5 ^ 2 := by positivity
  have p4 : 0 ≤ (7/6 : ℝ) * y4 ^ 2 := by positivity
  have p0 : 0 ≤ (8/7 : ℝ) * y0 ^ 2 := by positivity
  have p2 : 0 ≤ (9/8 : ℝ) * y2 ^ 2 := by positivity
  have p3 : 0 ≤ (10/9 : ℝ) * y3 ^ 2 := by positivity
  
  have e9 : y9 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p0, p2, p3]
  have e8 : y8 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p0, p2, p3]
  have e7 : y7 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p0, p2, p3]
  have e6 : y6 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p0, p2, p3]
  have e5 : y5 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p0, p2, p3]
  have e4 : y4 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p0, p2, p3]
  have e0 : y0 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p0, p2, p3]
  have e2 : y2 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p0, p2, p3]
  have e3 : y3 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p0, p2, p3]
  
  have z9 := sq_eq_zero_iff.mp e9
  have z8 := sq_eq_zero_iff.mp e8
  have z7 := sq_eq_zero_iff.mp e7
  have z6 := sq_eq_zero_iff.mp e6
  have z5 := sq_eq_zero_iff.mp e5
  have z4 := sq_eq_zero_iff.mp e4
  have z0 := sq_eq_zero_iff.mp e0
  have z2 := sq_eq_zero_iff.mp e2
  have z3 := sq_eq_zero_iff.mp e3
  
  have d9 : y9 = x 9 - (1/2 : ℝ) * x 8 := hy9.symm
  have d8 : y8 = x 8 - (2/3 : ℝ) * x 7 := hy8.symm
  have d7 : y7 = x 7 - (3/4 : ℝ) * x 6 := hy7.symm
  have d6 : y6 = x 6 - (4/5 : ℝ) * x 5 := hy6.symm
  have d5 : y5 = x 5 - (5/6 : ℝ) * x 4 := hy5.symm
  have d4 : y4 = x 4 - (6/7 : ℝ) * x 0 := hy4.symm
  have d0 : y0 = x 0 - (7/8 : ℝ) * x 2 := hy0.symm
  have d2 : y2 = x 2 - (8/9 : ℝ) * x 3 := hy2.symm
  have d3 : y3 = x 3 := hy3.symm
  
  have x3 : x 3 = 0 := by linarith
  have x2 : x 2 = 0 := by linarith
  have x0 : x 0 = 0 := by linarith
  have x4 : x 4 = 0 := by linarith
  have x5 : x 5 = 0 := by linarith
  have x6 : x 6 = 0 := by linarith
  have x7 : x 7 = 0 := by linarith
  have x8 : x 8 = 0 := by linarith
  have x9 : x 9 = 0 := by linarith
  
  intro i
  match i with
  | ⟨0, _⟩ => exact x0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact x2
  | ⟨3, _⟩ => exact x3
  | ⟨4, _⟩ => exact x4
  | ⟨5, _⟩ => exact x5
  | ⟨6, _⟩ => exact x6
  | ⟨7, _⟩ => exact x7
  | ⟨8, _⟩ => exact x8
  | ⟨9, _⟩ => exact x9

/-! ## D₉ Subdiagram (Delete Node 3) -/
noncomputable def D9_c9 (x : Fin 10 → ℝ) : ℝ := x 9 - (1/2 : ℝ) * x 8
noncomputable def D9_c8 (x : Fin 10 → ℝ) : ℝ := x 8 - (2/3 : ℝ) * x 7
noncomputable def D9_c7 (x : Fin 10 → ℝ) : ℝ := x 7 - (3/4 : ℝ) * x 6
noncomputable def D9_c6 (x : Fin 10 → ℝ) : ℝ := x 6 - (4/5 : ℝ) * x 5
noncomputable def D9_c5 (x : Fin 10 → ℝ) : ℝ := x 5 - (5/6 : ℝ) * x 4
noncomputable def D9_c4 (x : Fin 10 → ℝ) : ℝ := x 4 - (6/7 : ℝ) * x 0
noncomputable def D9_c1 (x : Fin 10 → ℝ) : ℝ := x 1 - (1/2 : ℝ) * x 0
noncomputable def D9_c2 (x : Fin 10 → ℝ) : ℝ := x 2 - (1/2 : ℝ) * x 0
noncomputable def D9_c0 (x : Fin 10 → ℝ) : ℝ := x 0

theorem D9_form_eq (x : Fin 10 → ℝ) (h3 : x 3 = 0) :
    cartanQuadraticFormReal x = 
      2 * D9_c9 x ^ 2 +
      (3/2 : ℝ) * D9_c8 x ^ 2 +
      (4/3 : ℝ) * D9_c7 x ^ 2 +
      (5/4 : ℝ) * D9_c6 x ^ 2 +
      (6/5 : ℝ) * D9_c5 x ^ 2 +
      (7/6 : ℝ) * D9_c4 x ^ 2 +
      2 * D9_c1 x ^ 2 +
      2 * D9_c2 x ^ 2 +
      (1/7 : ℝ) * D9_c0 x ^ 2 := by
  rw [cartanQuadraticFormReal_eq_expanded]
  unfold D9_c9 D9_c8 D9_c7 D9_c6 D9_c5 D9_c4 D9_c1 D9_c2 D9_c0 cartanFormExpanded
  rw [h3]
  ring

theorem D9_positive_definite (x : Fin 10 → ℝ) (h3 : x 3 = 0) 
    (hq : cartanQuadraticFormReal x = 0) : ∀ i, x i = 0 := by
  have heq := D9_form_eq x h3
  rw [hq] at heq
  
  generalize hy9 : D9_c9 x = y9
  generalize hy8 : D9_c8 x = y8
  generalize hy7 : D9_c7 x = y7
  generalize hy6 : D9_c6 x = y6
  generalize hy5 : D9_c5 x = y5
  generalize hy4 : D9_c4 x = y4
  generalize hy1 : D9_c1 x = y1
  generalize hy2 : D9_c2 x = y2
  generalize hy0 : D9_c0 x = y0
  
  have p9 : 0 ≤ 2 * y9 ^ 2 := by positivity
  have p8 : 0 ≤ (3/2 : ℝ) * y8 ^ 2 := by positivity
  have p7 : 0 ≤ (4/3 : ℝ) * y7 ^ 2 := by positivity
  have p6 : 0 ≤ (5/4 : ℝ) * y6 ^ 2 := by positivity
  have p5 : 0 ≤ (6/5 : ℝ) * y5 ^ 2 := by positivity
  have p4 : 0 ≤ (7/6 : ℝ) * y4 ^ 2 := by positivity
  have p1 : 0 ≤ 2 * y1 ^ 2 := by positivity
  have p2 : 0 ≤ 2 * y2 ^ 2 := by positivity
  have p0 : 0 ≤ (1/7 : ℝ) * y0 ^ 2 := by positivity
  
  have e9 : y9 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p1, p2, p0]
  have e8 : y8 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p1, p2, p0]
  have e7 : y7 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p1, p2, p0]
  have e6 : y6 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p1, p2, p0]
  have e5 : y5 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p1, p2, p0]
  have e4 : y4 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p1, p2, p0]
  have e1 : y1 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p1, p2, p0]
  have e2 : y2 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p1, p2, p0]
  have e0 : y0 ^ 2 = 0 := by linarith [heq, p9, p8, p7, p6, p5, p4, p1, p2, p0]
  
  have z9 := sq_eq_zero_iff.mp e9
  have z8 := sq_eq_zero_iff.mp e8
  have z7 := sq_eq_zero_iff.mp e7
  have z6 := sq_eq_zero_iff.mp e6
  have z5 := sq_eq_zero_iff.mp e5
  have z4 := sq_eq_zero_iff.mp e4
  have z1 := sq_eq_zero_iff.mp e1
  have z2 := sq_eq_zero_iff.mp e2
  have z0 := sq_eq_zero_iff.mp e0
  
  have d9 : y9 = x 9 - (1/2 : ℝ) * x 8 := hy9.symm
  have d8 : y8 = x 8 - (2/3 : ℝ) * x 7 := hy8.symm
  have d7 : y7 = x 7 - (3/4 : ℝ) * x 6 := hy7.symm
  have d6 : y6 = x 6 - (4/5 : ℝ) * x 5 := hy6.symm
  have d5 : y5 = x 5 - (5/6 : ℝ) * x 4 := hy5.symm
  have d4 : y4 = x 4 - (6/7 : ℝ) * x 0 := hy4.symm
  have d1 : y1 = x 1 - (1/2 : ℝ) * x 0 := hy1.symm
  have d2 : y2 = x 2 - (1/2 : ℝ) * x 0 := hy2.symm
  have d0 : y0 = x 0 := hy0.symm
  
  have x0 : x 0 = 0 := by linarith
  have x1 : x 1 = 0 := by linarith
  have x2 : x 2 = 0 := by linarith
  have x4 : x 4 = 0 := by linarith
  have x5 : x 5 = 0 := by linarith
  have x6 : x 6 = 0 := by linarith
  have x7 : x 7 = 0 := by linarith
  have x8 : x 8 = 0 := by linarith
  have x9 : x 9 = 0 := by linarith
  
  intro i
  match i with
  | ⟨0, _⟩ => exact x0
  | ⟨1, _⟩ => exact x1
  | ⟨2, _⟩ => exact x2
  | ⟨3, _⟩ => exact h3
  | ⟨4, _⟩ => exact x4
  | ⟨5, _⟩ => exact x5
  | ⟨6, _⟩ => exact x6
  | ⟨7, _⟩ => exact x7
  | ⟨8, _⟩ => exact x8
  | ⟨9, _⟩ => exact x9

/-! ## Affine E₈ Subdiagram (Delete Node 9) -/
noncomputable def E8_d1 (x : Fin 10 → ℝ) : ℝ := x 1 - (1/2 : ℝ) * x 0
noncomputable def E8_d3 (x : Fin 10 → ℝ) : ℝ := x 3 - (1/2 : ℝ) * x 2
noncomputable def E8_d2 (x : Fin 10 → ℝ) : ℝ := x 2 - (2/3 : ℝ) * x 0
noncomputable def E8_d8 (x : Fin 10 → ℝ) : ℝ := x 8 - (1/2 : ℝ) * x 7
noncomputable def E8_d7 (x : Fin 10 → ℝ) : ℝ := x 7 - (2/3 : ℝ) * x 6
noncomputable def E8_d6 (x : Fin 10 → ℝ) : ℝ := x 6 - (3/4 : ℝ) * x 5
noncomputable def E8_d5 (x : Fin 10 → ℝ) : ℝ := x 5 - (4/5 : ℝ) * x 4
noncomputable def E8_d4 (x : Fin 10 → ℝ) : ℝ := x 4 - (5/6 : ℝ) * x 0

theorem E8_form_eq (x : Fin 10 → ℝ) (h9 : x 9 = 0) :
    cartanQuadraticFormReal x = 
      2 * E8_d1 x ^ 2 +
      2 * E8_d3 x ^ 2 +
      (3/2 : ℝ) * E8_d2 x ^ 2 +
      2 * E8_d8 x ^ 2 +
      (3/2 : ℝ) * E8_d7 x ^ 2 +
      (4/3 : ℝ) * E8_d6 x ^ 2 +
      (5/4 : ℝ) * E8_d5 x ^ 2 +
      (6/5 : ℝ) * E8_d4 x ^ 2 := by
  rw [cartanQuadraticFormReal_eq_expanded]
  unfold E8_d1 E8_d3 E8_d2 E8_d8 E8_d7 E8_d6 E8_d5 E8_d4 cartanFormExpanded
  rw [h9]
  ring

theorem E8_positive_semidefinite (x : Fin 10 → ℝ) (h9 : x 9 = 0) :
    0 ≤ cartanQuadraticFormReal x := by
  rw [E8_form_eq x h9]
  positivity

theorem E8_nullspace (x : Fin 10 → ℝ) (h9 : x 9 = 0) 
    (hq : cartanQuadraticFormReal x = 0) : 
    x 1 = (1/2 : ℝ) * x 0 ∧ 
    x 2 = (2/3 : ℝ) * x 0 ∧ 
    x 3 = (1/3 : ℝ) * x 0 ∧ 
    x 4 = (5/6 : ℝ) * x 0 ∧ 
    x 5 = (2/3 : ℝ) * x 0 ∧ 
    x 6 = (1/2 : ℝ) * x 0 ∧ 
    x 7 = (1/3 : ℝ) * x 0 ∧ 
    x 8 = (1/6 : ℝ) * x 0 := by
  have heq := E8_form_eq x h9
  rw [hq] at heq
  
  generalize hy1 : E8_d1 x = y1
  generalize hy3 : E8_d3 x = y3
  generalize hy2 : E8_d2 x = y2
  generalize hy8 : E8_d8 x = y8
  generalize hy7 : E8_d7 x = y7
  generalize hy6 : E8_d6 x = y6
  generalize hy5 : E8_d5 x = y5
  generalize hy4 : E8_d4 x = y4
  
  have p1 : 0 ≤ 2 * y1 ^ 2 := by positivity
  have p3 : 0 ≤ 2 * y3 ^ 2 := by positivity
  have p2 : 0 ≤ (3/2 : ℝ) * y2 ^ 2 := by positivity
  have p8 : 0 ≤ 2 * y8 ^ 2 := by positivity
  have p7 : 0 ≤ (3/2 : ℝ) * y7 ^ 2 := by positivity
  have p6 : 0 ≤ (4/3 : ℝ) * y6 ^ 2 := by positivity
  have p5 : 0 ≤ (5/4 : ℝ) * y5 ^ 2 := by positivity
  have p4 : 0 ≤ (6/5 : ℝ) * y4 ^ 2 := by positivity
  
  have e1 : y1 ^ 2 = 0 := by linarith [heq, p1, p3, p2, p8, p7, p6, p5, p4]
  have e3 : y3 ^ 2 = 0 := by linarith [heq, p1, p3, p2, p8, p7, p6, p5, p4]
  have e2 : y2 ^ 2 = 0 := by linarith [heq, p1, p3, p2, p8, p7, p6, p5, p4]
  have e8 : y8 ^ 2 = 0 := by linarith [heq, p1, p3, p2, p8, p7, p6, p5, p4]
  have e7 : y7 ^ 2 = 0 := by linarith [heq, p1, p3, p2, p8, p7, p6, p5, p4]
  have e6 : y6 ^ 2 = 0 := by linarith [heq, p1, p3, p2, p8, p7, p6, p5, p4]
  have e5 : y5 ^ 2 = 0 := by linarith [heq, p1, p3, p2, p8, p7, p6, p5, p4]
  have e4 : y4 ^ 2 = 0 := by linarith [heq, p1, p3, p2, p8, p7, p6, p5, p4]
  
  have z1 := sq_eq_zero_iff.mp e1
  have z3 := sq_eq_zero_iff.mp e3
  have z2 := sq_eq_zero_iff.mp e2
  have z8 := sq_eq_zero_iff.mp e8
  have z7 := sq_eq_zero_iff.mp e7
  have z6 := sq_eq_zero_iff.mp e6
  have z5 := sq_eq_zero_iff.mp e5
  have z4 := sq_eq_zero_iff.mp e4
  
  have d1 : y1 = x 1 - (1/2 : ℝ) * x 0 := hy1.symm
  have d3 : y3 = x 3 - (1/2 : ℝ) * x 2 := hy3.symm
  have d2 : y2 = x 2 - (2/3 : ℝ) * x 0 := hy2.symm
  have d8 : y8 = x 8 - (1/2 : ℝ) * x 7 := hy8.symm
  have d7 : y7 = x 7 - (2/3 : ℝ) * x 6 := hy7.symm
  have d6 : y6 = x 6 - (3/4 : ℝ) * x 5 := hy6.symm
  have d5 : y5 = x 5 - (4/5 : ℝ) * x 4 := hy5.symm
  have d4 : y4 = x 4 - (5/6 : ℝ) * x 0 := hy4.symm
  
  constructor
  · linarith
  · constructor
    · linarith
    · constructor
      · linarith
      · constructor
        · linarith
        · constructor
          · linarith
          · constructor
            · linarith
            · constructor
              · linarith
              · linarith

end InfoGeometry.Lie.E10ProperSubdiagrams
