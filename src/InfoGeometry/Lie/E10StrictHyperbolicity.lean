import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Lie.E10LorentzianDecomposition
import InfoGeometry.Lie.E10HyperbolicSignature
import InfoGeometry.Lie.E10ProperSubdiagrams

namespace InfoGeometry.Lie.E10StrictHyperbolicity

open InfoGeometry.Lie.E10
open InfoGeometry.Lie.E10LorentzianDecomposition
open InfoGeometry.Lie.E10Hyperbolic
open InfoGeometry.Lie.E10ProperSubdiagrams

theorem positiveArmPart_eq_zero_implies_ai_zero (x : Fin 10 → ℝ) (h : positiveArmPart x = 0) :
    a1 x = 0 ∧ a2 x = 0 ∧ a3 x = 0 ∧ a4 x = 0 ∧ a5 x = 0 ∧ a6 x = 0 ∧ a7 x = 0 ∧ a8 x = 0 ∧ a9 x = 0 := by
  unfold positiveArmPart at h
  have h1 : 0 ≤ 2 * a1 x ^ 2 := by positivity
  have h2 : 0 ≤ a2 x ^ 2 := by positivity
  have h23 : 0 ≤ (a2 x - a3 x) ^ 2 := by positivity
  have h3 : 0 ≤ a3 x ^ 2 := by positivity
  have h4 : 0 ≤ a4 x ^ 2 := by positivity
  have h45 : 0 ≤ (a4 x - a5 x) ^ 2 := by positivity
  have h56 : 0 ≤ (a5 x - a6 x) ^ 2 := by positivity
  have h67 : 0 ≤ (a6 x - a7 x) ^ 2 := by positivity
  have h78 : 0 ≤ (a7 x - a8 x) ^ 2 := by positivity
  have h89 : 0 ≤ (a8 x - a9 x) ^ 2 := by positivity
  have h9 : 0 ≤ a9 x ^ 2 := by positivity
  
  have e1 : a1 x ^ 2 = 0 := by linarith [h, h1, h2, h23, h3, h4, h45, h56, h67, h78, h89, h9]
  have e2 : a2 x ^ 2 = 0 := by linarith [h, h1, h2, h23, h3, h4, h45, h56, h67, h78, h89, h9]
  have e3 : a3 x ^ 2 = 0 := by linarith [h, h1, h2, h23, h3, h4, h45, h56, h67, h78, h89, h9]
  have e4 : a4 x ^ 2 = 0 := by linarith [h, h1, h2, h23, h3, h4, h45, h56, h67, h78, h89, h9]
  have e5 : (a4 x - a5 x) ^ 2 = 0 := by linarith [h, h1, h2, h23, h3, h4, h45, h56, h67, h78, h89, h9]
  have e6 : (a5 x - a6 x) ^ 2 = 0 := by linarith [h, h1, h2, h23, h3, h4, h45, h56, h67, h78, h89, h9]
  have e7 : (a6 x - a7 x) ^ 2 = 0 := by linarith [h, h1, h2, h23, h3, h4, h45, h56, h67, h78, h89, h9]
  have e8 : (a7 x - a8 x) ^ 2 = 0 := by linarith [h, h1, h2, h23, h3, h4, h45, h56, h67, h78, h89, h9]
  have e9 : a9 x ^ 2 = 0 := by linarith [h, h1, h2, h23, h3, h4, h45, h56, h67, h78, h89, h9]
  
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sq_eq_zero_iff.mp e1
  · exact sq_eq_zero_iff.mp e2
  · exact sq_eq_zero_iff.mp e3
  · exact sq_eq_zero_iff.mp e4
  · have h40 := sq_eq_zero_iff.mp e4
    have h450 := sq_eq_zero_iff.mp e5
    linarith
  · have h40 := sq_eq_zero_iff.mp e4
    have h450 := sq_eq_zero_iff.mp e5
    have h560 := sq_eq_zero_iff.mp e6
    linarith
  · have h40 := sq_eq_zero_iff.mp e4
    have h450 := sq_eq_zero_iff.mp e5
    have h560 := sq_eq_zero_iff.mp e6
    have h670 := sq_eq_zero_iff.mp e7
    linarith
  · have h40 := sq_eq_zero_iff.mp e4
    have h450 := sq_eq_zero_iff.mp e5
    have h560 := sq_eq_zero_iff.mp e6
    have h670 := sq_eq_zero_iff.mp e7
    have h780 := sq_eq_zero_iff.mp e8
    linarith
  · exact sq_eq_zero_iff.mp e9

/-- 🏆 THEOREM: The arm coordinate transformation is invertible. -/
theorem e10_arm_form_strictly_positive_definite (x : Fin 10 → ℝ)
    (h_pos : positiveArmPart x = 0) (h_cent : x 0 = 0) :
    ∀ i, x i = 0 := by
  have ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    positiveArmPart_eq_zero_implies_ai_zero x h_pos
  
  have def1 : a1 x = x 1 - x 0 / 2 := rfl
  have def2 : a2 x = x 2 - (2/3 : ℝ) * x 0 := rfl
  have def3 : a3 x = x 3 - x 0 / 3 := rfl
  have def4 : a4 x = x 4 - (6/7 : ℝ) * x 0 := rfl
  have def5 : a5 x = x 5 - (5/7 : ℝ) * x 0 := rfl
  have def6 : a6 x = x 6 - (4/7 : ℝ) * x 0 := rfl
  have def7 : a7 x = x 7 - (3/7 : ℝ) * x 0 := rfl
  have def8 : a8 x = x 8 - (2/7 : ℝ) * x 0 := rfl
  have def9 : a9 x = x 9 - x 0 / 7 := rfl
  
  have x1 : x 1 = 0 := by linarith
  have x2 : x 2 = 0 := by linarith
  have x3 : x 3 = 0 := by linarith
  have x4 : x 4 = 0 := by linarith
  have x5 : x 5 = 0 := by linarith
  have x6 : x 6 = 0 := by linarith
  have x7 : x 7 = 0 := by linarith
  have x8 : x 8 = 0 := by linarith
  have x9 : x 9 = 0 := by linarith

  intro i
  fin_cases i
  · exact h_cent
  · exact x1
  · exact x2
  · exact x3
  · exact x4
  · exact x5
  · exact x6
  · exact x7
  · exact x8
  · exact x9

/-- 
The global E₁₀ Cartan matrix is physically indefinite.
It possesses strictly positive state vectors and strictly negative state vectors.
-/
theorem e10_is_indefinite :
    (∃ v : Fin 10 → ℝ, 0 < cartanQuadraticFormReal v) ∧ 
    (∃ w : Fin 10 → ℝ, cartanQuadraticFormReal w < 0) := by
  constructor
  · -- The canonical simple root at node 0 has length squared 2.
    use (fun i => if i = 0 then 1 else 0)
    have h_eval : cartanQuadraticFormReal (fun i => if i = 0 then 1 else 0) = 2 := by
      rw [cartanQuadraticFormReal_eq_expanded]
      unfold cartanFormExpanded
      norm_num
    rw [h_eval]
    norm_num
  · -- The explicit timelike imaginary root constructed in E10HyperbolicSignature
    use (fun i => (timelikeRoot i : ℝ))
    have h_eval : cartanQuadraticFormReal (fun i => (timelikeRoot i : ℝ)) = -4 := by
      -- The real form evaluates to exactly the integer form value
      -- since it's just a homomorphism.
      rw [cartanQuadraticFormReal_eq_expanded]
      unfold cartanFormExpanded timelikeRoot
      norm_num
    rw [h_eval]
    norm_num

/--
The Strict Hyperbolicity Criterion.
The three maximal proper subdiagrams correspond to deleting nodes 1, 3, or 9.
Any other proper subdiagram is a sub-graph of one of these three.
Since A₉ and D₉ are strictly positive definite, and E₈⁽¹⁾ is positive 
semidefinite, any physical subsystem bounded away from the full E₁₀ space 
is gravitationally stable (cannot possess a negative mode).
-/
theorem e10_proper_subdiagrams_are_stable :
    -- Maximal limit 1: A₉ (Delete node 1)
    (∀ x : Fin 10 → ℝ, x 1 = 0 → cartanQuadraticFormReal x = 0 → ∀ i, x i = 0) ∧
    -- Maximal limit 2: D₉ (Delete node 3)
    (∀ x : Fin 10 → ℝ, x 3 = 0 → cartanQuadraticFormReal x = 0 → ∀ i, x i = 0) ∧
    -- Maximal limit 3: Affine E₈ (Delete node 9)
    (∀ x : Fin 10 → ℝ, x 9 = 0 → 0 ≤ cartanQuadraticFormReal x) := by
  constructor
  · exact A9_positive_definite
  constructor
  · exact D9_positive_definite
  · exact E8_positive_semidefinite

end InfoGeometry.Lie.E10StrictHyperbolicity
