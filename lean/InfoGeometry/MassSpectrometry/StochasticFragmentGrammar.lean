import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.MassSpectrometry.FragmentationDAG
import InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge

/-!
# Stochastic fragmentation grammars

The chemistry-specific layer is kept as explicit data.  Substochastic kernels
allow terminal fragments.  When a kernel is normalized, it is bridged into the
repository's existing `StochasticTransitionMatrix` owner, so amplitude and
Bhattacharyya results are reused rather than duplicated.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open scoped BigOperators

/-- Experimental conditions indexing a fragmentation kernel. -/
structure CollisionCondition where
  energy : ℝ
  charge : ℕ
  gas : String

/-- Directed edge labels for a finite fragmentation system. -/
abbrev FragmentEdge (n : ℕ) := Fin n × Fin n

/-- A finite substochastic grammar supported on a fragmentation DAG. -/
structure StochasticGrammar {n : ℕ} (D : FragmentationDAG n) where
  weight : Fin n → Fin n → ℝ
  weight_nonneg : ∀ u v, 0 ≤ weight u v
  support : ∀ {u v}, weight u v ≠ 0 → D.edge u v
  row_sum_le_one : ∀ u, ∑ v, weight u v ≤ 1

/-- A family of fragmentation grammars indexed by experimental conditions. -/
structure EnergyConditionedGrammar {n : ℕ} (D : FragmentationDAG n) where
  kernel : CollisionCondition → StochasticGrammar D

namespace StochasticGrammar

variable {n : ℕ} {D : FragmentationDAG n} (G : StochasticGrammar D)

/-- Multiplicative weight of a finite transition list. -/
def pathProbability : List (FragmentEdge n) → ℝ
  | [] => 1
  | e :: es => G.weight e.1 e.2 * pathProbability es

/-- Additive negative-log action of a finite transition list. -/
def pathSurprisal : List (FragmentEdge n) → ℝ
  | [] => 0
  | e :: es => -Real.log (G.weight e.1 e.2) + pathSurprisal es

@[simp] theorem pathProbability_nil : G.pathProbability [] = 1 := rfl

@[simp] theorem pathProbability_cons (e : FragmentEdge n)
    (es : List (FragmentEdge n)) :
    G.pathProbability (e :: es) =
      G.weight e.1 e.2 * G.pathProbability es := rfl

@[simp] theorem pathSurprisal_nil : G.pathSurprisal [] = 0 := rfl

@[simp] theorem pathSurprisal_cons (e : FragmentEdge n)
    (es : List (FragmentEdge n)) :
    G.pathSurprisal (e :: es) =
      -Real.log (G.weight e.1 e.2) + G.pathSurprisal es := rfl

theorem pathProbability_ne_zero
    (es : List (FragmentEdge n))
    (h : ∀ e ∈ es, G.weight e.1 e.2 ≠ 0) :
    G.pathProbability es ≠ 0 := by
  induction es with
  | nil => simp
  | cons e es ih =>
      have he : G.weight e.1 e.2 ≠ 0 := h e (by simp)
      have hrest : ∀ f ∈ es, G.weight f.1 f.2 ≠ 0 := by
        intro f hf
        exact h f (by simp [hf])
      simp [pathProbability, he, ih hrest]

/-- Negative log converts nonzero path products into additive edge surprisal. -/
theorem neg_log_pathProbability_eq_pathSurprisal
    (es : List (FragmentEdge n))
    (h : ∀ e ∈ es, G.weight e.1 e.2 ≠ 0) :
    -Real.log (G.pathProbability es) = G.pathSurprisal es := by
  induction es with
  | nil => simp [pathProbability, pathSurprisal]
  | cons e es ih =>
      have he : G.weight e.1 e.2 ≠ 0 := h e (by simp)
      have hrest : ∀ f ∈ es, G.weight f.1 f.2 ≠ 0 := by
        intro f hf
        exact h f (by simp [hf])
      have hp : G.pathProbability es ≠ 0 := G.pathProbability_ne_zero es hrest
      rw [pathProbability, pathSurprisal, Real.log_mul he hp, ih hrest]
      ring

/-- Every nonzero grammar transition strictly lowers fragmentation rank. -/
theorem rank_decreases_of_weight_ne_zero
    {u v : Fin n} (h : G.weight u v ≠ 0) :
    D.rank v < D.rank u := by
  exact D.rank_decreases (G.support h)

end StochasticGrammar

/-- Normalized grammar, used when every source state emits total probability 1. -/
structure NormalizedGrammar {n : ℕ} (D : FragmentationDAG n) where
  weight : Fin n → Fin n → ℝ
  weight_nonneg : ∀ u v, 0 ≤ weight u v
  support : ∀ {u v}, weight u v ≠ 0 → D.edge u v
  row_sum : ∀ u, ∑ v, weight u v = 1

namespace NormalizedGrammar

variable {n : ℕ} {D : FragmentationDAG n} (G : NormalizedGrammar D)

/-- Forget support and expose the repository's existing row-stochastic carrier. -/
def toTransitionMatrix :
    InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge.StochasticTransitionMatrix n where
  A := G.weight
  nonneg := G.weight_nonneg
  row_sum := G.row_sum

/-- The square-root amplitude row of a normalized fragmentation grammar has
unit L2 norm, by the pre-existing stochastic-language theorem. -/
theorem amplitude_row_l2_normalization (i : Fin n) :
    ∑ j, (G.toTransitionMatrix.amplitudeMatrix i j) ^ 2 = 1 := by
  exact G.toTransitionMatrix.amplitude_row_l2_normalization i

end NormalizedGrammar

end InfoGeometry.MassSpectrometry
