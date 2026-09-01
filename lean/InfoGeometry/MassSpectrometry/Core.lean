import Mathlib
import InfoGeometry.Routing.PermutationPerfectMatching

/-!
# Finite mass-spectrometry representation core

This module gives a Mathlib-native finite carrier for mass-spectrometry data
and for the combinatorial structures used to compare spectra with latent
fragment states.  It deliberately separates proved algebraic facts from
instrument- or chemistry-specific modelling assumptions.

The formal layer contains:

* finite positive-mass, nonnegative-intensity spectra;
* free-monoid words of peak tokens;
* rank-certified fragmentation DAGs;
* hard peak/fragment assignments by permutation matrices;
* soft assignments as doubly stochastic matrices;
* logarithmic mass coordinates and their scale invariance;
* finite stochastic fragmentation grammars;
* multiplicative path weights and additive negative-log surprisal.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open scoped BigOperators

/-! ## Peak spectra -/

/-- A centroided spectral peak.  Positivity/nonnegativity are part of the
carrier rather than external conventions. -/
structure Peak where
  mass : ℝ
  intensity : ℝ
  mass_pos : 0 < mass
  intensity_nonneg : 0 ≤ intensity

/-- A finite spectrum with exactly `n` indexed peaks. -/
abbrev Spectrum (n : ℕ) := Fin n → Peak

/-- Total recorded intensity of a finite spectrum. -/
def totalIntensity {n : ℕ} (S : Spectrum n) : ℝ :=
  ∑ i, (S i).intensity

/-- The first intensity-weighted mass moment. -/
def firstMassMoment {n : ℕ} (S : Spectrum n) : ℝ :=
  ∑ i, (S i).intensity * (S i).mass

theorem totalIntensity_nonneg {n : ℕ} (S : Spectrum n) :
    0 ≤ totalIntensity S := by
  unfold totalIntensity
  exact Finset.sum_nonneg fun i _ => (S i).intensity_nonneg

theorem firstMassMoment_nonneg {n : ℕ} (S : Spectrum n) :
    0 ≤ firstMassMoment S := by
  unfold firstMassMoment
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (S i).intensity_nonneg (le_of_lt (S i).mass_pos)

/-- A spectrum can be represented as a word in the free monoid on peak
symbols.  No physical significance is attached to an arbitrary input order. -/
def peakWord (xs : List Peak) : FreeMonoid Peak :=
  FreeMonoid.ofList xs

@[simp] theorem peakWord_toList (xs : List Peak) :
    FreeMonoid.toList (peakWord xs) = xs := by
  simp [peakWord]

/-- Predicate saying that a chosen serialization is nondecreasing in mass. -/
def IsMassSorted (xs : List Peak) : Prop :=
  xs.Pairwise fun p q => p.mass ≤ q.mass

@[simp] theorem isMassSorted_nil : IsMassSorted [] := by
  simp [IsMassSorted]

@[simp] theorem isMassSorted_singleton (p : Peak) : IsMassSorted [p] := by
  simp [IsMassSorted]

/-! ## Fragmentation DAGs -/

/-- A finite directed fragmentation system certified acyclic by a strictly
rank-decreasing edge map.  `rank` may encode fragmentation depth, molecular
size, or any other well-founded finite grading supplied by an application. -/
structure FragmentationDAG (n : ℕ) where
  edge : Fin n → Fin n → Prop
  rank : Fin n → ℕ
  rank_decreases : ∀ {u v}, edge u v → rank v < rank u

namespace FragmentationDAG

variable {n : ℕ} (D : FragmentationDAG n)

theorem edge_irrefl (u : Fin n) : ¬ D.edge u u := by
  intro h
  exact (Nat.lt_irrefl (D.rank u)) (D.rank_decreases h)

theorem not_two_cycle {u v : Fin n} (huv : D.edge u v) : ¬ D.edge v u := by
  intro hvu
  have h₁ : D.rank v < D.rank u := D.rank_decreases huv
  have h₂ : D.rank u < D.rank v := D.rank_decreases hvu
  exact (Nat.not_lt_of_ge (Nat.le_of_lt h₁)) h₂

theorem not_three_cycle {u v w : Fin n}
    (huv : D.edge u v) (hvw : D.edge v w) : ¬ D.edge w u := by
  intro hwu
  have h₁ : D.rank v < D.rank u := D.rank_decreases huv
  have h₂ : D.rank w < D.rank v := D.rank_decreases hvw
  have h₃ : D.rank u < D.rank w := D.rank_decreases hwu
  omega

end FragmentationDAG

/-! ## Hard and soft peak/fragment assignment -/

abbrev AssignmentMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Hard one-to-one peak/fragment assignment. -/
def hardAssignment {n : ℕ} (σ : Equiv.Perm (Fin n)) : AssignmentMatrix n :=
  σ.permMatrix ℝ

/-- The support of a hard assignment is a perfect matching. -/
theorem hardAssignment_support_isPerfectMatching {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    InfoGeometry.Routing.PermutationPerfectMatching.IsPerfectMatching
      (InfoGeometry.Routing.PermutationPerfectMatching.matrixSupport
        (hardAssignment σ)) := by
  simpa [hardAssignment] using
    (InfoGeometry.Routing.PermutationPerfectMatching.permMatrix_support_isPerfectMatching σ)

/-- A finite Birkhoff-type assignment: nonnegative entries with unit row and
column sums. -/
structure IsDoublyStochastic {n : ℕ} (A : AssignmentMatrix n) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  row_sum : ∀ i, ∑ j, A i j = 1
  col_sum : ∀ j, ∑ i, A i j = 1

/-- The identity assignment is doubly stochastic. -/
theorem identity_isDoublyStochastic (n : ℕ) :
    IsDoublyStochastic (1 : AssignmentMatrix n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    by_cases h : i = j
    · simp [h]
    · simp [h]
  · intro i
    simp
  · intro j
    simp

/-! ## Logarithmic mass coordinates -/

/-- Dimensionless logarithmic mass coordinate relative to a reference mass. -/
def logMass (m m₀ : ℝ) : ℝ :=
  Real.log (m / m₀)

/-- A common multiplicative rescaling cancels from the relative log-mass
coordinate. -/
theorem logMass_common_scale
    {λ m m₀ : ℝ} (hλ : λ ≠ 0) (hm₀ : m₀ ≠ 0) :
    logMass (λ * m) (λ * m₀) = logMass m m₀ := by
  unfold logMass
  congr 1
  field_simp [hλ, hm₀]

/-- Relative log mass is a difference of absolute log coordinates. -/
theorem logMass_eq_sub
    {m m₀ : ℝ} (hm : m ≠ 0) (hm₀ : m₀ ≠ 0) :
    logMass m m₀ = Real.log m - Real.log m₀ := by
  unfold logMass
  exact Real.log_div hm hm₀

/-- Multiplicative mass scaling becomes translation in logarithmic mass. -/
theorem log_scale_add
    {λ m : ℝ} (hλ : λ ≠ 0) (hm : m ≠ 0) :
    Real.log (λ * m) = Real.log λ + Real.log m := by
  exact Real.log_mul hλ hm

/-! ## Finite stochastic fragmentation grammar -/

/-- Directed edge labels for a finite fragmentation system. -/
abbrev FragmentEdge (n : ℕ) := Fin n × Fin n

/-- A finite substochastic grammar supported on the fragmentation DAG.
The row bound allows probability mass to terminate at a fragment rather than
forcing every state to emit another fragment. -/
structure StochasticGrammar {n : ℕ} (D : FragmentationDAG n) where
  weight : Fin n → Fin n → ℝ
  weight_nonneg : ∀ u v, 0 ≤ weight u v
  support : ∀ {u v}, weight u v ≠ 0 → D.edge u v
  row_sum_le_one : ∀ u, ∑ v, weight u v ≤ 1

namespace StochasticGrammar

variable {n : ℕ} {D : FragmentationDAG n} (G : StochasticGrammar D)

/-- Multiplicative probability weight assigned to a finite list of directed
fragment transitions. -/
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

/-- Nonzero edge weights imply a nonzero multiplicative path weight. -/
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

/-- The negative logarithm sends a product of nonzero transition weights to
the sum of their edge surprisals. -/
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
      have hp : G.pathProbability es ≠ 0 :=
        G.pathProbability_ne_zero es hrest
      rw [pathProbability, pathSurprisal, Real.log_mul he hp, ih hrest]
      ring

/-- Every nonzero grammar transition is a genuine DAG edge and therefore
strictly lowers the chosen fragmentation rank. -/
theorem rank_decreases_of_weight_ne_zero
    {u v : Fin n} (h : G.weight u v ≠ 0) :
    D.rank v < D.rank u := by
  exact D.rank_decreases (G.support h)

end StochasticGrammar

end InfoGeometry.MassSpectrometry
