/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.InformationGeometry.ParametricCramerRaoAndCumulants
import InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity
import InfoGeometry.Categorical.MarkovCategoryAndColimitInformation
import InfoGeometry.OperatorAlgebra.KadisonSchwarzAndQuantumCramerRao
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Classical-to-Operator Information Geometry Bridge

Unifies the finite statistical manifold pillar with the noncommutative operator-algebraic
pillar by realizing any finite distribution `P : ProbDist α` inside the real matrix star-algebra
`Matrix α α ℝ`:

1. **Commutative Diagonal Embedding**:
   - `diagState P := Matrix.diagonal P.p` and `diagFunctional P` (`M ↦ Tr(diagState P * M)`),
     proved to satisfy `IsPositiveStarFunctional (diagFunctional P)` and to match the complex
     `InfoGeometry.QuantumGeometry.SLD.sldFisherInner` on diagonal real observables.
2. **Quantum-to-Classical Cramér–Rao & SLD Reduction**:
   - Proves `diag_tangent_eq_sld_jordan`, `quantumSLDInner_diag_eq_fisherMetric`, and
     `quantumVariance_diag_eq_statVariance`, and derives `classical_cramer_rao_from_quantum_sld`
     as a direct specialization of the noncommutative `sld_quantum_cramer_rao_inequality`.
3. **Markov Channels as Matrix Kraus Maps & Kadison–Schwarz Variance Contraction**:
   - Constructs the exact square-root matrix Kraus family `markovKraus K` indexed by `α × α`,
     verifies right completeness `∑ ab, star (markovKraus K ab) * markovKraus K ab = 1`,
     proves `krausChannel (markovKraus K) (diagState P) = diagState (pushforward K P)` and
     `(diagFunctional P).comp (krausDualLinear (markovKraus K)) = diagFunctional (pushforward K P)`,
     and derives classical conditional-expectation variance contraction
     `markov_conditional_expectation_variance_contraction` from `krausDual_quantumVariance_le`.
-/

noncomputable section

namespace InfoGeometry.Foundations.ClassicalToOperatorInformationBridge

open Finset Matrix
open scoped BigOperators
open InfoGeometry.Epistemology.VariationalRG
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.InformationGeometry.ParametricCramerRaoAndCumulants
open InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel
open InfoGeometry.OperatorAlgebra.PeirceQuantumGeometricTensor
open InfoGeometry.OperatorAlgebra.KadisonSchwarzAndQuantumCramerRao
open InfoGeometry.QuantumGeometry.SLD

section DiagonalState

lemma diagonal_star {α : Type*} [DecidableEq α] (f : α → ℝ) :
    star (Matrix.diagonal f : Matrix α α ℝ) = Matrix.diagonal f := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.star_apply]
  · simp [Matrix.star_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Commutative embedding of a finite probability distribution `P` as a diagonal density
matrix `Matrix.diagonal P.p` in `Matrix α α ℝ`. -/
def diagState (P : ProbDist α) : Matrix α α ℝ :=
  Matrix.diagonal P.p

/-- Positive linear expectation state `M ↦ Tr(diagState P * M)` on `Matrix α α ℝ`. -/
def diagFunctional (P : ProbDist α) : Matrix α α ℝ →ₗ[ℝ] ℝ where
  toFun M := Matrix.trace (diagState P * M)
  map_add' M₁ M₂ := by simp [mul_add, Matrix.trace_add]
  map_smul' r M := by simp [Matrix.trace_smul, smul_eq_mul]

@[simp]
theorem diagFunctional_apply (P : ProbDist α) (M : Matrix α α ℝ) :
    diagFunctional P M = ∑ a, P.p a * M a a := by
  dsimp [diagFunctional, diagState, Matrix.trace]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Matrix.diagonal_mul]

@[simp]
theorem diagFunctional_one (P : ProbDist α) :
    diagFunctional P 1 = 1 := by
  simpa using P.sum_one

/-- `diagFunctional P` satisfies `IsPositiveStarFunctional` on `Matrix α α ℝ`. -/
theorem diagFunctional_isPositiveStarFunctional (P : ProbDist α) :
    IsPositiveStarFunctional (diagFunctional P) := by
  refine ⟨fun M => ?_, fun M => ?_⟩
  · rw [diagFunctional_apply]
    refine Finset.sum_nonneg ?_
    intro a _
    have hdiag : (star M * M) a a = ∑ b, M b a * M b a := by
      simp [Matrix.mul_apply, Matrix.star_apply]
    rw [hdiag]
    exact mul_nonneg (P.nonneg a) (Finset.sum_nonneg fun b _ => mul_self_nonneg (M b a))
  · simp [diagFunctional_apply, Matrix.star_apply]

/-- Compatibility of `quantumSLDInner (diagFunctional P)` on real diagonal observables with
`InfoGeometry.QuantumGeometry.SLD.sldFisherInner` on `Matrix α α ℂ`. -/
theorem sldFisherInner_complex_diag_eq_quantumSLDInner
    (P : ProbDist α) (l₁ l₂ : α → ℝ) :
    sldFisherInner
        (Matrix.diagonal fun a => (P.p a : ℂ))
        (Matrix.diagonal fun a => (l₁ a : ℂ))
        (Matrix.diagonal fun a => (l₂ a : ℂ)) =
      (quantumSLDInner (diagFunctional P) (Matrix.diagonal l₁) (Matrix.diagonal l₂) : ℂ) := by
  have hc :
      (Matrix.diagonal fun a => (P.p a : ℂ)) *
          InfoGeometry.QuantumGeometry.SLD.jordanProd
            (Matrix.diagonal fun a => (l₁ a : ℂ))
            (Matrix.diagonal fun a => (l₂ a : ℂ)) =
        Matrix.diagonal fun a => ((P.p a * (l₁ a * l₂ a + l₂ a * l₁ a) : ℝ) : ℂ) := by
    dsimp [InfoGeometry.QuantumGeometry.SLD.jordanProd]
    rw [mul_add, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Complex.ofReal_mul, Complex.ofReal_add]
      ring
    · simp only [Matrix.add_apply, Matrix.diagonal_apply_ne _ hij, add_zero]
  have hr :
      quantumSLDInner (diagFunctional P) (Matrix.diagonal l₁) (Matrix.diagonal l₂) =
        (1 / 2 : ℝ) * ∑ a, P.p a * (l₁ a * l₂ a + l₂ a * l₁ a) := by
    dsimp [quantumSLDInner, operatorJordan]
    rw [diagFunctional_apply]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [Matrix.add_apply, Matrix.diagonal_mul_diagonal]
  dsimp [sldFisherInner]
  rw [hc, Matrix.trace_diagonal, hr]
  push_cast
  rfl

/-- Exact SLD Jordan tangent identification:
`diag(dp) = (1 / 2) • {diag(p), diag(score p dp)}`. -/
theorem diag_tangent_eq_sld_jordan (P : ProbInterior α) (dp : α → ℝ) :
    Matrix.diagonal dp =
      (1 / 2 : ℝ) • operatorJordan (diagState (toProbDist P)) (Matrix.diagonal (score P.p dp)) := by
  dsimp [operatorJordan, diagState, toProbDist]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    have hpos : P.p i ≠ 0 := ne_of_gt (P.pos i)
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.diagonal_apply_eq, smul_eq_mul, score]
    field_simp [hpos]
    ring
  · simp [hij]

/-- On diagonal score operators, `quantumSLDInner (diagFunctional (toProbDist P))` reduces
identically to `ChentsovMetricInvariance.fisherMetric`. -/
theorem quantumSLDInner_diag_eq_fisherMetric (P : ProbInterior α) (dp : α → ℝ) :
    quantumSLDInner (diagFunctional (toProbDist P))
        (Matrix.diagonal (score P.p dp)) (Matrix.diagonal (score P.p dp)) =
      fisherMetric P dp dp := by
  rw [quantumSLDInner_selfAdjoint_eq (diagFunctional_isPositiveStarFunctional _)
    (diagonal_star _) (diagonal_star _), diagonal_star, Matrix.diagonal_mul_diagonal,
    diagFunctional_apply, ← modelFisherInfo_eq_chentsov_fisherMetric]
  unfold modelFisherInfo toProbDist
  refine Finset.sum_congr rfl ?_
  intro a _
  simp [sq]

/-- For any `P : ProbDist α`, `quantumVariance (diagFunctional P) (Matrix.diagonal T)` equals
`statVariance P.p T`. -/
theorem quantumVariance_diag_eq_statVariance_probDist (P : ProbDist α) (T : α → ℝ) :
    quantumVariance (diagFunctional P) (Matrix.diagonal T) = statVariance P.p T := by
  have hm : diagFunctional P (Matrix.diagonal T) = statMeanOf P.p T := by
    rw [diagFunctional_apply]
    simp [statMeanOf]
  have hsub :
      Matrix.diagonal T - diagFunctional P (Matrix.diagonal T) • (1 : Matrix α α ℝ) =
        Matrix.diagonal fun a => T a - statMeanOf P.p T := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hm]
    · simp [hij]
  dsimp [quantumVariance]
  rw [hsub, Matrix.diagonal_mul_diagonal, diagFunctional_apply]
  unfold statVariance
  refine Finset.sum_congr rfl ?_
  intro a _
  simp [sq]

/-- On an interior distribution `P : ProbInterior α`, `quantumVariance` of `Matrix.diagonal T`
equals `statVariance P.p T`. -/
theorem quantumVariance_diag_eq_statVariance (P : ProbInterior α) (T : α → ℝ) :
    quantumVariance (diagFunctional (toProbDist P)) (Matrix.diagonal T) = statVariance P.p T :=
  quantumVariance_diag_eq_statVariance_probDist (toProbDist P) T

/-- **Classical Cramér–Rao Inequality Derived from Quantum SLD Cramér–Rao**:
specializing `sld_quantum_cramer_rao_inequality` to `diagFunctional (toProbDist P)`,
observable `Matrix.diagonal T`, and SLD operator `Matrix.diagonal (score P.p dp)` yields
`(∑ a, dp a * T a) ^ 2 ≤ statVariance P.p T * fisherMetric P dp dp`. -/
theorem classical_cramer_rao_from_quantum_sld (P : ProbInterior α) (dp T : α → ℝ)
    (hsum : ∑ a, dp a = 0) :
    (∑ a, dp a * T a) ^ 2 ≤ statVariance P.p T * fisherMetric P dp dp := by
  let ω := diagFunctional (toProbDist P)
  have hω : IsPositiveStarFunctional ω := diagFunctional_isPositiveStarFunctional _
  let X := Matrix.diagonal T
  let L := Matrix.diagonal (score P.p dp)
  have hcr := sld_quantum_cramer_rao_inequality hω (diagonal_star T) (diagonal_star (score P.p dp))
  have hcov : quantumSLDInner ω (X - ω X • 1) L = ∑ a, dp a * T a := by
    have hcent : X - ω X • (1 : Matrix α α ℝ) = Matrix.diagonal fun a => T a - statMeanOf P.p T := by
      have hm : ω X = statMeanOf P.p T := by
        dsimp [ω, X, toProbDist]
        rw [diagFunctional_apply]
        simp [statMeanOf]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [X, hm]
      · simp [X, hij]
    rw [quantumSLDInner_selfAdjoint_eq hω
      (centered_selfAdjoint (diagonal_star T) (ω X)) (diagonal_star _)]
    rw [centered_selfAdjoint (diagonal_star T) (ω X), hcent, Matrix.diagonal_mul_diagonal]
    dsimp [ω, toProbDist]
    rw [diagFunctional_apply]
    have hexp := expectation_score_eq_zero P dp hsum
    calc
      ∑ a, P.p a * (Matrix.diagonal (fun b => (T b - statMeanOf P.p T) * score P.p dp b) a a)
          = ∑ a, P.p a * ((T a - statMeanOf P.p T) * score P.p dp a) := by simp
      _ = ∑ a, (T a * (P.p a * score P.p dp a) - statMeanOf P.p T * (P.p a * score P.p dp a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
      _ = ∑ a, T a * (P.p a * score P.p dp a) -
            statMeanOf P.p T * ∑ a, P.p a * score P.p dp a := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = ∑ a, dp a * T a := by
            rw [hexp, mul_zero, sub_zero]
            refine Finset.sum_congr rfl ?_
            intro a _
            dsimp [score]
            have hne : P.p a ≠ 0 := ne_of_gt (P.pos a)
            field_simp [hne]
  rw [hcov, quantumVariance_diag_eq_statVariance P T, quantumSLDInner_diag_eq_fisherMetric P dp] at hcr
  exact hcr

end DiagonalState

/-! ### 3. Markov Kernels as Matrix Kraus Channels & Quantum-to-Classical Variance DPI -/

section MarkovKrausBridge

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Matrix Kraus operator `W_{(a, b)} = √(K(a, b)) |b⟩⟨a|` realizing a stochastic matrix `K`
as a completely positive trace-preserving Kraus channel on `Matrix α α ℝ`. -/
def markovKraus (K : MarkovKernel α α) (ab : α × α) : Matrix α α ℝ :=
  Matrix.of fun i j => if i = ab.2 ∧ j = ab.1 then Real.sqrt (K.T ab.1 ab.2) else 0

lemma markovKraus_star_mul_markovKraus_apply
    (K : MarkovKernel α α) (a₀ b₀ i j : α) :
    (star (markovKraus K (a₀, b₀)) * markovKraus K (a₀, b₀)) i j =
      if i = a₀ ∧ j = a₀ then K.T a₀ b₀ else 0 := by
  dsimp [Matrix.mul_apply, Matrix.star_apply, markovKraus]
  simp only [starRingEnd_apply, star_trivial]
  by_cases hij : i = a₀ ∧ j = a₀
  · rcases hij with ⟨hi, hj⟩
    rw [hi, hj]
    simp only [↓reduceIte, and_self]
    rw [Finset.sum_eq_single b₀]
    · simp [Real.mul_self_sqrt (K.nonneg a₀ b₀)]
    · intro k _ hne
      simp [hne]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  · simp only [hij, ↓reduceIte]
    refine Finset.sum_eq_zero ?_
    intro k _
    by_cases h1 : k = b₀ ∧ i = a₀ <;> by_cases h2 : k = b₀ ∧ j = a₀ <;>
      simp_all

/-- Exact Kraus completeness `∑ ab, W_ab* W_ab = 1` for every Markov kernel `K`. -/
theorem markovKraus_right_completeness (K : MarkovKernel α α) :
    ∑ ab : α × α, star (markovKraus K ab) * markovKraus K ab = 1 := by
  ext i j
  rw [Matrix.sum_apply, Fintype.sum_prod_type]
  simp_rw [markovKraus_star_mul_markovKraus_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Finset.sum_eq_single i]
    · simp [K.sum_one i]
    · intro a _ hne
      exact Finset.sum_eq_zero fun b _ => by simp [hne.symm]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  · rw [Matrix.one_apply_ne hij]
    refine Finset.sum_eq_zero ?_
    intro a _
    refine Finset.sum_eq_zero ?_
    intro b _
    by_cases h : i = a ∧ j = a
    · exact absurd (h.1.trans h.2.symm) hij
    · simp [h]

lemma krausChannel_markovKraus_diag_apply
    (K : MarkovKernel α α) (P : ProbDist α) (a₀ b₀ i j : α) :
    (markovKraus K (a₀, b₀) * diagState P * star (markovKraus K (a₀, b₀))) i j =
      if i = b₀ ∧ j = b₀ then P.p a₀ * K.T a₀ b₀ else 0 := by
  dsimp [Matrix.mul_apply, Matrix.star_apply, markovKraus, diagState]
  simp only [starRingEnd_apply, star_trivial]
  by_cases hij : i = b₀ ∧ j = b₀
  · rcases hij with ⟨hi, hj⟩
    rw [hi, hj]
    simp only [↓reduceIte, and_self]
    rw [Finset.sum_eq_single a₀]
    · rw [Finset.sum_eq_single a₀]
      · simp only [↓reduceIte, Matrix.diagonal_apply_eq, and_self]
        calc
          Real.sqrt (K.T a₀ b₀) * P.p a₀ * Real.sqrt (K.T a₀ b₀)
              = P.p a₀ * (Real.sqrt (K.T a₀ b₀) * Real.sqrt (K.T a₀ b₀)) := by ring
          _ = P.p a₀ * K.T a₀ b₀ := by rw [Real.mul_self_sqrt (K.nonneg a₀ b₀)]
      · intro l _ hne
        simp [hne]
      · intro hmem
        exact (hmem (Finset.mem_univ _)).elim
    · intro k _ hne
      simp [hne]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  · simp only [hij, ↓reduceIte]
    refine Finset.sum_eq_zero ?_
    intro k _
    by_cases hjk : j = b₀ ∧ k = a₀
    · have hi : i ≠ b₀ := fun hi => hij ⟨hi, hjk.1⟩
      have hsum0 :
          ∑ x, (if i = b₀ ∧ x = a₀ then Real.sqrt (K.T a₀ b₀) else 0) * Matrix.diagonal P.p x k = 0 :=
        Finset.sum_eq_zero fun x _ => by simp [hi]
      rw [hsum0, zero_mul]
    · simp [hjk]

/-- Forward Markov pushforward equals the forward matrix Kraus channel on diagonal states:
`krausChannel (markovKraus K) (diagState P) = diagState (pushforward K P)`. -/
theorem krausChannel_markovKraus_diagState (K : MarkovKernel α α) (P : ProbDist α) :
    krausChannel (markovKraus K) (diagState P) = diagState (pushforward K P) := by
  ext i j
  unfold krausChannel
  rw [Matrix.sum_apply, Fintype.sum_prod_type]
  simp_rw [krausChannel_markovKraus_diag_apply]
  by_cases hij : i = j
  · subst hij
    rw [diagState, Matrix.diagonal_apply_eq, Finset.sum_comm, Finset.sum_eq_single i]
    · simp [pushforward]
    · intro b _ hne
      exact Finset.sum_eq_zero fun a _ => by simp [hne.symm]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  · rw [diagState, Matrix.diagonal_apply_ne _ hij]
    refine Finset.sum_eq_zero ?_
    intro a _
    refine Finset.sum_eq_zero ?_
    intro b _
    by_cases h : i = b ∧ j = b
    · exact absurd (h.1.trans h.2.symm) hij
    · simp [h]

lemma krausDual_markovKraus_apply
    (K : MarkovKernel α α) (M : Matrix α α ℝ) (a₀ b₀ i j : α) :
    (star (markovKraus K (a₀, b₀)) * M * markovKraus K (a₀, b₀)) i j =
      if i = a₀ ∧ j = a₀ then K.T a₀ b₀ * M b₀ b₀ else 0 := by
  dsimp [Matrix.mul_apply, Matrix.star_apply, markovKraus]
  simp only [starRingEnd_apply, star_trivial]
  by_cases hij : i = a₀ ∧ j = a₀
  · rcases hij with ⟨hi, hj⟩
    rw [hi, hj]
    simp only [↓reduceIte, and_self]
    rw [Finset.sum_eq_single b₀]
    · rw [Finset.sum_eq_single b₀]
      · simp only [↓reduceIte, and_self]
        calc
          Real.sqrt (K.T a₀ b₀) * M b₀ b₀ * Real.sqrt (K.T a₀ b₀)
              = (Real.sqrt (K.T a₀ b₀) * Real.sqrt (K.T a₀ b₀)) * M b₀ b₀ := by ring
          _ = K.T a₀ b₀ * M b₀ b₀ := by rw [Real.mul_self_sqrt (K.nonneg a₀ b₀)]
      · intro k _ hne
        simp [hne]
      · intro hmem
        exact (hmem (Finset.mem_univ _)).elim
    · intro l _ hne
      simp [hne]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  · simp only [hij, ↓reduceIte]
    refine Finset.sum_eq_zero ?_
    intro l _
    by_cases hjl : l = b₀ ∧ j = a₀
    · have hi : i ≠ a₀ := fun hi => hij ⟨hi, hjl.2⟩
      have hsum0 : ∑ k, (if k = b₀ ∧ i = a₀ then Real.sqrt (K.T a₀ b₀) else 0) * M k l = 0 :=
        Finset.sum_eq_zero fun k _ => by simp [hi]
      rw [hsum0, zero_mul]
    · simp [hjl]

/-- Backward Heisenberg Kraus action on a diagonal observable `Matrix.diagonal f` computes
exact Markov conditional expectation `a ↦ ∑ b, K.T a b * f b`. -/
theorem krausDual_markovKraus_diagonal (K : MarkovKernel α α) (f : α → ℝ) :
    krausDual (markovKraus K) (Matrix.diagonal f) =
      Matrix.diagonal fun a => ∑ b, K.T a b * f b := by
  ext i j
  unfold krausDual
  rw [Matrix.sum_apply, Fintype.sum_prod_type]
  simp_rw [krausDual_markovKraus_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl ?_
      intro b _
      simp
    · intro a _ hne
      exact Finset.sum_eq_zero fun b _ => by simp [hne.symm]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  · rw [Matrix.diagonal_apply_ne _ hij]
    refine Finset.sum_eq_zero ?_
    intro a _
    refine Finset.sum_eq_zero ?_
    intro b _
    by_cases h : i = a ∧ j = a
    · exact absurd (h.1.trans h.2.symm) hij
    · simp [h]

/-- Duality between `krausDualLinear (markovKraus K)` and `pushforward K P` on `Matrix α α ℝ`. -/
theorem diagFunctional_comp_krausDual_markovKraus
    (K : MarkovKernel α α) (P : ProbDist α) :
    (diagFunctional P).comp (krausDualLinear (markovKraus K)) = diagFunctional (pushforward K P) := by
  ext M
  change diagFunctional P (krausDual (markovKraus K) M) = diagFunctional (pushforward K P) M
  rw [diagFunctional_apply, diagFunctional_apply]
  have hdiag (a : α) :
      (krausDual (markovKraus K) M) a a = ∑ b, K.T a b * M b b := by
    unfold krausDual
    rw [Matrix.sum_apply, Fintype.sum_prod_type]
    simp_rw [krausDual_markovKraus_apply]
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl ?_
      intro b _
      simp
    · intro a₀ _ hne
      exact Finset.sum_eq_zero fun b₀ _ => by simp [hne.symm]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  simp_rw [hdiag]
  calc
    ∑ a, P.p a * ∑ b, K.T a b * M b b
        = ∑ a, ∑ b, (P.p a * K.T a b) * M b b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          ring
    _ = ∑ b, ∑ a, (P.p a * K.T a b) * M b b := Finset.sum_comm
    _ = ∑ b, (∑ a, P.p a * K.T a b) * M b b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [← Finset.sum_mul]
    _ = ∑ b, (pushforward K P).p b * M b b := rfl

/-- **Markov Conditional-Expectation Variance Contraction Derived from Operator Kadison–Schwarz**:
specializing `krausDual_quantumVariance_le` to `diagFunctional P` and `markovKraus K` yields
`Var_P(E[f | ·]) ≤ Var_{K_* P}(f)` directly from noncommutative operator theory. -/
theorem markov_conditional_expectation_variance_contraction
    (K : MarkovKernel α α) (P : ProbDist α) (f : α → ℝ) :
    statVariance P.p (fun a => ∑ b, K.T a b * f b) ≤ statVariance (pushforward K P).p f := by
  have hkv :=
    krausDual_quantumVariance_le
      (ω := diagFunctional P) (diagFunctional_isPositiveStarFunctional P)
      (markovKraus K) (markovKraus_right_completeness K) (diagonal_star f)
  rw [krausDual_markovKraus_diagonal K f, diagFunctional_comp_krausDual_markovKraus K P,
    quantumVariance_diag_eq_statVariance_probDist P _,
    quantumVariance_diag_eq_statVariance_probDist (pushforward K P) f] at hkv
  exact hkv

end MarkovKrausBridge

end InfoGeometry.Foundations.ClassicalToOperatorInformationBridge

end section
