/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Epistemology.ChentsovMetricInvariance

/-!
# Rational uniqueness for ambiently invariant bilinear families

`InvariantMetricFamily` stores symmetric bilinear forms on the full coordinate
spaces `α → ℝ`, together with partition-embedding invariance for **all** input
vectors. This is stronger than the usual tangent-only naturality hypothesis.
The uniqueness result below concerns the restriction of each form to zero-sum
tangent vectors; it therefore proves uniqueness for this stronger ambient
extension class, not the tangent-only form of Chentsov's theorem.

Main result (`chentsov_uniqueness_rational`): there is one real constant `c` such that,
for every finite type `α`, every rational interior distribution `P` and all tangent
vectors `u v` (zero coordinate sum), `F.g α P u v = c * fisherMetric P u v`.

Proof outline:
* permutation embeddings force the Gram matrix at the uniform distribution to be
  `a` on the diagonal and `b` off it, so `F` is a multiple of Fisher at the uniform point;
* block embeddings `(Σ i, Fin (m i)) → α` and equivalences transfer the scale between
  types, pinning it to a single reference value computed on `Bool`;
* a rational distribution `P i = m i / N` is pushed onto the uniform distribution on
  `Σ i, Fin (m i)`, where the scale is already known.
-/

namespace InfoGeometry.Epistemology.ChentsovUniqueness

open Finset
open scoped BigOperators
open InfoGeometry.Epistemology.ChentsovMetricInvariance

/-! ### 1. Interior distributions -/

theorem probInterior_ext {α : Type} [Fintype α] {P Q : ProbInterior α}
    (h_eq : P.p = Q.p) : P = Q := by
  cases P
  cases Q
  cases h_eq
  rfl

/-- The uniform interior distribution on a nonempty finite type. -/
noncomputable def uniformInterior (α : Type) [Fintype α] [Nonempty α] : ProbInterior α where
  p := fun _ => 1 / (Fintype.card α : ℝ)
  pos := fun _ => by have := Fintype.card_pos (α := α); positivity
  sum_one := by
    have h_card : (Fintype.card α : ℝ) ≠ 0 := by
      have := Fintype.card_pos (α := α); positivity
    simp [Finset.card_univ, h_card]

/-- An interior distribution with constant weights is the uniform distribution. -/
theorem eq_uniform_of_const {α : Type} [Fintype α] [Nonempty α] (Q : ProbInterior α)
    (h_const : ∀ a b, Q.p a = Q.p b) : Q = uniformInterior α := by
  apply probInterior_ext
  funext a
  have h_sum : ∑ b, Q.p b = (Fintype.card α : ℝ) * Q.p a := by
    rw [Finset.sum_congr rfl (fun b _ => h_const b a)]
    simp [Finset.card_univ]
  have h_card : (Fintype.card α : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := α); positivity
  show Q.p a = 1 / (Fintype.card α : ℝ)
  rw [Q.sum_one] at h_sum
  field_simp
  linarith

/-! ### 2. Pushforwards along partition embeddings -/

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]

/-- Interior pushforward of `P` along a partition embedding. -/
noncomputable def pushP (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) :
    ProbInterior β :=
  congruentPushforwardInterior (partitionEmbeddingToKernel E) P (partitionEmbedding_weight_pos E)

/-- Pushforward of a coordinate vector along a partition embedding. -/
def pushV (E : CongruentPartitionEmbedding α β) (u : α → ℝ) : β → ℝ :=
  pushforwardTangentVec (partitionEmbeddingToKernel E).kernel u

theorem pushP_apply (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (b : β) :
    (pushP E P).p b = P.p (E.π b) * E.c b := by
  show (VariationalRG.pushforward _ (toProbDist P)).p b = _
  rw [congruent_pushforward_at]
  simp [partitionEmbeddingToKernel]

theorem pushV_apply (E : CongruentPartitionEmbedding α β) (u : α → ℝ) (b : β) :
    pushV E u b = u (E.π b) * E.c b := by
  rw [pushV, congruent_pushforward_tangent_at]
  simp [partitionEmbeddingToKernel]

theorem pushV_sum_zero (E : CongruentPartitionEmbedding α β) {u : α → ℝ}
    (hu : ∑ i, u i = 0) : ∑ b, pushV E u b = 0 :=
  pushforwardTangent_sum_zero _ ⟨u, hu⟩

theorem fisherMetric_pushP (E : CongruentPartitionEmbedding α β) (P : ProbInterior α)
    (u v : α → ℝ) :
    fisherMetric (pushP E P) (pushV E u) (pushV E v) = fisherMetric P u v :=
  chentsov_partition_embedding_fisher_invariance E P u v

/-- If the pushed weights are constant, the pushforward is uniform. -/
theorem pushP_eq_uniform [Nonempty β] (E : CongruentPartitionEmbedding α β)
    (P : ProbInterior α) (h_const : ∀ b b', P.p (E.π b) * E.c b = P.p (E.π b') * E.c b') :
    pushP E P = uniformInterior β :=
  eq_uniform_of_const _ fun b b' => by rw [pushP_apply, pushP_apply, h_const b b']

/-! ### 3. Equivalence and block embeddings -/

/-- An equivalence `σ : α ≃ β` as a partition embedding with unit weights. -/
def ofEquiv (σ : α ≃ β) : CongruentPartitionEmbedding α β where
  π := σ.symm
  c := fun _ => 1
  c_pos := fun _ => zero_lt_one
  partition_sum a := by
    have h_fib : (Finset.univ.filter fun b => σ.symm b = a) = {σ a} := by
      ext b
      simp [Equiv.symm_apply_eq]
    rw [h_fib, Finset.sum_singleton]

theorem pushV_ofEquiv_single (σ : α ≃ β) [DecidableEq β] (i : α) :
    pushV (ofEquiv σ) (Pi.single i 1) = Pi.single (σ i) 1 := by
  funext b
  rw [pushV_apply]
  simp [ofEquiv, Pi.single_apply, Equiv.symm_apply_eq]

theorem pushP_ofEquiv_uniform [Nonempty α] [Nonempty β] (σ : α ≃ β) :
    pushP (ofEquiv σ) (uniformInterior α) = uniformInterior β :=
  pushP_eq_uniform _ _ fun _ _ => rfl

/-- The block embedding splitting outcome `i` into `m i` equally weighted outcomes. -/
noncomputable def blockEmbedding (m : α → ℕ) (hm : ∀ i, 0 < m i) :
    CongruentPartitionEmbedding α (Σ i, Fin (m i)) where
  π := Sigma.fst
  c b := 1 / (m b.1 : ℝ)
  c_pos b := by have := hm b.1; positivity
  partition_sum a := by
    have h_inner : ∀ i, (∑ _x : Fin (m i), if i = a then 1 / (m i : ℝ) else 0) =
        if i = a then 1 else 0 := by
      intro i
      split_ifs with hia
      · subst hia
        have h_ne : (m i : ℝ) ≠ 0 := by have := hm i; positivity
        simp [h_ne]
      · simp
    rw [Finset.sum_filter, Fintype.sum_sigma]
    rw [Finset.sum_congr rfl (fun i _ => h_inner i)]
    simp

theorem blockEmbedding_c (m : α → ℕ) (hm : ∀ i, 0 < m i) (b : Σ i, Fin (m i)) :
    (blockEmbedding m hm).c b = 1 / (m b.1 : ℝ) := rfl

theorem blockEmbedding_π (m : α → ℕ) (hm : ∀ i, 0 < m i) (b : Σ i, Fin (m i)) :
    (blockEmbedding m hm).π b = b.1 := rfl

/-! ### 4. Invariant metric families -/

/-- Ambient bilinear extensions on simplex interiors, invariant under every
partition embedding on arbitrary coordinate vectors. This explicit ambient
naturality is stronger than requiring invariance only for zero-sum tangent vectors. -/
structure InvariantMetricFamily where
  g : ∀ (α : Type) [Fintype α], ProbInterior α → (α → ℝ) → (α → ℝ) → ℝ
  add_left : ∀ (α : Type) [Fintype α] (P : ProbInterior α) (u v w : α → ℝ),
    g α P (u + v) w = g α P u w + g α P v w
  smul_left : ∀ (α : Type) [Fintype α] (P : ProbInterior α) (r : ℝ) (u w : α → ℝ),
    g α P (r • u) w = r * g α P u w
  symm : ∀ (α : Type) [Fintype α] (P : ProbInterior α) (u v : α → ℝ),
    g α P u v = g α P v u
  invariant : ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (u v : α → ℝ),
    g β (pushP E P) (pushV E u) (pushV E v) = g α P u v

theorem fisherMetric_add_left {γ : Type} [Fintype γ] (P : ProbInterior γ) (u v w : γ → ℝ) :
    fisherMetric P (u + v) w = fisherMetric P u w + fisherMetric P v w := by
  unfold fisherMetric
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.add_apply, add_mul, add_div]

/-- The family `c • Fisher`. -/
noncomputable def scaledFisherFamily (c : ℝ) : InvariantMetricFamily where
  g := fun _ _ P u v => c * fisherMetric P u v
  add_left := fun _ _ P u v w => by rw [fisherMetric_add_left, mul_add]
  smul_left := fun _ _ P r u w => by
    rw [show r • u = fun a => r * u a from rfl, fisherMetric_smul_left, mul_left_comm]
  symm := fun _ _ P u v => by rw [fisherMetric_symm]
  invariant := fun E P u v => by rw [fisherMetric_pushP]

/-- Closed witness: the Fisher metric family itself. -/
noncomputable def fisherFamily : InvariantMetricFamily := scaledFisherFamily 1

noncomputable instance : Inhabited InvariantMetricFamily := ⟨fisherFamily⟩

theorem fisherFamily_g (γ : Type) [Fintype γ] (P : ProbInterior γ) (u v : γ → ℝ) :
    fisherFamily.g γ P u v = fisherMetric P u v := one_mul _

namespace InvariantMetricFamily

variable (F : InvariantMetricFamily) {γ : Type} [Fintype γ]

theorem zero_left (P : ProbInterior γ) (w : γ → ℝ) : F.g γ P 0 w = 0 := by
  have h := F.smul_left γ P 0 0 w
  rwa [zero_smul, zero_mul] at h

theorem sum_left {ι : Type} (P : ProbInterior γ) (s : Finset ι) (f : ι → γ → ℝ)
    (w : γ → ℝ) : F.g γ P (∑ i ∈ s, f i) w = ∑ i ∈ s, F.g γ P (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using F.zero_left P w
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, F.add_left, ih]

theorem eq_sum_single (u : γ → ℝ) [DecidableEq γ] :
    u = ∑ i, u i • (Pi.single i 1 : γ → ℝ) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- Coordinate expansion in the left argument. -/
theorem expand_left [DecidableEq γ] (P : ProbInterior γ) (u w : γ → ℝ) :
    F.g γ P u w = ∑ i, u i * F.g γ P (Pi.single i 1) w := by
  conv_lhs => rw [eq_sum_single u]
  rw [F.sum_left]
  exact Finset.sum_congr rfl fun i _ => F.smul_left γ P _ _ w

/-- (L1) Full coordinate expansion through the Gram matrix. -/
theorem expand [DecidableEq γ] (P : ProbInterior γ) (u v : γ → ℝ) :
    F.g γ P u v = ∑ i, ∑ j, u i * v j * F.g γ P (Pi.single i 1) (Pi.single j 1) := by
  rw [F.expand_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [F.symm, F.expand_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [F.symm γ P (Pi.single j 1)]
  ring

/-- Gram form for a matrix that is `a` on the diagonal and `b` off it. -/
theorem gram_formula [DecidableEq γ] (P : ProbInterior γ) {a b : ℝ}
    (h_diag : ∀ i, F.g γ P (Pi.single i 1) (Pi.single i 1) = a)
    (h_off : ∀ i j, i ≠ j → F.g γ P (Pi.single i 1) (Pi.single j 1) = b)
    (u v : γ → ℝ) (hv : ∑ j, v j = 0) :
    F.g γ P u v = (a - b) * ∑ i, u i * v i := by
  have h_entry : ∀ i j, u i * v j * F.g γ P (Pi.single i 1) (Pi.single j 1) =
      u i * b * v j + if i = j then u i * v i * (a - b) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [h_diag]; simp only [↓reduceIte]; ring
    · rw [h_off i j hij]; simp only [hij, ↓reduceIte]; ring
  rw [F.expand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (fun j _ => h_entry i j), Finset.sum_add_distrib,
    ← Finset.mul_sum, hv, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  ring

/-! ### 5. Scale at a point and its transfer -/

/-- `F` equals `k • Fisher` on the tangent space at `P`. -/
def HasScale (γ : Type) [Fintype γ] (P : ProbInterior γ) (k : ℝ) : Prop :=
  ∀ u v : γ → ℝ, ∑ i, u i = 0 → ∑ i, v i = 0 → F.g γ P u v = k * fisherMetric P u v

/-- A scale at the image of a partition embedding transfers to the source point. -/
theorem hasScale_of_push (E : CongruentPartitionEmbedding α β) {P : ProbInterior α}
    {Q : ProbInterior β} (hPQ : pushP E P = Q) {k : ℝ} (hQ : F.HasScale β Q k) :
    F.HasScale α P k := by
  intro u v hu hv
  rw [← F.invariant E P u v, hPQ, hQ _ _ (pushV_sum_zero E hu) (pushV_sum_zero E hv), ← hPQ,
    fisherMetric_pushP]

/-! ### 6. The uniform point -/

/-- (L2) Permutation invariance of the Gram matrix at the uniform distribution. -/
theorem gram_perm [DecidableEq γ] [Nonempty γ] (σ : γ ≃ γ) (i j : γ) :
    F.g γ (uniformInterior γ) (Pi.single (σ i) 1) (Pi.single (σ j) 1) =
      F.g γ (uniformInterior γ) (Pi.single i 1) (Pi.single j 1) := by
  have h := F.invariant (ofEquiv σ) (uniformInterior γ) (Pi.single i 1) (Pi.single j 1)
  rwa [pushP_ofEquiv_uniform, pushV_ofEquiv_single, pushV_ofEquiv_single] at h

theorem fisherMetric_uniform [Nonempty γ] (u v : γ → ℝ) :
    fisherMetric (uniformInterior γ) u v = (Fintype.card γ : ℝ) * ∑ i, u i * v i := by
  unfold fisherMetric
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show u i * v i / (1 / (Fintype.card γ : ℝ)) = _
  rw [div_div_eq_mul_div, div_one, mul_comm]

/-- (L3) At the uniform distribution on a type with two distinct points, `F` is a
multiple of the Fisher metric on tangent vectors. -/
theorem hasScale_uniform_exists [DecidableEq γ] [Nonempty γ] {i₀ j₀ : γ} (h_ne : i₀ ≠ j₀) :
    ∃ k, F.HasScale γ (uniformInterior γ) k := by
  set G := fun i j : γ => F.g γ (uniformInterior γ) (Pi.single i 1) (Pi.single j 1) with hG
  have h_diag : ∀ i, G i i = G i₀ i₀ := by
    intro i
    have h := F.gram_perm (Equiv.swap i₀ i) i₀ i₀
    rwa [Equiv.swap_apply_left] at h
  have h_off : ∀ i j, i ≠ j → G i j = G i₀ j₀ := by
    intro i j hij
    set j' := Equiv.swap i₀ i j₀ with hj'
    have h_j'i : j' ≠ i := by
      intro h_eq
      apply h_ne
      exact (Equiv.swap i₀ i).injective (by rw [← hj', h_eq, Equiv.swap_apply_left])
    have h_perm := F.gram_perm ((Equiv.swap i₀ i).trans (Equiv.swap j' j)) i₀ j₀
    rwa [Equiv.trans_apply, Equiv.trans_apply, Equiv.swap_apply_left, ← hj',
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm h_j'i) hij] at h_perm
  have h_card : (Fintype.card γ : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := γ); positivity
  refine ⟨(G i₀ i₀ - G i₀ j₀) / Fintype.card γ, fun u v _ hv => ?_⟩
  rw [F.gram_formula _ h_diag h_off u v hv, fisherMetric_uniform]
  field_simp

/-! ### 7. A single global constant -/

/-- Reference tangent vector on `Bool`. -/
def boolTangent : Bool → ℝ := fun b => if b then 1 else -1

theorem boolTangent_sum : ∑ b, boolTangent b = 0 := by simp [boolTangent]

theorem fisher_boolTangent_ne :
    fisherMetric (uniformInterior Bool) boolTangent boolTangent ≠ 0 := by
  refine ne_of_gt (fisherMetric_pos_of_ne_zero _ _ fun h_eq => ?_)
  have h := congrFun h_eq true
  simp [boolTangent] at h

/-- The reference scale of `F`, read off on `Bool`. -/
noncomputable def refScale : ℝ :=
  F.g Bool (uniformInterior Bool) boolTangent boolTangent /
    fisherMetric (uniformInterior Bool) boolTangent boolTangent

theorem eq_refScale {k : ℝ} (hk : F.HasScale Bool (uniformInterior Bool) k) :
    k = F.refScale :=
  (eq_div_of_mul_eq fisher_boolTangent_ne
    (hk _ _ boolTangent_sum boolTangent_sum).symm)

/-- (L4) The constant block embedding maps the uniform distribution to the uniform one. -/
theorem pushP_block_uniform [Nonempty α] (n : ℕ) (hn : 0 < n)
    [Nonempty (Σ _ : α, Fin n)] :
    pushP (blockEmbedding (fun _ => n) fun _ => hn) (uniformInterior α) =
      uniformInterior (Σ _ : α, Fin n) :=
  pushP_eq_uniform _ _ fun _ _ => rfl

/-- (L4) On every nonempty finite type, `F` is `refScale F` times Fisher at the uniform point. -/
theorem hasScale_uniform (δ : Type) [Fintype δ] [DecidableEq δ] [Nonempty δ] :
    F.HasScale δ (uniformInterior δ) F.refScale := by
  have h_pos : 0 < Fintype.card δ := Fintype.card_pos
  obtain ⟨d₀⟩ := ‹Nonempty δ›
  have : Nonempty (Σ _ : Bool, Fin (Fintype.card δ)) := ⟨⟨true, ⟨0, h_pos⟩⟩⟩
  have : Nonempty (Σ _ : δ, Fin 2) := ⟨⟨d₀, 0⟩⟩
  have h_ne : (⟨true, ⟨0, h_pos⟩⟩ : Σ _ : Bool, Fin (Fintype.card δ)) ≠ ⟨false, ⟨0, h_pos⟩⟩ := by
    simp
  obtain ⟨k, hk⟩ := F.hasScale_uniform_exists h_ne
  have h_bool := F.hasScale_of_push _ (pushP_block_uniform (α := Bool) _ h_pos) hk
  have h_card : Fintype.card (Σ _ : δ, Fin 2) = Fintype.card (Σ _ : Bool, Fin (Fintype.card δ)) := by
    simp [Fintype.card_sigma, mul_comm]
  have h_mid := F.hasScale_of_push _ (pushP_ofEquiv_uniform (Fintype.equivOfCardEq h_card)) hk
  have h_base := F.hasScale_of_push _ (pushP_block_uniform (α := δ) 2 two_pos) h_mid
  rwa [← F.eq_refScale h_bool]

/-! ### 8. Rational reduction -/

omit [DecidableEq α] in
theorem rational_count_pos {P : ProbInterior α} {N : ℕ} {m : α → ℕ}
    (hm : ∀ i, P.p i = m i / N) (i : α) : 0 < m i := by
  have h := P.pos i
  rw [hm i] at h
  rcases Nat.eq_zero_or_pos (m i) with h0 | h0
  · rw [h0, Nat.cast_zero, zero_div] at h
    exact absurd h (lt_irrefl 0)
  · exact h0

/-- (L5) A rational distribution is pushed onto the uniform distribution of its blocks. -/
theorem pushP_block_rational {P : ProbInterior α} {N : ℕ} {m : α → ℕ}
    (hm : ∀ i, P.p i = m i / N) [Nonempty (Σ i, Fin (m i))] :
    pushP (blockEmbedding m (rational_count_pos hm)) P = uniformInterior (Σ i, Fin (m i)) := by
  have h_val : ∀ b : Σ i, Fin (m i), P.p ((blockEmbedding m (rational_count_pos hm)).π b) *
      (blockEmbedding m (rational_count_pos hm)).c b = 1 / N := by
    intro b
    have h_ne : (m b.1 : ℝ) ≠ 0 := by have := rational_count_pos hm b.1; positivity
    rw [blockEmbedding_π, blockEmbedding_c, hm b.1]
    field_simp
  exact pushP_eq_uniform _ _ fun b b' => by rw [h_val b, h_val b']

omit [DecidableEq α] in
theorem nonempty_of_probInterior (P : ProbInterior α) : Nonempty α := by
  by_contra h_empty
  rw [not_nonempty_iff] at h_empty
  have h := P.sum_one
  simp at h

end InvariantMetricFamily

/-! ### 9. Chentsov uniqueness on rational points -/

/-- **Chentsov uniqueness at rational points (ambient-invariance form).** Every
ambiently invariant metric family (`InvariantMetricFamily`) is a single constant
multiple of the Fisher metric on the simplex tangent space at all rational
interior distributions. (For the tangent-only invariance formulation, see
`InfoGeometry.Epistemology.ChentsovTangentUniqueness`.) -/
theorem chentsov_uniqueness_rational (F : InvariantMetricFamily) :
    ∃ c : ℝ, ∀ (α : Type) [Fintype α] [DecidableEq α] (P : ProbInterior α),
      (∃ (N : ℕ) (m : α → ℕ), ∀ i, P.p i = m i / N) →
      ∀ u v : α → ℝ, ∑ i, u i = 0 → ∑ i, v i = 0 →
        F.g α P u v = c * fisherMetric P u v := by
  refine ⟨F.refScale, fun α _ _ P hP u v hu hv => ?_⟩
  obtain ⟨N, m, hm⟩ := hP
  obtain ⟨i₀⟩ := InvariantMetricFamily.nonempty_of_probInterior P
  have : Nonempty (Σ i, Fin (m i)) :=
    ⟨⟨i₀, ⟨0, InvariantMetricFamily.rational_count_pos hm i₀⟩⟩⟩
  exact F.hasScale_of_push _ (InvariantMetricFamily.pushP_block_rational hm)
    (F.hasScale_uniform _) u v hu hv

/-- Every scalar multiple of Fisher is an ambiently invariant family. Together with
`chentsov_uniqueness_rational`, this gives the tangent-restriction classification;
it does not classify the ambient extensions away from zero-sum vectors. -/
theorem chentsov_rational_classification (c : ℝ) :
    ∃ F : InvariantMetricFamily, ∀ (α : Type) [Fintype α] (P : ProbInterior α) (u v : α → ℝ),
      F.g α P u v = c * fisherMetric P u v :=
  ⟨scaledFisherFamily c, fun _ _ _ _ _ => rfl⟩

end InfoGeometry.Epistemology.ChentsovUniqueness
