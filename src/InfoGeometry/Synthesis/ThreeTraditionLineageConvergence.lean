/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Epistemology.ChentsovMetricInvariance
import InfoGeometry.Epistemology.ChentsovUniquenessContinuous
import InfoGeometry.Epistemology.SubmersionSplitFinrank
import InfoGeometry.QuantumContext.AttentionKMSState
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
import InfoGeometry.SuperGrassmannian.UnorientedSuperGrassmannianCPT
import InfoGeometry.SuperGrassmannian.SuperGrassmannianProjectorBridge
import InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
import InfoGeometry.Canonical.GrandEpistemicGeometricSynthesis

/-!
# Three-Tradition Lineage Convergence: Information Geometry, Operator Algebras, and Para-Kähler Supergeometry

This module constructs genuine cross-tradition definitions and bridge theorems uniting the six
foundational mathematical lineages across the repository without 1-line forwarding wrappers or
conjunction bundling:

1. **Section 1 — Statistical Invariance Lineage (Rao 1945 / Chentsov 1972 $\longleftrightarrow$ KMS Softmax Interior)**:
   - Constructs `softmaxProbInterior logits β : ChentsovMetricInvariance.ProbInterior α` directly
     from the Gibbs/Boltzmann softmax thermal weights of `AttentionKMSState`.
   - Proves `chentsov_softmax_partition_embedding_fisher_invariance` uniting Chentsov's congruent
     partition-embedding isometry with the explicit softmax Fisher sum
     $\sum_i \frac{u_i v_i}{\rho_i(\beta)}$, and `chentsov_seqContinuous_at_softmax_interior`
     specializing sequentially continuous invariant metric classification to `softmaxProbInterior`.

2. **Section 2 — Information-Geometric Flow & Submersion Pruning Lineage (O'Neill 1966 / Amari 1985–1998 $\longleftrightarrow$ Libermann Para-Kähler Split)**:
   - Constructs `paraKahlerSubmersionSplit K hK : RiemannianSubmersion.SubmersionSplit V` from the
     spectral projectors `SuperGrassmannian.paraProjectorPlus K` and `paraProjectorMinus K`.
   - Proves `paraKahler_projV_eq_zero_of_mem_primalSheet`, submodule complementarity
     `isCompl_primalSheet_covectorVacuumSheet`, exact dimension decomposition
     `finrank_eq_primalSheet_add_covectorVacuumSheet`, and strict cubic FLOP reduction
     `paraKahler_primalSheet_cubic_cost_lt` on the primal eigen-sheet.

3. **Section 3 — Modular Operator Theory & Attention Sink Lineage (KMS 1957–1959 / Tomita–Takesaki 1970 $\longleftrightarrow$ Simplex Interior & Cuntz Colimit)**:
   - Proves `attentionState_eq_softmaxProbInterior_sum` and the cross-tradition colimit modular-flow
     readout theorem `kms_colimit_modularFlow_readout_eq_softmaxProbInterior_sum` uniting
     `selectedStageColimitFunctional`, `rawMap`, `modularFlow`, and `softmaxProbInterior`.
   - Proves `prunedState_anchor_bound_le_diagonal_sum` and explicit non-commutativity witnesses on
     the two-token matrix algebra.

4. **Section 4 — $CPT$ & Spacetime Symmetries Lineage (Bisognano–Wichmann 1975 / Borchers 1992 $\longleftrightarrow$ Spectral Projectors $P^\pm$)**:
   - Proves the coordinate evaluations `paraProjectorPlus_K_op_apply` and
     `paraProjectorMinus_K_op_apply` on `ModularCPT.DoubledCarrier E`.
   - Proves that modular `CPT_op` intertwines `SuperGrassmannian.paraProjectorPlus` and
     `paraProjectorMinus` (`cpt_intertwines_paraProjectorPlus_paraProjectorMinus`,
     `cpt_intertwines_paraProjectorMinus_paraProjectorPlus`) and maps `primalSubspace` into
     `vacuumSubspace` (`cpt_maps_primalSubspace_to_vacuumSubspace`).

5. **Section 5 — Neutral & Para-Kähler Geometry Lineage (Libermann 1954 / Cruceanu–Fortuny–Gadea 1996 $\longleftrightarrow$ Zorn Split-Octonions)**:
   - Proves submodule equalities `libermann_lineage_doubled_paraK_primalSheet`
     (`SuperGrassmannian.primalSheet K_op = ModularCPT.primalSubspace`) and
     `libermann_lineage_doubled_paraK_vacuumSheet`
     (`SuperGrassmannian.covectorVacuumSheet K_op = ModularCPT.vacuumSubspace`).
   - Bridges the 6D Zorn phase space `SplitOctonionParaKahlerNullCone.ParaKahlerVec ℝ` to
     `ModularCPT.DoubledCarrier (Fin 3 → ℝ)` via `paraKahlerVecToDoubled`, proving equivariance
     under the para-complex involution (`paraKahlerVecToDoubled_paraComplexK`) and sheet inclusions
     (`paraKahlerVecToDoubled_primalSheet_mem_primalSheet`,
     `paraKahlerVecToDoubled_dualSheet_mem_covectorVacuumSheet`).

6. **Section 6 — Supergeometry, Orientifolds & Categorical Colimit Lineage (Berezin 1966 / Manin 1988 / Polchinski 1996)**:
   - Proves that the unoriented Möbius twist `moebiusTwist` intertwines `paraProjectorPlus` and
     `paraProjectorMinus`, preserves the split Krein metric (`kreinForm_moebiusTwist_invariant`),
     negates the canonical symplectic form (`symplecticForm_moebiusTwist_anti_invariant`), and
     transposes `SuperGrassmannian.primalSheet K_op` with `covectorVacuumSheet K_op`.
   - Proves multi-step `TensorTowerColimit.iota_seq` horizontal-vertical decomposition
     (`colimit_lineage_iota_seq_eq_add_projH_projV`) and vanishing vertical drift across tower
     transitions (`colimit_lineage_projV_iota_seq_projH_eq_zero`).

## Scope Note

All theorems in this synthesis module are exact algebraic, linear-algebraic, or sequentially
continuous simplex-interior identities proved over finite types, real modules, or inductive matrix
and module towers. No analytical continuations, infinite-dimensional Hilbert-space completions, or
unproved physical axioms are assumed.
-/

namespace InfoGeometry.Synthesis.ThreeTraditionLineageConvergence

open scoped BigOperators
open InfoGeometry.Epistemology
open InfoGeometry.Canonical
open InfoGeometry.Export
open InfoGeometry.QuantumContext
open InfoGeometry.SuperGrassmannian

/-!
### Section 1 — Statistical Invariance Lineage (Rao 1945 / Chentsov 1972 $\longleftrightarrow$ KMS Softmax Interior)
-/

/-- Canonical interior probability distribution on a finite nonempty token type `α` induced by the
Gibbs/Boltzmann softmax weights of `AttentionKMSState`. -/
noncomputable def softmaxProbInterior
    {α : Type*} [Fintype α] [Nonempty α] (logits : α → ℝ) (β : ℝ) :
    ChentsovMetricInvariance.ProbInterior α where
  p := AttentionKMSState.softmaxWeight logits β
  pos := AttentionKMSState.softmaxWeight_pos logits β
  sum_one := AttentionKMSState.softmaxWeight_sum_one logits β

/-- Evaluating `softmaxProbInterior` at token `i` recovers `AttentionKMSState.softmaxWeight`. -/
@[simp]
theorem softmaxProbInterior_p_eq
    {α : Type*} [Fintype α] [Nonempty α] (logits : α → ℝ) (β : ℝ) (i : α) :
    (softmaxProbInterior logits β).p i = AttentionKMSState.softmaxWeight logits β i :=
  rfl

/-- **Chentsov–KMS Bridge — Congruent Partition Invariance of the Softmax Fisher Metric**:
Pushing the KMS softmax interior distribution `softmaxProbInterior logits β` forward along any
sufficient-statistic partition embedding `E : CongruentPartitionEmbedding α γ` preserves the finite
Fisher information metric and equals the explicit Boltzmann-weighted tangent sum. -/
theorem chentsov_softmax_partition_embedding_fisher_invariance
    {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq α] [Nonempty α]
    (E : ChentsovMetricInvariance.CongruentPartitionEmbedding α γ)
    (logits : α → ℝ) (β : ℝ) (u v : α → ℝ) :
    ChentsovMetricInvariance.fisherMetric
        (ChentsovMetricInvariance.congruentPushforwardInterior
          (ChentsovMetricInvariance.partitionEmbeddingToKernel E)
          (softmaxProbInterior logits β)
          (ChentsovMetricInvariance.partitionEmbedding_weight_pos E))
        (ChentsovMetricInvariance.pushforwardTangentVec
          (ChentsovMetricInvariance.partitionEmbeddingToKernel E).kernel u)
        (ChentsovMetricInvariance.pushforwardTangentVec
          (ChentsovMetricInvariance.partitionEmbeddingToKernel E).kernel v) =
      ∑ i : α, (u i * v i) / AttentionKMSState.softmaxWeight logits β i := by
  rw [ChentsovMetricInvariance.chentsov_partition_embedding_fisher_invariance
    E (softmaxProbInterior logits β) u v]
  rfl

/-- **Chentsov–KMS Bridge — Sequentially Continuous Invariant Metric Evaluation on Softmax States**:
For any sequentially continuous `InvariantMetricFamily F`, there exists a universal scale `c : ℝ`
such that on every finite nonempty token space `α` and every KMS softmax distribution
`softmaxProbInterior logits β`, `F.g` evaluates on tangent vectors `u, v` to `c` times the
Boltzmann-weighted Fisher sum. -/
theorem chentsov_seqContinuous_at_softmax_interior
    (F : ChentsovUniqueness.InvariantMetricFamily)
    (hF : ChentsovUniquenessContinuous.SeqContinuous F) :
    ∃ c : ℝ, ∀ (α : Type) [Fintype α] [DecidableEq α] [Nonempty α]
      (logits : α → ℝ) (β : ℝ) (u v : α → ℝ),
      ∑ i, u i = 0 → ∑ i, v i = 0 →
        F.g α (softmaxProbInterior logits β) u v =
          c * ∑ i : α, (u i * v i) / AttentionKMSState.softmaxWeight logits β i := by
  obtain ⟨c, hc⟩ := ChentsovUniquenessContinuous.chentsov_uniqueness_of_seqContinuous F hF
  refine ⟨c, fun α _ _ _ logits β u v hu hv => ?_⟩
  exact hc α (softmaxProbInterior logits β) u v hu hv

/-!
### Section 2 — Information-Geometric Flow & Submersion Pruning Lineage (O'Neill 1966 / Amari 1985–1998 $\longleftrightarrow$ Libermann Para-Kähler Split)
-/

/-- Canonical `RiemannianSubmersion.SubmersionSplit V` induced by the spectral projectors
`SuperGrassmannian.paraProjectorPlus K` and `paraProjectorMinus K` of an involutive para-complex
operator `K`. -/
noncomputable def paraKahlerSubmersionSplit
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v) :
    RiemannianSubmersion.SubmersionSplit V where
  projH := SuperGrassmannian.paraProjectorPlus K
  projV := SuperGrassmannian.paraProjectorMinus K
  sum_id := SuperGrassmannian.paraProjectors_sum_id K
  idemH := SuperGrassmannian.paraProjectorPlus_idempotent K hK
  idemV := SuperGrassmannian.paraProjectorMinus_idempotent K hK
  orthoHV := SuperGrassmannian.paraProjectorPlus_mul_minus K hK
  orthoVH := SuperGrassmannian.paraProjectorMinus_mul_plus K hK

/-- **Amari–Libermann Bridge — Vanishing Vertical Projection on the Primal Sheet**:
Every vector `v ∈ SuperGrassmannian.primalSheet K` has zero vertical component under
`paraKahlerSubmersionSplit K hK`. -/
theorem paraKahler_projV_eq_zero_of_mem_primalSheet
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v) {v : V}
    (hv : v ∈ SuperGrassmannian.primalSheet K) :
    (paraKahlerSubmersionSplit K hK).projV v = 0 := by
  have h_fix : (paraKahlerSubmersionSplit K hK).projH v = v :=
    (SuperGrassmannian.mem_primalSheet_iff K hK v).mp hv
  exact RiemannianSubmersion.vertical_zero_of_horizontal_fixed
    (paraKahlerSubmersionSplit K hK) v h_fix

/-- **Amari–Libermann Bridge — Complementarity of Primal and Covector Vacuum Eigen-Sheets**:
For any para-complex involution `K`, `SuperGrassmannian.primalSheet K` and
`SuperGrassmannian.covectorVacuumSheet K` are complementary submodules (`IsCompl`). -/
theorem isCompl_primalSheet_covectorVacuumSheet
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v) :
    IsCompl (SuperGrassmannian.primalSheet K) (SuperGrassmannian.covectorVacuumSheet K) := by
  rw [SuperGrassmannian.primalSheet_eq_range_projectorPlus K hK,
    SuperGrassmannian.covectorVacuumSheet_eq_range_projectorMinus K hK]
  exact SubmersionSplitFinrank.isCompl_range_projH_range_projV (paraKahlerSubmersionSplit K hK)

/-- **Amari–Libermann Bridge — Exact Finrank Decomposition across Para-Kähler Eigen-Sheets**:
On any finite-dimensional real vector space `V`, `finrank V` equals the sum of the dimensions of
`SuperGrassmannian.primalSheet K` and `SuperGrassmannian.covectorVacuumSheet K`. -/
theorem finrank_eq_primalSheet_add_covectorVacuumSheet
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v) :
    Module.finrank ℝ V =
      Module.finrank ℝ (SuperGrassmannian.primalSheet K) +
        Module.finrank ℝ (SuperGrassmannian.covectorVacuumSheet K) := by
  rw [SuperGrassmannian.primalSheet_eq_range_projectorPlus K hK,
    SuperGrassmannian.covectorVacuumSheet_eq_range_projectorMinus K hK]
  exact SubmersionSplitFinrank.finrank_split (paraKahlerSubmersionSplit K hK)

/-- **Amari–Libermann Bridge — Strict Cubic FLOP Reduction on the Primal Eigen-Sheet**:
Whenever both `SuperGrassmannian.primalSheet K` and `SuperGrassmannian.covectorVacuumSheet K` are
nontrivial (`≠ ⊥`), restricting cubic operator complexity to `primalSheet K` strictly reduces the
cubic cost below `cubicCostModel (finrank ℝ V)`. -/
theorem paraKahler_primalSheet_cubic_cost_lt
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v)
    (hH : SuperGrassmannian.primalSheet K ≠ ⊥)
    (hV : SuperGrassmannian.covectorVacuumSheet K ≠ ⊥) :
    LeanJuliaVerifiedInterop.cubicCostModel (Module.finrank ℝ (SuperGrassmannian.primalSheet K)) <
      LeanJuliaVerifiedInterop.cubicCostModel (Module.finrank ℝ V) := by
  rw [SuperGrassmannian.primalSheet_eq_range_projectorPlus K hK] at hH ⊢
  rw [SuperGrassmannian.covectorVacuumSheet_eq_range_projectorMinus K hK] at hV
  exact SubmersionSplitFinrank.cost_horizontal_lt (paraKahlerSubmersionSplit K hK) hH hV

/-!
### Section 3 — Modular Operator Theory & Attention Sink Lineage (KMS 1957–1959 / Tomita–Takesaki 1970 $\longleftrightarrow$ Simplex Interior & Cuntz Colimit)
-/

/-- **KMS–Chentsov Bridge — Attention GNS State as Expectation over `softmaxProbInterior`**:
The GNS state functional `AttentionKMSState.attentionState logits β A` equals the diagonal
expectation weighted by `(softmaxProbInterior logits β).p`. -/
theorem attentionState_eq_softmaxProbInterior_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) (A : Matrix ι ι ℝ) :
    AttentionKMSState.attentionState logits β A =
      ∑ i : ι, (softmaxProbInterior logits β).p i * A i i := by
  rw [AttentionKMSState.attentionState_eq_sum]
  rfl

/-- **KMS–Colimit–Chentsov Bridge — Cross-Stage Modular Flow Readout via `softmaxProbInterior`**:
For any `k ≤ n` in the Cuntz matrix tower, evolving a complexified stage-`k` observable `A` under
the real-time modular automorphism group `modularFlow logits β t`, pushing it to stage `n` via
`rawMap h`, and reading it out under `selectedStageColimitFunctional k` recovers the exact finite
`softmaxProbInterior` diagonal expectation. -/
theorem kms_colimit_modularFlow_readout_eq_softmaxProbInterior_sum
    {k n : ℕ} (h : k ≤ n) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    MatrixStageSelectedFunctional.selectedStageColimitFunctional k
        (AttentionStageColimitState.attentionStageDensity k logits β)
        (CuntzMatrixAlgebraicStarColimit.stageInjection n
          (CuntzMatrixAlgebraicStarColimit.rawMap h
            (ColimitAttentionTomitaFlow.modularFlow logits β t
              (AttentionStageColimitState.complexifyRealMatrix A)))) =
      ((∑ i : Fin (2 ^ k), (softmaxProbInterior logits β).p i * A i i : ℝ) : ℂ) := by
  rw [ColimitAttentionTomitaFlow.attentionColimitFunctional_rawMap_modularFlow_invariant h logits β t]
  rw [AttentionStageColimitState.attentionColimitFunctional_real_seed_readout]
  rw [attentionState_eq_softmaxProbInterior_sum]

/-- **Attention Sink Bridge — Anchor-Column Energy Bound on the Weighted Gram Diagonal Sum**:
Under any pruned weight distribution `pw`, the anchor weight times the squared Euclidean norm of
the anchor column of `A` bounds the weighted Gram diagonal sum `∑ i, w_i (Aᵀ A)_{i,i}` from below. -/
theorem prunedState_anchor_bound_le_diagonal_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pw : AttentionKMSState.PrunedWeights ι) (anchor : ι) (A : Matrix ι ι ℝ) :
    pw.weights anchor * (∑ j, (A j anchor) ^ 2) ≤
      ∑ i, pw.weights i * (A.transpose * A) i i := by
  rw [← ColimitAttentionTomitaFlow.prunedState_eq_sum pw (A.transpose * A)]
  exact ColimitAttentionTomitaFlow.prunedState_ge_anchor_column_normSq pw anchor A

/-- Entrywise `(0, 0)` witness certifying non-commutativity of the elementary two-token transition
matrices `matE01` and `matE10`. -/
theorem matE01_mul_matE10_diag_zero_ne_swap :
    (ColimitAttentionTomitaFlow.matE01 * ColimitAttentionTomitaFlow.matE10) 0 0 ≠
      (ColimitAttentionTomitaFlow.matE10 * ColimitAttentionTomitaFlow.matE01) 0 0 := by
  dsimp [ColimitAttentionTomitaFlow.matE01, ColimitAttentionTomitaFlow.matE10, Matrix.mul_apply]
  rw [Fin.sum_univ_two]
  norm_num

/-- Closed non-commutativity theorem for the two-token matrix carrier `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem matE01_mul_matE10_ne_comm :
    ColimitAttentionTomitaFlow.matE01 * ColimitAttentionTomitaFlow.matE10 ≠
      ColimitAttentionTomitaFlow.matE10 * ColimitAttentionTomitaFlow.matE01 := by
  intro h
  exact matE01_mul_matE10_diag_zero_ne_swap (congr_fun (congr_fun h 0) 0)

/-!
### Section 4 — $CPT$ & Spacetime Symmetries Lineage (Bisognano–Wichmann 1975 / Borchers 1992 $\longleftrightarrow$ Spectral Projectors $P^\pm$)
-/

/-- Evaluation of `SuperGrassmannian.paraProjectorPlus` for the doubled para-complex involution
`ModularCPT.K_op` projects `z = (z.1, z.2)` onto `(z.1, 0)`. -/
theorem paraProjectorPlus_K_op_apply
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E) :
    SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E)) z = (z.1, 0) := by
  rw [SuperGrassmannian.paraProjectorPlus_apply]
  ext
  · dsimp
    rw [← two_smul ℝ z.1, smul_smul]
    norm_num
  · dsimp
    rw [add_neg_cancel, smul_zero]

/-- Evaluation of `SuperGrassmannian.paraProjectorMinus` for the doubled para-complex involution
`ModularCPT.K_op` projects `z = (z.1, z.2)` onto `(0, z.2)`. -/
theorem paraProjectorMinus_K_op_apply
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E) :
    SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E)) z = (0, z.2) := by
  rw [SuperGrassmannian.paraProjectorMinus_apply]
  ext
  · dsimp
    rw [sub_self, smul_zero]
  · dsimp
    rw [sub_neg_eq_add, ← two_smul ℝ z.2, smul_smul]
    norm_num

/-- **Bisognano–Wichmann–Libermann Bridge — $CPT$ Intertwines $P^+$ with $P^-$**:
Applying `ModularCPT.CPT_op` after the positive spectral projector `paraProjectorPlus K_op` equals
applying the negative spectral projector `paraProjectorMinus K_op` after `CPT_op`. -/
theorem cpt_intertwines_paraProjectorPlus_paraProjectorMinus
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E) :
    ModularCPT.CPT_op (SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E)) z) =
      SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E)) (ModularCPT.CPT_op z) := by
  rw [paraProjectorPlus_K_op_apply, paraProjectorMinus_K_op_apply, ModularCPT.CPT_apply]
  ext <;> simp

/-- **Bisognano–Wichmann–Libermann Bridge — $CPT$ Intertwines $P^-$ with $P^+$**:
Applying `ModularCPT.CPT_op` after the negative spectral projector `paraProjectorMinus K_op` equals
applying the positive spectral projector `paraProjectorPlus K_op` after `CPT_op`. -/
theorem cpt_intertwines_paraProjectorMinus_paraProjectorPlus
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E) :
    ModularCPT.CPT_op (SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E)) z) =
      SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E)) (ModularCPT.CPT_op z) := by
  rw [paraProjectorMinus_K_op_apply, paraProjectorPlus_K_op_apply, ModularCPT.CPT_apply]
  ext <;> simp

/-- **Bisognano–Wichmann Lineage — Modular $CPT$ Maps the Primal Subspace into the Vacuum Subspace**:
For any state $z \in \mathrm{primalSubspace}$ ($E \times \{0\}$), its modular $CPT$ image
`CPT_op z = (-z.2, z.1)` lies in `vacuumSubspace` ($\{0\} \times E$). -/
theorem cpt_maps_primalSubspace_to_vacuumSubspace
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E)
    (hz : z ∈ ModularCPT.primalSubspace) :
    ModularCPT.CPT_op z ∈ ModularCPT.vacuumSubspace := by
  dsimp [ModularCPT.primalSubspace] at hz
  rw [LinearMap.mem_ker] at hz
  change z.2 = 0 at hz
  dsimp [ModularCPT.vacuumSubspace]
  rw [LinearMap.mem_ker, ModularCPT.CPT_apply]
  change -z.2 = 0
  rw [hz, neg_zero]

/-!
### Section 5 — Neutral & Para-Kähler Geometry Lineage (Libermann 1954 / Cruceanu–Fortuny–Gadea 1996 $\longleftrightarrow$ Zorn Split-Octonions)
-/

/-- **Libermann Lineage — Doubled Para-Kähler Primal Sheet Bridge**:
On the doubled carrier $E \times E$, the $+1$ spectral eigen-sheet
`SuperGrassmannian.primalSheet ModularCPT.K_op` coincides identically with the coordinate kernel
submodule `ModularCPT.primalSubspace` ($E \times \{0\}$). -/
theorem libermann_lineage_doubled_paraK_primalSheet
    {E : Type*} [AddCommGroup E] [Module ℝ E] :
    SuperGrassmannian.primalSheet (ModularCPT.K_op (E := E)) =
      ModularCPT.primalSubspace (E := E) := by
  ext z
  rw [SuperGrassmannian.mem_primalSheet_iff (ModularCPT.K_op (E := E)) ModularCPT.K_involutive z,
    paraProjectorPlus_K_op_apply]
  dsimp [ModularCPT.primalSubspace]
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact (Prod.ext_iff.mp h).2.symm
  · intro h
    exact Prod.ext rfl h.symm

/-- **Libermann Lineage — Doubled Para-Kähler Covector Vacuum Sheet Bridge**:
On the doubled carrier $E \times E$, the $-1$ spectral eigen-sheet
`SuperGrassmannian.covectorVacuumSheet ModularCPT.K_op` coincides identically with the coordinate
kernel submodule `ModularCPT.vacuumSubspace` ($\{0\} \times E$). -/
theorem libermann_lineage_doubled_paraK_vacuumSheet
    {E : Type*} [AddCommGroup E] [Module ℝ E] :
    SuperGrassmannian.covectorVacuumSheet (ModularCPT.K_op (E := E)) =
      ModularCPT.vacuumSubspace (E := E) := by
  ext z
  rw [SuperGrassmannian.mem_covectorVacuumSheet_iff (ModularCPT.K_op (E := E))
    ModularCPT.K_involutive z, paraProjectorMinus_K_op_apply]
  dsimp [ModularCPT.vacuumSubspace]
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact (Prod.ext_iff.mp h).1.symm
  · intro h
    exact Prod.ext h.symm rfl

/-- Canonical identification of the 6D Zorn para-Kähler phase space
`SplitOctonionParaKahlerNullCone.ParaKahlerVec ℝ` with `ModularCPT.DoubledCarrier (Fin 3 → ℝ)`. -/
def paraKahlerVecToDoubled
    (z : SplitOctonionParaKahlerNullCone.ParaKahlerVec ℝ) :
    ModularCPT.DoubledCarrier (Fin 3 → ℝ) :=
  (z.u, z.v)

/-- **Libermann–Zorn Bridge — Equivariance of `paraKahlerVecToDoubled` under the Para-Complex Involution $K$**:
Mapping a 6D Zorn phase-space vector `z` to `DoubledCarrier (Fin 3 → ℝ)` intertwines
`SplitOctonionParaKahlerNullCone.paraComplexK` with `ModularCPT.K_op`. -/
theorem paraKahlerVecToDoubled_paraComplexK
    (z : SplitOctonionParaKahlerNullCone.ParaKahlerVec ℝ) :
    paraKahlerVecToDoubled (SplitOctonionParaKahlerNullCone.paraComplexK z) =
      ModularCPT.K_op (paraKahlerVecToDoubled z) := by
  ext i <;> rfl

/-- **Libermann–Zorn Bridge — Zorn Primal Sheet Lands in `SuperGrassmannian.primalSheet K_op`**:
Every embedded 3D primal vector `SplitOctonionParaKahlerNullCone.primalSheet u` maps under
`paraKahlerVecToDoubled` into `SuperGrassmannian.primalSheet ModularCPT.K_op`. -/
theorem paraKahlerVecToDoubled_primalSheet_mem_primalSheet
    (u : Fin 3 → ℝ) :
    paraKahlerVecToDoubled (SplitOctonionParaKahlerNullCone.primalSheet u) ∈
      SuperGrassmannian.primalSheet (ModularCPT.K_op (E := Fin 3 → ℝ)) := by
  rw [libermann_lineage_doubled_paraK_primalSheet]
  dsimp [ModularCPT.primalSubspace, paraKahlerVecToDoubled,
    SplitOctonionParaKahlerNullCone.primalSheet]
  rw [LinearMap.mem_ker]
  rfl

/-- **Libermann–Zorn Bridge — Zorn Dual Sheet Lands in `SuperGrassmannian.covectorVacuumSheet K_op`**:
Every embedded 3D dual vector `SplitOctonionParaKahlerNullCone.dualSheet v` maps under
`paraKahlerVecToDoubled` into `SuperGrassmannian.covectorVacuumSheet ModularCPT.K_op`. -/
theorem paraKahlerVecToDoubled_dualSheet_mem_covectorVacuumSheet
    (v : Fin 3 → ℝ) :
    paraKahlerVecToDoubled (SplitOctonionParaKahlerNullCone.dualSheet v) ∈
      SuperGrassmannian.covectorVacuumSheet (ModularCPT.K_op (E := Fin 3 → ℝ)) := by
  rw [libermann_lineage_doubled_paraK_vacuumSheet]
  dsimp [ModularCPT.vacuumSubspace, paraKahlerVecToDoubled,
    SplitOctonionParaKahlerNullCone.dualSheet]
  rw [LinearMap.mem_ker]
  rfl

/-!
### Section 6 — Supergeometry, Orientifolds & Categorical Colimit Lineage (Berezin 1966 / Manin 1988 / Polchinski 1996)
-/

/-- **Manin–Polchinski–Libermann Bridge — Möbius Twist Intertwines $P^+$ with $P^-$**:
Applying the unoriented Möbius twist `ModularCPT.moebiusTwist` after `paraProjectorPlus K_op`
equals applying `paraProjectorMinus K_op` after `moebiusTwist`. -/
theorem moebiusTwist_intertwines_paraProjectorPlus_paraProjectorMinus
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E) :
    ModularCPT.moebiusTwist
        (SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E)) z) =
      SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E))
        (ModularCPT.moebiusTwist z) := by
  rw [paraProjectorPlus_K_op_apply, paraProjectorMinus_K_op_apply,
    ModularCPT.moebiusTwist_apply]
  ext <;> simp [ModularCPT.moebiusTwist_apply]

/-- **Manin–Polchinski–Libermann Bridge — Möbius Twist Intertwines $P^-$ with $P^+$**:
Applying the unoriented Möbius twist `ModularCPT.moebiusTwist` after `paraProjectorMinus K_op`
equals applying `paraProjectorPlus K_op` after `moebiusTwist`. -/
theorem moebiusTwist_intertwines_paraProjectorMinus_paraProjectorPlus
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E) :
    ModularCPT.moebiusTwist
        (SuperGrassmannian.paraProjectorMinus (ModularCPT.K_op (E := E)) z) =
      SuperGrassmannian.paraProjectorPlus (ModularCPT.K_op (E := E))
        (ModularCPT.moebiusTwist z) := by
  rw [paraProjectorMinus_K_op_apply, paraProjectorPlus_K_op_apply,
    ModularCPT.moebiusTwist_apply]
  ext <;> simp [ModularCPT.moebiusTwist_apply]

/-- **Manin–Polchinski Lineage — Krein Metric Invariance under the Unoriented Möbius Twist**:
Unlike `CPT_op` (which negates `kreinForm`), the orientation-reversing Möbius twist
`moebiusTwist = P_op ∘ₗ C_op` preserves the split Krein metric identically. -/
theorem kreinForm_moebiusTwist_invariant
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (z₁ z₂ : ModularCPT.DoubledCarrier E) :
    ModularCPT.kreinForm pairing
        (ModularCPT.moebiusTwist z₁) (ModularCPT.moebiusTwist z₂) =
      ModularCPT.kreinForm pairing z₁ z₂ := by
  dsimp [ModularCPT.kreinForm]
  rw [ModularCPT.moebiusTwist_apply, ModularCPT.moebiusTwist_apply]
  dsimp
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact add_comm (pairing z₁.2 z₂.1) (pairing z₁.1 z₂.2)

/-- **Manin–Polchinski Lineage — Symplectic Form Anti-Invariance under the Unoriented Möbius Twist**:
Unlike `CPT_op` (which preserves `symplecticForm`), the unoriented Möbius twist negates the
canonical symplectic 2-form on `DoubledCarrier E`. -/
theorem symplecticForm_moebiusTwist_anti_invariant
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (z₁ z₂ : ModularCPT.DoubledCarrier E) :
    ModularCPT.symplecticForm pairing
        (ModularCPT.moebiusTwist z₁) (ModularCPT.moebiusTwist z₂) =
      - ModularCPT.symplecticForm pairing z₁ z₂ := by
  dsimp [ModularCPT.symplecticForm]
  rw [ModularCPT.moebiusTwist_apply, ModularCPT.moebiusTwist_apply]
  dsimp
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact (neg_sub (pairing z₁.1 z₂.2) (pairing z₁.2 z₂.1)).symm

/-- **Manin–Polchinski Lineage — Möbius Twist Maps the Primal Subspace into the Vacuum Subspace**:
For any state $z \in \mathrm{primalSubspace}$ ($E \times \{0\}$), its Möbius-twisted image
`moebiusTwist z = (-z.2, -z.1)` lies in `vacuumSubspace` ($\{0\} \times E$). -/
theorem manin_polchinski_lineage_moebius_maps_primal_to_vacuum
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E)
    (hz : z ∈ ModularCPT.primalSubspace) :
    ModularCPT.moebiusTwist z ∈ ModularCPT.vacuumSubspace := by
  dsimp [ModularCPT.primalSubspace] at hz
  rw [LinearMap.mem_ker] at hz
  change z.2 = 0 at hz
  dsimp [ModularCPT.vacuumSubspace]
  rw [LinearMap.mem_ker, ModularCPT.moebiusTwist_apply]
  change -z.2 = 0
  rw [hz, neg_zero]

/-- **Manin–Polchinski Lineage — Möbius Twist Maps the Vacuum Subspace into the Primal Subspace**:
For any state $z \in \mathrm{vacuumSubspace}$ ($\{0\} \times E$), its Möbius-twisted image
`moebiusTwist z = (-z.2, -z.1)` lies in `primalSubspace` ($E \times \{0\}$). -/
theorem manin_polchinski_lineage_moebius_maps_vacuum_to_primal
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E)
    (hz : z ∈ ModularCPT.vacuumSubspace) :
    ModularCPT.moebiusTwist z ∈ ModularCPT.primalSubspace := by
  dsimp [ModularCPT.vacuumSubspace] at hz
  rw [LinearMap.mem_ker] at hz
  change z.1 = 0 at hz
  dsimp [ModularCPT.primalSubspace]
  rw [LinearMap.mem_ker, ModularCPT.moebiusTwist_apply]
  change -z.1 = 0
  rw [hz, neg_zero]

/-- **Manin–Polchinski–Libermann Bridge — Möbius Twist Maps `primalSheet K_op` into `covectorVacuumSheet K_op`**:
Every $+1$ spectral eigenstate in `SuperGrassmannian.primalSheet ModularCPT.K_op` is mapped by
`ModularCPT.moebiusTwist` into the $-1$ spectral eigen-sheet
`SuperGrassmannian.covectorVacuumSheet ModularCPT.K_op`. -/
theorem manin_polchinski_lineage_moebius_maps_primalSheet_to_covectorVacuumSheet
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E)
    (hz : z ∈ SuperGrassmannian.primalSheet (ModularCPT.K_op (E := E))) :
    ModularCPT.moebiusTwist z ∈
      SuperGrassmannian.covectorVacuumSheet (ModularCPT.K_op (E := E)) := by
  rw [libermann_lineage_doubled_paraK_primalSheet] at hz
  rw [libermann_lineage_doubled_paraK_vacuumSheet]
  exact manin_polchinski_lineage_moebius_maps_primal_to_vacuum z hz

/-- **Manin–Polchinski–Libermann Bridge — Möbius Twist Maps `covectorVacuumSheet K_op` into `primalSheet K_op`**:
Every $-1$ spectral eigenstate in `SuperGrassmannian.covectorVacuumSheet ModularCPT.K_op` is mapped
by `ModularCPT.moebiusTwist` into the $+1$ spectral eigen-sheet
`SuperGrassmannian.primalSheet ModularCPT.K_op`. -/
theorem manin_polchinski_lineage_moebius_maps_covectorVacuumSheet_to_primalSheet
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : ModularCPT.DoubledCarrier E)
    (hz : z ∈ SuperGrassmannian.covectorVacuumSheet (ModularCPT.K_op (E := E))) :
    ModularCPT.moebiusTwist z ∈
      SuperGrassmannian.primalSheet (ModularCPT.K_op (E := E)) := by
  rw [libermann_lineage_doubled_paraK_vacuumSheet] at hz
  rw [libermann_lineage_doubled_paraK_primalSheet]
  exact manin_polchinski_lineage_moebius_maps_vacuum_to_primal z hz

/-- **Categorical Colimit Lineage — Multi-Step `TensorTowerColimit.iota_seq` Horizontal-Vertical Decomposition**:
When a projector family `PF` intertwines a `HolographicTower`, pushing the stage-`n` horizontal
and vertical submersion components of `x : T n` across `_root_.iota_seq T tower.iota n m`
reconstructs `_root_.iota_seq T tower.iota n m x` at stage `n + m`. -/
theorem colimit_lineage_iota_seq_eq_add_projH_projV
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module ℝ (T n)]
    (tower : HolographicColimitContinuum.HolographicTower (R := ℝ) T)
    (PF : HolographicColimitContinuum.ProjectorFamily (R := ℝ) T)
    (h_inter : HolographicColimitContinuum.IntertwinesProjector tower PF)
    (n m : ℕ) (x : T n) :
    _root_.iota_seq T tower.iota n m
        ((GrandEpistemicGeometricSynthesis.colimitStageSubmersionSplit PF n).projH x) +
      _root_.iota_seq T tower.iota n m
        ((GrandEpistemicGeometricSynthesis.colimitStageSubmersionSplit PF n).projV x) =
      _root_.iota_seq T tower.iota n m x := by
  rw [← GrandEpistemicGeometricSynthesis.colimitStageSubmersionSplit_projH_comm_tensorTowerColimit
    tower PF h_inter n m x]
  rw [← GrandEpistemicGeometricSynthesis.colimitStageSubmersionSplit_projV_comm_tensorTowerColimit
    tower PF h_inter n m x]
  exact (GrandEpistemicGeometricSynthesis.colimitStageSubmersionSplit PF (n + m)).sum_id
    (_root_.iota_seq T tower.iota n m x)

/-- **Categorical Colimit Lineage — Vanishing Vertical Drift of Pushed Horizontal States across `TensorTowerColimit.iota_seq`**:
When `PF` intertwines `tower`, pushing a horizontally projected stage-`n` state `projH x` across
`_root_.iota_seq T tower.iota n m` yields identically zero vertical component at stage `n + m`. -/
theorem colimit_lineage_projV_iota_seq_projH_eq_zero
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module ℝ (T n)]
    (tower : HolographicColimitContinuum.HolographicTower (R := ℝ) T)
    (PF : HolographicColimitContinuum.ProjectorFamily (R := ℝ) T)
    (h_inter : HolographicColimitContinuum.IntertwinesProjector tower PF)
    (n m : ℕ) (x : T n) :
    (GrandEpistemicGeometricSynthesis.colimitStageSubmersionSplit PF (n + m)).projV
        (_root_.iota_seq T tower.iota n m
          ((GrandEpistemicGeometricSynthesis.colimitStageSubmersionSplit PF n).projH x)) = 0 := by
  rw [← GrandEpistemicGeometricSynthesis.colimitStageSubmersionSplit_projH_comm_tensorTowerColimit
    tower PF h_inter n m x]
  exact (GrandEpistemicGeometricSynthesis.colimitStageSubmersionSplit PF (n + m)).orthoVH
    (_root_.iota_seq T tower.iota n m x)

end InfoGeometry.Synthesis.ThreeTraditionLineageConvergence
