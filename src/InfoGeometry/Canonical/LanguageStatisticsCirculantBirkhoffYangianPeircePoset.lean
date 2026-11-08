/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel
import InfoGeometry.Canonical.LanguageStatisticsTranslationSymmetry
import InfoGeometry.LLM.ZModFourierBridge
import InfoGeometry.LLM.CyclicGramGeometry
import InfoGeometry.Canonical.AttentionGlauberCopulaBridge
import InfoGeometry.Canonical.SmithBlockCirculantMoorePenrose
import InfoGeometry.Canonical.ChaoRetrocirculant
import InfoGeometry.Canonical.SmithRetrocirculantMoorePenrose
import InfoGeometry.Algebra.OperatorCyclotomicParafermions
import InfoGeometry.Algebra.CyclicShiftNilpotencySeparation
import InfoGeometry.Canonical.Z4CirculantMassLadder
import InfoGeometry.Canonical.FourierCharacterRepresentationBridge
import InfoGeometry.Parafermion.ParafermionCondensationGaloisCharacterPoset
import InfoGeometry.Clifford.Cl55RoPEAttentionPairing
import InfoGeometry.Clifford.Cl55AttentionRelativePositionBridge
import InfoGeometry.Routing.CliffordRoPETorus
import InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics
import InfoGeometry.Canonical.Attention
import InfoGeometry.Routing.AttentionPolytope
import InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge
import InfoGeometry.LinearAlgebra.FiniteGramDeformationEntropy
import InfoGeometry.Routing.BirkhoffVonNeumann
import InfoGeometry.Canonical.GibsonBasicDoublyStochastic
import InfoGeometry.Cantor.PermutationOperator
import InfoGeometry.Clifford.ClNNPermutationSymmetry
import InfoGeometry.Cantor.CliffordMarkovOperators
import InfoGeometry.Clifford.Cl55PeirceMoERouting
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Algebra.YangianCoproductTensorAction
import InfoGeometry.OperatorAlgebra.SplitOctonionPeirceYangBaxterBridge
import InfoGeometry.Physics.YangBaxterQSwap
import InfoGeometry.Topology.AmplituhedronBCFW
import InfoGeometry.Canonical.CantorPlabicTwistorBridge
import InfoGeometry.Canonical.DoubledPlabicTwistedAmplituhedronFoam
import InfoGeometry.Core.TensorPeirceDecomposition
import InfoGeometry.Clifford.Cl11TensorStageFactorization
import InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset
import InfoGeometry.WignerHurwitzAdamsKTheory.WignerHurwitzAdamsKTheoryPoset
import InfoGeometry.PinMinus88Triality.PinMinus88TrialityPoset
import InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevLocalGapOmegaSpectrumPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential

/-!
# Language Statistics and Related Finite Algebra Catalog

## i. Overview

This canonical module contains finite algebraic results motivated in part by Karkada,
Korchinski, Nava, Wyart, and Bahri (`arXiv:2602.15029`, *"Symmetry in language statistics shapes
the geometry of model representations"*), alongside related results from existing repository
owners. The declarations below form a catalog with selected explicitly proved bridges; their
co-location and stage numbering do not assert that every listed domain is derived from the paper
or that the stages form a mathematically induced causal dependency relation:

$$\mathbf{T} \;\; \Big(\text{Periodic Circulant Shift Centralizer } [S, K] = 0, \;\; K = \sum_{r=0}^{N-1} c_r S^r, \;\; \mu_k = \mu_{N-k}\Big)
  \quad \overset{\Pi_{\mathrm{diag}}(X) = P X P + (1 - P) X (1 - P)}{\underset{\longleftrightarrow}{\relbar\joinrel\longrightarrow}} \quad
  \mathbf{S} \;\; \Big(\text{Open-Boundary Toeplitz Cut } [P, X] \neq 0, \;\; X - \Pi_{\mathrm{diag}}(X) = \mathrm{oddGrade}(P, X)\Big)$$

* **Node `𝔏𝔖₁` (`shift_centralizer_subalgebra_and_circulant_indirect_cooccurrence`):**
  Proves over any associative ring `[Ring B]` that the shift centralizer
  $\mathcal{Z}(S) = \{K \in B \mid S K = K S\}$ is a subalgebra via the non-commutative Leibniz law
  `comm S (K1 * K2) = comm S K1 * K2 + K1 * comm S K2`, so second-order indirect co-occurrence
  paths $K^2$ remain shift-invariant (`S * (K * K) = (K * K) * S`) whenever $S K = K S$. Welds this
  to `TranslationSymmetryEmbeddings.translationInvariant_iff_differenceKernel`,
  `LanguageStatisticsTranslationSymmetry.relativeKernelMatrix_mul_translation_invariant`,
  `SmithBlockCirculantMoorePenrose.blockCirculant3_commutes_cyclicShift`, the polynomial expansion
  `blockCirculant3 A0 A1 A2 = A0 • 1 + A1 • cyclicShift3 + A2 • cyclicShift3 ^ 2` with
  `cyclicShift3 ^ 3 = 1`, algebraic bistochasticity of `blockCirculant3` when `A0 + A1 + A2 = 1`,
  and the open-interval Toeplitz boundary commutator defect.
* **Node `𝔏𝔖₂` (`fourier_character_relative_kernel_and_cosine_sine_circle_degeneracy`):**
  Welds `TranslationSymmetryEmbeddings.character_is_convolution_eigenmode` (multiplicative
  characters are eigenvectors of every displacement convolution operator with DFT eigenvalues),
  `FourierCharacterEncoding.fourierCharacterKernel_add_left` ($\chi((a+t)-(a+s)) = \chi(t-s)$),
  and `FourierCharacter.toPositionRepresentation_relative_kernel` to the conjugate harmonic
  degeneracy $\mu_k = \mu_{N-k}$ of symmetric circulant coefficients ($c_r = c_{N-r}$),
  `Z4CirculantMassLadder.charMat4_det`, `squared_modulus`, `opposite_phase_separation`, and
  `ParafermionCondensationGaloisCharacterPoset.cyclic_character_sum_ring_identities`.
* **Node `𝔏𝔖₃` (`rope_relative_position_attention_and_clifford_spinor_trace`):**
  Welds `TranslationSymmetryEmbeddings.translationInvariant_softmaxKernel`,
  `AttentionGlauberCopulaBridge.log_attentionDependenceRatio` (Pointwise Mutual Information) and
  `attentionMutualInformation_eq_expectedLogDependenceRatio`,
  `Cl55RoPEAttentionPairing.InvariantRotorPairing.attentionScore_eq_relative`,
  `Cl55AttentionRelativePositionBridge.rotatedAttention_relative_position`
  ($\mathrm{Tr}(R(m\theta) q k R(-n\theta)) = \mathrm{Tr}(R((m-n)\theta) q k)$), and
  `AttentionPolytope.reconstruct`.
* **Node `𝔏𝔖₄` (`stochastic_grammar_amplitude_sphere_and_gram_logdet_entropy`):**
  Welds `StochasticGrammarCuntzKriegerBridge.StochasticTransitionMatrix.amplitude_row_l2_normalization`
  ($\sum_j \Psi(i, j)^2 = 1$) and `bhattacharyya_language_fidelity_eq_inner_product` to symmetric
  Gramian factorization $(W^\top W)^\top = W^\top W$ and `FiniteGramDeformationEntropy.det_gramDistortion`
  ($\det(J^\top J) = (\det J)^2$).
* **Node `𝔏𝔖₅` (`birkhoff_bistochastic_polytope_permutations_and_clifford_markov_channel`):**
  Welds `BirkhoffRouting.birkhoff_von_neumann_decomposition` ($W = \sum_{\sigma \in S_n} w_\sigma P_\sigma$),
  `BirkhoffRouting.sinkhorn_step_row_sum_one`, `GibsonBasicDoublyStochastic.basic12_is_doubly_stochastic`,
  `basic12_det`, and `doublyStochastic_mul` to `PermutationOperator.operatorUnitRep_injective` and
  `CliffordMarkovOperators.randomFockAverage_cantorMode`.
* **Node `𝔏𝔖₆` (`moe_peirce_hypercube_routing_and_sigmoid_partition`):**
  Welds `Cl55PeirceMoERouting.sigmoid_add_sigmoid_neg` ($\sigma(x) + \sigma(-x) = 1$),
  `peircePlus_idem`, `peirce_orthogonal_pm`, `peirce_sum_one`, `hypercube_expert_sum_one`
  ($P_{++} + P_{+-} + P_{-+} + P_{--} = 1$), and `hypercube_expert_orthogonal_pp_pm`.
* **Node `𝔏𝔖₇` (`yangian_qswap_braid_and_amplituhedron_bcfw_polytope_gluing`):**
  Welds `YangBaxterQSwap.yang_baxter_relation` ($C_{12}(q) C_{23}(q) C_{12}(q) = C_{23}(q) C_{12}(q) C_{23}(q)$),
  `AmplituhedronBCFW.plucker_spurious_factor`, `bcfw_spurious_pole_cancellation`,
  `spurious_residue_cancellation`, and `DoubledPlabicTwistedAmplituhedronFoam.plabic_square_move_spurious_pole_cancellation`.
* **Node `𝔏𝔖₈` (`peirce_centralizer_projection_and_recursive_tensor_homogenization` & `recursive_commuting_peirce_and_artin_wedderburn_centralizer`):**
  Welds `TensorPeirceDecomposition.toTensorTower_ofTensorTower`, `ofTensorTower_toTensorTower`,
  `tensor_peirce_exact_reconstruction`, and `fromBlocks_pi_homogenization` ($\pi_{ab}(M) = I_2 \otimes M_{ab}$)
  with `Cl11TensorStageFactorization.stageTensorFactorization_reindex_kronecker`, the Peirce
  centralizer projection laws `comm P (evenGrade P X) = 0` and `X - evenGrade P X = oddGrade P X`,
  the repeated commuting-idempotent Peirce centralizer law
  `evenGrade Q (evenGrade P X) = X ↔ (comm P X = 0 ∧ comm Q X = 0)`, the Artin–Wedderburn outer
  matrix-unit centralizer commutation `[E_{ij}, \pi_{ab}(M)] = 0`, and
  `PeirceSpine.superDerivPhi_square_zero_iff` ($\partial_\Phi^2(X) = 0 \iff V X = X V$).

## ii. Key results

- `LanguageStatisticsPeirceStage` & `causalEdge_acyclic`
- `shift_centralizer_subalgebra_and_circulant_indirect_cooccurrence` (`𝔏𝔖₁`)
- `cyclic_shift_nilpotency_separation_and_retrocirculant_penrose` (`𝔏𝔖₁`)
- `fourier_character_relative_kernel_and_cosine_sine_circle_degeneracy` (`𝔏𝔖₂`)
- `rope_relative_position_attention_and_clifford_spinor_trace` (`𝔏𝔖₃`)
- `clifford_rope_torus_spiral_normalization_and_gibbs_attention` (`𝔏𝔖₃`)
- `stochastic_grammar_amplitude_sphere_and_gram_logdet_entropy` (`𝔏𝔖₄`)
- `birkhoff_bistochastic_polytope_permutations_and_clifford_markov_channel` (`𝔏𝔖₅`)
- `moe_peirce_hypercube_routing_and_sigmoid_partition` (`𝔏𝔖₆`)
- `yangian_qswap_braid_and_amplituhedron_bcfw_polytope_gluing` (`𝔏𝔖₇`)
- `peirce_centralizer_projection_and_recursive_tensor_homogenization` (`𝔏𝔖₈`)
- `recursive_commuting_peirce_and_artin_wedderburn_centralizer` (`𝔏𝔖₈`)
- `language_statistics_circulant_birkhoff_yangian_peirce_master_synthesis` (`𝔏𝔖₈`)
- `cyclic_gram_fourier_centering_peirce_centralizer_bridge` (`𝔏𝔖₈`)
- `binary_attribute_log_affine` & `finite_binary_attribute_log_factor_decomposition` (`𝔏𝔖₈`)
- `peirce_helper_excursion_attribute_surprisal_and_kms_toeplitz_laplacian` (`𝔏𝔖₈`)
- `z12_residue_arithmetic_and_character_argument` (finite residue arithmetic)
- `peirce_rotor_conjugation_and_commutator` (conditional Peirce identity)
- `conditional_involution_compression_variance` (conditional compression identity)
- `finite_arithmetic_peirce_and_compression_conjunction` (conjunction only; no carrier map)
- `z12_z24_divisor_ramanujan_sum_and_unit_residue_squares` (finite divisor Ramanujan sum calculation)
- `peirce_reflected_rotor_norm_and_off_diagonal_compression_defect` (conditional Peirce norm and off-diagonal compression identity)
- `cl11_tensor_stage_factorization_and_peirce_compression_synthesis` (finite binary stage tensor factorization and conjunction)
- `wigner_clebsch_gordan_mat3_zorn_cross_and_dressed_peirce_bott_synthesis` (finite arithmetic/Catalan calculation, division-free `3 × 3` matrix channel decomposition, Zorn cross-product identity, and conditional dressed Peirce projector / `PeirceIndex` cardinality conjunction)
- `wigner_hurwitz_adams_frobenius_pythagorean_and_d23_filter_synthesis` (scaled idempotency, mutual annihilation, and Frobenius Pythagorean law on `Matrix (Fin 3) (Fin 3) K`, quaternion norm/triality and `D23HurwitzCliffordFilterBank` paraunitarity, and polynomial identity `Phi6 (x^4) = Phi24 x`)

## iii. Table of contents

1. The 8-stage index poset (`𝔏𝔖₁ ≺ ⋯ ≺ 𝔏𝔖₈`) and strict acyclicity
2. Node `𝔏𝔖₁`: Shift centralizer subalgebra, `3 × 3` circulant polynomial expansion, and Toeplitz boundary defect
3. Node `𝔏𝔖₂`: Relative-position Fourier characters, $\mu_k = \mu_{N-k}$ cosine/sine circle degeneracy, and $\mathbb{Z}_4$ mass ladder
4. Node `𝔏𝔖₃`: RoPE relative-position attention, Pointwise Mutual Information (PMI), and native `Cl(5,5)` spinor trace cyclicity
5. Node `𝔏𝔖₄`: Stochastic grammar Born-amplitude sphere, Bhattacharyya inner product, and Gramian log-det compression
6. Node `𝔏𝔖₅`: Birkhoff–von Neumann bistochastic polytope, permutation operators, and split-Clifford Fock Markov channel
7. Node `𝔏𝔖₆`: Clifford–MoE hypercube Peirce routing and logistic sigmoid partition
8. Node `𝔏𝔖₇`: Yang–Baxter $q$-swap braid relation and Amplituhedron BCFW / plabic polytope pole cancellation
9. Node `𝔏𝔖₈`: Recursive Tensor–Peirce dyadic tower, joint centralizer projection, Artin–Wedderburn commutation, and grand master synthesis

## iv. References

- D. Karkada, D. J. Korchinski, A. Nava, M. Wyart, and Y. Bahri, *"Symmetry in language statistics
  shapes the geometry of model representations"*, `arXiv:2602.15029` (2026).
- R. L. Smith, *"Moore–Penrose Inverses of Block Circulant and Block k-Circulant Matrices"*,
  Linear Algebra Appl. 16 (1977), 237–245.
- G. Birkhoff, *"Three observations on linear algebra"*, Univ. Nac. Tucumán Rev. Ser. A 5 (1946).

### Three-Bucket Audit Map (`audit-proof` Policy)

#### BUCKET 1 — Proved Kernel Content
- `causalEdge_acyclic`, `shift_centralizer_subalgebra_and_circulant_indirect_cooccurrence`,
  `cyclic_shift_nilpotency_separation_and_retrocirculant_penrose`.
- `fourier_character_relative_kernel_and_cosine_sine_circle_degeneracy`.
- `rope_relative_position_attention_and_clifford_spinor_trace`,
  `clifford_rope_torus_spiral_normalization_and_gibbs_attention`.
- `stochastic_grammar_amplitude_sphere_and_gram_logdet_entropy`.
- `birkhoff_bistochastic_polytope_permutations_and_clifford_markov_channel`.
- `moe_peirce_hypercube_routing_and_sigmoid_partition`.
- `yangian_qswap_braid_and_amplituhedron_bcfw_polytope_gluing`.
- `peirce_centralizer_projection_and_recursive_tensor_homogenization`.
- `recursive_commuting_peirce_and_artin_wedderburn_centralizer`.
- `language_statistics_circulant_birkhoff_yangian_peirce_master_synthesis`.
- `cyclic_gram_fourier_centering_peirce_centralizer_bridge`.
- `binary_attribute_probability_model_pmi_derivation`,
  `finite_binary_attribute_product_pmi_decomposition`,
  `peirce_helper_excursion_attribute_surprisal_and_kms_toeplitz_laplacian`.
- `z12_residue_arithmetic_and_character_argument`,
  `peirce_rotor_conjugation_and_commutator`,
  `conditional_involution_compression_variance`,
  `finite_arithmetic_peirce_and_compression_conjunction`,
  `z12_z24_divisor_ramanujan_sum_and_unit_residue_squares`,
  `peirce_reflected_rotor_norm_and_off_diagonal_compression_defect`,
  `cl11_tensor_stage_factorization_and_peirce_compression_synthesis`,
  `wigner_clebsch_gordan_mat3_zorn_cross_and_dressed_peirce_bott_synthesis`,
  `wigner_hurwitz_adams_frobenius_pythagorean_and_d23_filter_synthesis`,
  `pin_minus_88_octahedral_reflection_cl11_parity_time_and_abk_triality_synthesis`,
  `kitaev_local_bulk_gap_collar_healing_and_universal_invertibility_rotor_synthesis`.

#### BUCKET 2 — Conditional / Interface Boundaries
- Ring centralizer and Peirce identities hold over `[Ring B]` under explicit hypotheses such as
  `hK1 : S * K1 = K1 * S`, `hK2 : S * K2 = K2 * S`, `hP : P * P = P`, `hQ : Q * Q = Q`, and `hPQ : P * Q = Q * P`.
- BCFW rational cancellation holds over `[Field F]` under `PhysicalFacetsNonzero p`, `hS : S ≠ 0`,
  and `BCFWMatchingCondition p S N_A N_B N₅`.

#### BUCKET 3 — Open / Unformalized
- Empirical corpus estimation of token co-occurrence probabilities $P(x_i, x_j)$ on natural-language
  datasets and nonlinear SGD training dynamics of neural language models remain external empirical
  context outside this algebraic/geometric owner.
-/

/-! The finite translation-symmetry/convolution core is housed in this
canonical owner so the language-statistics spine has one entry point. -/
namespace InfoGeometry.Information.TranslationSymmetryEmbeddings

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

/-- A pair kernel determined by the displacement from its first argument. -/
def DifferenceKernel {A : Type*} (c : G → A) (x y : G) : A := c (y - x)

/-- Translation invariance is equivalent to dependence on the group difference. -/
lemma translationInvariant_iff_differenceKernel {A : Type*} (K : G → G → A) :
    (∀ a x y : G, K (x + a) (y + a) = K x y) ↔
      ∃ c : G → A, ∀ x y, K x y = DifferenceKernel c x y := by
  constructor
  · intro h
    refine ⟨fun d => K 0 d, ?_⟩
    intro x y
    have h' := h (-x) x y
    simpa [DifferenceKernel, sub_eq_add_neg] using h'.symm
  · rintro ⟨c, hc⟩ a x y
    rw [hc, hc]
    simp [DifferenceKernel, add_sub_add_right_eq_sub]

/-- The convolution matrix associated to a displacement kernel. -/
def convolutionMatrix (c : G → ℂ) : Matrix G G ℂ :=
  fun x y => c (y - x)

/-- Translation-invariant kernel matrices have a displacement-kernel form. -/
lemma translationInvariant_matrix_is_convolution
    (K : Matrix G G ℂ) (hK : ∀ a x y, K (x + a) (y + a) = K x y) :
    ∃ c : G → ℂ, K = convolutionMatrix c := by
  refine ⟨fun d => K 0 d, ?_⟩
  ext x y
  simpa [convolutionMatrix, add_sub_add_right_eq_sub, sub_eq_add_neg] using
    (hK (-x) x y).symm

/-- Every convolution matrix is simultaneously translation-invariant. -/
lemma convolutionMatrix_translation_invariant
    (c : G → ℂ) (a x y : G) :
    convolutionMatrix c (x + a) (y + a) = convolutionMatrix c x y := by
  change c ((y + a) - (x + a)) = c (y - x)
  congr 1
  abel

/-- Matrix-level equivalence between translation invariance and convolution form. -/
lemma translationInvariant_matrix_iff_convolution
    (K : Matrix G G ℂ) :
    (∀ a x y, K (x + a) (y + a) = K x y) ↔
      ∃ c : G → ℂ, K = convolutionMatrix c := by
  constructor
  · exact translationInvariant_matrix_is_convolution K
  · rintro ⟨c, hK⟩ a x y
    simpa only [hK] using convolutionMatrix_translation_invariant c a x y

variable [Fintype G]

/-- Simultaneous-translation invariance is closed under finite matrix composition. -/
lemma translationInvariant_matrix_mul [DecidableEq G]
    (K L : Matrix G G ℂ)
    (hK : ∀ a x y, K (x + a) (y + a) = K x y)
    (hL : ∀ a x y, L (x + a) (y + a) = L x y)
    (a x y : G) :
    (K * L) (x + a) (y + a) = (K * L) x y := by
  classical
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp (Equiv.addRight a)
    (fun k : G => K (x + a) k * L k (y + a))]
  apply Finset.sum_congr rfl
  intro k hk
  change K (x + a) (k + a) * L (k + a) (y + a) = K x k * L k y
  rw [hK a x k, hL a k y]

/-- Convolution by `c`, with displacement convention `y - x`. -/
def convolve (c : G → ℂ) (f : G → ℂ) (x : G) : ℂ :=
  ∑ y : G, c (y - x) * f y

/-- The regular translation action on functions on `G`. -/
def translateFunction (a : G) (f : G → ℂ) (x : G) : ℂ := f (x + a)

/-- Convolution commutes with every regular translation. -/
lemma convolve_commutes_translation (c : G → ℂ) (f : G → ℂ) (a x : G) :
    convolve c (translateFunction a f) x =
      translateFunction a (convolve c f) x := by
  unfold convolve translateFunction
  rw [← Equiv.sum_comp (Equiv.addRight (-a))
    (fun y : G => c (y - x) * f (y + a))]
  apply Finset.sum_congr rfl
  intro y hy
  change c ((y + -a) - x) * f ((y + -a) + a) =
    c (y - (x + a)) * f y
  congr 2 <;> abel

/-- A multiplicative character is a convolution eigenmode with its finite
character transform as eigenvalue. -/
lemma character_is_convolution_eigenmode
    (c : G → ℂ) (χ : G → ℂˣ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) (x : G) :
    convolve c (fun y => (χ y : ℂ)) x =
      (∑ d : G, c d * (χ d : ℂ)) * (χ x : ℂ) := by
  unfold convolve
  rw [show (∑ y : G, c (y - x) * (χ y : ℂ)) =
      ∑ d : G, c ((d + x) - x) * (χ (d + x) : ℂ) from by
        simpa using (Equiv.sum_comp (Equiv.addRight x)
          (fun y => c (y - x) * (χ y : ℂ))).symm]
  simp only [add_sub_cancel_right]
  have hχ' : ∀ d, (χ (d + x) : ℂ) = (χ d : ℂ) * (χ x : ℂ) := by
    intro d
    rw [hχ]
    simp
  simp_rw [hχ']
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Finite row-softmax preserves simultaneous translation invariance of scores. -/
lemma translationInvariant_softmaxKernel [Nonempty G]
    (scores : G → G → ℝ)
    (hScores : ∀ t x y, scores (x + t) (y + t) = scores x y)
    (t x y : G) :
    InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionKernel scores (x + t) (y + t) =
      InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionKernel scores x y := by
  have hZ :
      InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.queryPartitionFunction
          scores (x + t) =
        InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.queryPartitionFunction
          scores x := by
    unfold InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.queryPartitionFunction
    calc
      (∑ j : G,
          InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.gibbsCouplingWeight
            scores (x + t) j) =
          ∑ d : G,
            InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.gibbsCouplingWeight
              scores (x + t) (d + t) := by
        symm
        exact Equiv.sum_comp (Equiv.addRight t) _
      _ = ∑ d : G,
            InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.gibbsCouplingWeight
              scores x d := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.gibbsCouplingWeight]
        rw [hScores t x d]
  unfold InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionKernel
  rw [show InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.gibbsCouplingWeight
      scores (x + t) (y + t) =
        InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.gibbsCouplingWeight
          scores x y from by
        simp only [InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.gibbsCouplingWeight]
        rw [hScores t x y], hZ]

end InfoGeometry.Information.TranslationSymmetryEmbeddings

noncomputable section

namespace InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset

open Matrix
open scoped BigOperators ComplexOrder Kronecker TensorProduct
open InfoGeometry.Information.TranslationSymmetryEmbeddings
open InfoGeometry.Canonical.LanguageStatisticsTranslationSymmetry
open InfoGeometry.Canonical.AttentionGlauberCopulaBridge
open InfoGeometry.Canonical.SmithBlockCirculantMoorePenrose
open InfoGeometry.Canonical.Z4CirculantMassLadder
open InfoGeometry.LLM
open InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
open ParafermionCondensationGaloisCharacterPoset
open InfoGeometry.Clifford.Cl55RoPEAttentionPairing
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Routing.AttentionPolytope
open DeterministicArgmaxAttention
open InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge
open InfoGeometry.LinearAlgebra.FiniteGramDeformationEntropy
open BirkhoffRouting
open InfoGeometry.Canonical.GibsonBasicDoublyStochastic
open InfoGeometry.Cantor.PermutationOperator
open InfoGeometry.Clifford.ClNNPermutationSymmetry
open InfoGeometry.Cantor.CliffordMarkovOperators
open InfoGeometry.Clifford.Cl55PeirceMoERouting
open InfoGeometry.Physics.YangBaxterQSwap
open InfoGeometry.AmplituhedronBCFW
open InfoGeometry.Canonical.DoubledPlabicTwistedAmplituhedronFoam
open InfoGeometry.Core.TensorPeirceDecomposition
open InfoGeometry.Clifford.Cl11TensorStageFactorization
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ### Binary log-factor identity (arXiv:2602.15029v3, Appendix D)

This scalar identity proves the log-affine rewrite conditional on factors of the
form `1 + s * x`, with `-1 < s < 1` and `x^2 = 1`. The theorem does not define
probabilities or establish the paper's probabilistic factorization into these
factors. It is separate from the cyclic Fourier results and empirical embedding
claims. -/

/-- For a sign `x² = 1`, the logarithmic factor is affine in `x`. The bounds
`-1 < s < 1` ensure both logarithm arguments in the coefficients are positive. -/
theorem binary_attribute_log_affine
    (s x : ℝ) (hs_lower : -1 < s) (hs_upper : s < 1) (hx : x * x = 1) :
    (0 < 1 + s ∧ 0 < 1 - s) ∧
    Real.log (1 + s * x) =
      (Real.log (1 + s) + Real.log (1 - s)) / 2 +
        ((Real.log (1 + s) - Real.log (1 - s)) / 2) * x := by
  constructor
  · exact ⟨by linarith [hs_lower], by linarith [hs_upper]⟩
  ·
    have hfactor : (x - 1) * (x + 1) = 0 := by nlinarith [hx]
    rcases mul_eq_zero.mp hfactor with hOne | hNegOne
    · have hx1 : x = 1 := by linarith
      rw [hx1, mul_one]
      ring
    · have hxNeg1 : x = -1 := by linarith
      rw [hxNeg1]
      have harg : 1 + s * -1 = 1 - s := by ring
      rw [harg]
      ring

/-- A finite sum of binary log-factors has a constant-plus-feature decomposition.
The factor parameters satisfy `-1 < s r < 1`, and each attribute product is a sign.
Identifying this sum with a PMI quantity requires a separate probability model. -/
theorem finite_binary_attribute_log_factor_decomposition
    {d : ℕ} (s a b : Fin d → ℝ)
    (hs_lower : ∀ r, -1 < s r) (hs_upper : ∀ r, s r < 1)
    (hab : ∀ r, (a r * b r) * (a r * b r) = 1) :
    (∑ r : Fin d, Real.log (1 + s r * (a r * b r))) =
      (∑ r : Fin d, (Real.log (1 + s r) + Real.log (1 - s r)) / 2) +
        ∑ r : Fin d,
          ((Real.log (1 + s r) - Real.log (1 - s r)) / 2) * (a r * b r) := by
  calc
    (∑ r : Fin d, Real.log (1 + s r * (a r * b r))) =
        ∑ r : Fin d,
          ((Real.log (1 + s r) + Real.log (1 - s r)) / 2 +
            ((Real.log (1 + s r) - Real.log (1 - s r)) / 2) * (a r * b r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact binary_attribute_log_affine (s r) (a r * b r)
        (hs_lower r) (hs_upper r) (hab r) |>.2
    _ = (∑ r : Fin d, (Real.log (1 + s r) + Real.log (1 - s r)) / 2) +
          ∑ r : Fin d,
            ((Real.log (1 + s r) - Real.log (1 - s r)) / 2) * (a r * b r) :=
      Finset.sum_add_distrib

/-- Normalized symmetric pair probability on `{±1} × {±1}` with correlation `s`:
`P(x, y) = (1 + s * (x * y)) / 4`. -/
def binaryAttributePairProb (s x y : ℝ) : ℝ :=
  (1 + s * (x * y)) / 4

/-- Marginal probability of `x ∈ {±1}` obtained by summing `binaryAttributePairProb s x y`
over `y ∈ {1, -1}`. -/
def binaryAttributeMarginal (s x : ℝ) : ℝ :=
  binaryAttributePairProb s x 1 + binaryAttributePairProb s x (-1)

/-- Likelihood ratio (joint probability divided by product of marginals) for the
symmetric binary-attribute pair model. -/
def binaryAttributeLikelihoodRatio (s x y : ℝ) : ℝ :=
  binaryAttributePairProb s x y / (binaryAttributeMarginal s x * binaryAttributeMarginal s y)

/-- **Normalized binary-attribute probability model and PMI derivation (`arXiv:2602.15029`, Appendix D, Eq. (44)).**
For correlation `-1 < s < 1` and signs `x, y ∈ {±1}` (`(x * y) * (x * y) = 1`):
1. The four pair probabilities sum to `1` over `{1, -1} × {1, -1}`.
2. Each pair probability `binaryAttributePairProb s x y` is strictly positive.
3. The marginal probabilities satisfy `binaryAttributeMarginal s x = 1 / 2`,
   `binaryAttributeMarginal s y = 1 / 2`, and `binaryAttributeMarginal s 1 + binaryAttributeMarginal s (-1) = 1`.
4. The likelihood ratio `binaryAttributeLikelihoodRatio s x y` equals `1 + s * (x * y)` and is strictly positive.
5. The pointwise mutual information `Real.log (binaryAttributeLikelihoodRatio s x y)` decomposes
   affinely into `(Real.log (1 + s) + Real.log (1 - s)) / 2 + ((Real.log (1 + s) - Real.log (1 - s)) / 2) * (x * y)`. -/
theorem binary_attribute_probability_model_pmi_derivation
    (s x y : ℝ) (hs_lower : -1 < s) (hs_upper : s < 1)
    (hxy : (x * y) * (x * y) = 1) :
    (binaryAttributePairProb s 1 1 + binaryAttributePairProb s 1 (-1) +
       binaryAttributePairProb s (-1) 1 + binaryAttributePairProb s (-1) (-1) = 1) ∧
    0 < binaryAttributePairProb s x y ∧
    (binaryAttributeMarginal s x = 1 / 2 ∧
     binaryAttributeMarginal s y = 1 / 2 ∧
     binaryAttributeMarginal s 1 + binaryAttributeMarginal s (-1) = 1) ∧
    (binaryAttributeLikelihoodRatio s x y = 1 + s * (x * y) ∧
     0 < binaryAttributeLikelihoodRatio s x y) ∧
    Real.log (binaryAttributeLikelihoodRatio s x y) =
      (Real.log (1 + s) + Real.log (1 - s)) / 2 +
        ((Real.log (1 + s) - Real.log (1 - s)) / 2) * (x * y) := by
  have hAff := binary_attribute_log_affine s (x * y) hs_lower hs_upper hxy
  have hLR : binaryAttributeLikelihoodRatio s x y = 1 + s * (x * y) := by
    unfold binaryAttributeLikelihoodRatio binaryAttributeMarginal binaryAttributePairProb
    ring
  have hFactorPos : 0 < 1 + s * (x * y) := by
    have hfactor : (x * y - 1) * (x * y + 1) = 0 := by nlinarith [hxy]
    rcases mul_eq_zero.mp hfactor with hOne | hNegOne
    · have h1 : x * y = 1 := by linarith
      rw [h1, mul_one]
      exact hAff.1.1
    · have hNeg1 : x * y = -1 := by linarith
      rw [hNeg1]
      have harg : 1 + s * -1 = 1 - s := by ring
      rw [harg]
      exact hAff.1.2
  have hProbPos : 0 < binaryAttributePairProb s x y := by
    unfold binaryAttributePairProb
    exact div_pos hFactorPos (by norm_num)
  have hLRPos : 0 < binaryAttributeLikelihoodRatio s x y := by
    rw [hLR]
    exact hFactorPos
  refine ⟨by unfold binaryAttributePairProb; ring,
          hProbPos,
          ⟨by unfold binaryAttributeMarginal binaryAttributePairProb; ring,
           by unfold binaryAttributeMarginal binaryAttributePairProb; ring,
           by unfold binaryAttributeMarginal binaryAttributePairProb; ring⟩,
          ⟨hLR, hLRPos⟩,
          ?_⟩
  rw [hLR]
  exact hAff.2

/-- **Product binary-attribute probability model PMI decomposition (`arXiv:2602.15029`, Appendix D, Eq. (44)).**
For `d` independent binary attributes with correlations `-1 < s r < 1` and sign products
`(a r * b r) * (a r * b r) = 1`, the logarithm of the product likelihood ratio
`∏ r : Fin d, binaryAttributeLikelihoodRatio (s r) (a r) (b r)` decomposes into the sum of
baseline means plus the weighted attribute inner product. -/
theorem finite_binary_attribute_product_pmi_decomposition
    {d : ℕ} (s a b : Fin d → ℝ)
    (hs_lower : ∀ r, -1 < s r) (hs_upper : ∀ r, s r < 1)
    (hab : ∀ r, (a r * b r) * (a r * b r) = 1) :
    (∀ r : Fin d, 0 < binaryAttributeLikelihoodRatio (s r) (a r) (b r)) ∧
    Real.log (∏ r : Fin d, binaryAttributeLikelihoodRatio (s r) (a r) (b r)) =
      (∑ r : Fin d, (Real.log (1 + s r) + Real.log (1 - s r)) / 2) +
        ∑ r : Fin d,
          ((Real.log (1 + s r) - Real.log (1 - s r)) / 2) * (a r * b r) := by
  have hModel (r : Fin d) :=
    binary_attribute_probability_model_pmi_derivation
      (s r) (a r) (b r) (hs_lower r) (hs_upper r) (hab r)
  have hPos : ∀ r : Fin d, 0 < binaryAttributeLikelihoodRatio (s r) (a r) (b r) :=
    fun r => (hModel r).2.2.2.1.2
  refine ⟨hPos, ?_⟩
  have hProdNeZero : ∀ r ∈ (Finset.univ : Finset (Fin d)),
      binaryAttributeLikelihoodRatio (s r) (a r) (b r) ≠ 0 :=
    fun r _ => (hPos r).ne'
  rw [Real.log_prod hProdNeZero]
  have hSumEq :
      (∑ r : Fin d, Real.log (binaryAttributeLikelihoodRatio (s r) (a r) (b r))) =
        ∑ r : Fin d, Real.log (1 + s r * (a r * b r)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [(hModel r).2.2.2.1.1]
  rw [hSumEq]
  exact finite_binary_attribute_log_factor_decomposition s a b hs_lower hs_upper hab

/-- Second-order survival of an involutive micro-attribute under an idempotent
compression. For `L = u + δ σ`, the first-order compressed operator loses the
`δ σ` term when `P σ P = 0`, while the compressed square retains `δ² P` when
`σ² = 1`. The commutation hypotheses state explicitly that the two coefficients
commute with the cut and the involution. This is a conditional operator identity:
the binary PMI theorem above supplies real coefficients, but does not itself
construct a quotient projector or involution action. -/
theorem involution_quotient_second_order_variance
    {B : Type*} [Ring B] (P u delta sigma : B)
    (hP : P * P = P) (hsigma : sigma * sigma = 1)
    (huP : u * P = P * u) (hdP : delta * P = P * delta)
    (hδu : delta * u = u * delta)
    (huσ : u * sigma = sigma * u) (hδσ : delta * sigma = sigma * delta)
    (hmicro : P * sigma * P = 0) :
    P * (u + delta * sigma) * P = u * P ∧
      P * ((u + delta * sigma) * (u + delta * sigma)) * P -
        (P * (u + delta * sigma) * P) * (P * (u + delta * sigma) * P) =
          (delta * delta) * P := by
  have hPU : P * u = u * P := huP.symm
  have hPδ : P * delta = delta * P := hdP.symm
  have hCompression : P * (u + delta * sigma) * P = u * P := by
    calc
      P * (u + delta * sigma) * P
        = (P * u) * P + (P * delta) * sigma * P := by
          simp only [mul_add, add_mul, mul_assoc]
      _ = u * (P * P) + delta * (P * sigma * P) := by
          rw [hPU, hPδ]
          simp only [mul_assoc]
      _ = u * P := by
          rw [hP, hmicro, mul_zero, add_zero]
  refine ⟨hCompression, ?_⟩
  have hL2 :
      (u + delta * sigma) * (u + delta * sigma) =
        (u * u + delta * delta) + (u * delta + u * delta) * sigma := by
    have hdσ2 : delta * sigma * (delta * sigma) = delta * delta := by
      calc
        delta * sigma * (delta * sigma) = delta * (sigma * delta) * sigma := by simp only [mul_assoc]
        _ = delta * delta * (sigma * sigma) := by rw [← hδσ]; simp only [mul_assoc]
        _ = delta * delta := by rw [hsigma, mul_one]
    have Cross :
        u * (delta * sigma) + delta * sigma * u =
          (u * delta + u * delta) * sigma := by
      calc
        u * (delta * sigma) + delta * sigma * u
          = u * delta * sigma + delta * (sigma * u) := by simp only [mul_assoc]
        _ = u * delta * sigma + (delta * u) * sigma := by
            rw [← huσ]
            simp only [mul_assoc]
        _ = (u * delta + u * delta) * sigma := by
            rw [hδu, add_mul]
    calc
      (u + delta * sigma) * (u + delta * sigma)
        = u * u + (u * (delta * sigma) + delta * sigma * u) +
            delta * sigma * (delta * sigma) := by
            simp only [add_mul, mul_add, mul_assoc]
            abel
      _ = (u * u + delta * delta) + (u * delta + u * delta) * sigma := by
          rw [Cross, hdσ2]
          abel
  have h_cross_zero : P * ((u * delta + u * delta) * sigma) * P = 0 := by
    calc
      P * ((u * delta + u * delta) * sigma) * P
        = (P * u * delta + P * u * delta) * sigma * P := by
            simp only [mul_add, add_mul, mul_assoc]
      _ = (u * P * delta + u * P * delta) * sigma * P := by
            rw [hPU]
      _ = (u * (P * delta) + u * (P * delta)) * sigma * P := by
            simp only [mul_assoc]
      _ = (u * delta + u * delta) * (P * sigma * P) := by
            rw [hPδ]
            simp only [add_mul, mul_assoc]
      _ = 0 := by rw [hmicro, mul_zero]
  rw [hCompression, hL2]
  calc
    P * ((u * u + delta * delta) + (u * delta + u * delta) * sigma) * P -
        u * P * (u * P)
      = P * (u * u + delta * delta) * P +
          P * ((u * delta + u * delta) * sigma) * P -
          u * (P * u) * P := by
          simp only [mul_add, add_mul, mul_assoc]
    _ = (u * u + delta * delta) * (P * P) + 0 -
          u * u * (P * P) := by
        rw [h_cross_zero, hPU]
        have h_u2 : P * (u * u) = u * u * P := by
          calc
            P * (u * u) = (P * u) * u := by rw [← mul_assoc]
            _ = (u * P) * u := by rw [hPU]
            _ = u * (P * u) := by rw [mul_assoc]
            _ = u * (u * P) := by rw [hPU]
            _ = u * u * P := by rw [← mul_assoc]
        have h_d2 : P * (delta * delta) = delta * delta * P := by
          calc
            P * (delta * delta) = (P * delta) * delta := by rw [← mul_assoc]
            _ = (delta * P) * delta := by rw [hPδ]
            _ = delta * (P * delta) := by rw [mul_assoc]
            _ = delta * (delta * P) := by rw [hPδ]
            _ = delta * delta * P := by rw [← mul_assoc]
        have h_comm_sum :
            P * (u * u + delta * delta) =
              (u * u + delta * delta) * P := by
          rw [mul_add, h_u2, h_d2, add_mul]
        rw [h_comm_sum]
        simp only [mul_assoc]
    _ = (delta * delta) * P := by
        rw [hP, add_zero, add_mul]
        abel

/-- The second-order compression defect is nonzero in a ring without zero
divisors when both the involution slope and the compressed identity are
nonzero. This records the hypotheses needed for the informal claim that the
micro-attribute variance survives nontrivially. -/
theorem involution_quotient_second_order_variance_ne_zero
    {B : Type*} [Ring B] [NoZeroDivisors B] (P u delta sigma : B)
    (hP : P * P = P) (hsigma : sigma * sigma = 1)
    (huP : u * P = P * u) (hdP : delta * P = P * delta)
    (hδu : delta * u = u * delta)
    (huσ : u * sigma = sigma * u) (hδσ : delta * sigma = sigma * delta)
    (hmicro : P * sigma * P = 0) (hP0 : P ≠ 0) (hδ0 : delta ≠ 0) :
    P * ((u + delta * sigma) * (u + delta * sigma)) * P -
      (P * (u + delta * sigma) * P) * (P * (u + delta * sigma) * P) ≠ 0 := by
  have hVariance :=
    (involution_quotient_second_order_variance P u delta sigma hP hsigma huP hdP
      hδu huσ hδσ hmicro).2
  rw [hVariance]
  exact mul_ne_zero (mul_ne_zero hδ0 hδ0) hP0

-- ============================================================================
-- SECTION 0: THE 8-NODE CAUSAL POSET (𝔏𝔖₁ ≺ ⋯ ≺ 𝔏𝔖₈)
-- ============================================================================

/--
The 8-stage index orders a catalog of finite results. Its numeric rank is declared explicitly;
this is not a theorem-derived causal dependency graph for `arXiv:2602.15029` or the other topics.
-/
inductive LanguageStatisticsPeirceStage : Type
  | LS1_ShiftCentralizerAndCirculantCooccurrence
  | LS2_FourierCharacterAndCircleHarmonicDegeneracy
  | LS3_RoPERelativePositionAndCliffordSpinorTrace
  | LS4_StochasticGrammarSphereAndGramLogDetEntropy
  | LS5_BirkhoffBistochasticPermutationsAndCliffordMarkov
  | LS6_MoEPeirceHypercubeRoutingAndSigmoidPartition
  | LS7_YangianQSwapBraidAndAmplituhedronBCFWPolytope
  | LS8_RecursiveTensorPeirceCentralizerMasterSynthesis
  deriving DecidableEq, Repr

namespace LanguageStatisticsPeirceStage

/-- Declared catalog rank `0..7` of each stage in `LanguageStatisticsPeirceStage`. -/
def rank : LanguageStatisticsPeirceStage → ℕ
  | .LS1_ShiftCentralizerAndCirculantCooccurrence => 0
  | .LS2_FourierCharacterAndCircleHarmonicDegeneracy => 1
  | .LS3_RoPERelativePositionAndCliffordSpinorTrace => 2
  | .LS4_StochasticGrammarSphereAndGramLogDetEntropy => 3
  | .LS5_BirkhoffBistochasticPermutationsAndCliffordMarkov => 4
  | .LS6_MoEPeirceHypercubeRoutingAndSigmoidPartition => 5
  | .LS7_YangianQSwapBraidAndAmplituhedronBCFWPolytope => 6
  | .LS8_RecursiveTensorPeirceCentralizerMasterSynthesis => 7

/-- `rank` is strictly injective across all 8 stages. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

/-- `LinearOrder` on `LanguageStatisticsPeirceStage` lifted along `rank`. -/
instance instLinearOrder : LinearOrder LanguageStatisticsPeirceStage :=
  LinearOrder.lift' rank rank_injective

/-- Rank-order relation on catalog entries, defined by `rank u < rank v`. -/
def causalEdge (u v : LanguageStatisticsPeirceStage) : Bool :=
  decide (rank u < rank v)

/-- Irreflexivity and transitivity of the declared catalog rank order. -/
theorem causalEdge_acyclic :
    (∀ u : LanguageStatisticsPeirceStage, causalEdge u u = false) ∧
    (∀ u v w : LanguageStatisticsPeirceStage,
      causalEdge u v = true → causalEdge v w = true → causalEdge u w = true) := by
  refine ⟨?_, ?_⟩
  · intro u
    simp [causalEdge]
  · intro u v w huv hvw
    simp only [causalEdge, decide_eq_true_eq] at huv hvw ⊢
    exact Nat.lt_trans huv hvw

end LanguageStatisticsPeirceStage

-- ============================================================================
-- NODE 𝔏𝔖₁: Shift Centralizer Subalgebra, Circulant Co-occurrence, & Toeplitz Cut
-- ============================================================================

/--
Symmetric $3 \times 3$ open-interval Toeplitz matrix with diagonal entry `t0`, first
off-diagonal `t1`, and boundary-corner entry `t2`. Unlike the periodic circulant
`blockCirculant3 t0 t1 t1`, when `t2 ≠ t1` the open boundary breaks cyclic shift symmetry.
-/
def symmetricToeplitz3 {R : Type*} [Ring R] (t0 t1 t2 : R) : Mat3 R :=
  !![t0, t1, t2;
     t1, t0, t1;
     t2, t1, t0]

/--
**Theorem 1A (`𝔏𝔖₁` — `shift_centralizer_subalgebra_and_circulant_indirect_cooccurrence`):**
Formalizes the periodic-circulant vs. open-Toeplitz algebraic cut of `arXiv:2602.15029`:
1. **Translation-Invariant Difference Kernel & Matrix Product Closure (`TranslationSymmetryEmbeddings`, `LanguageStatisticsTranslationSymmetry`):**
   `TranslationInvariant K_pair ↔ ∃ c, ∀ x y, K_pair x y = DifferenceKernel c x y`, and
   `(relativeKernelMatrix f * relativeKernelMatrix g) (i_g + a_g) (j_g + a_g) = (relativeKernelMatrix f * relativeKernelMatrix g) i_g j_g`.
2. **Non-Commutative Shift Derivation, Centralizer Subalgebra Closure, & Reynolds Intertwiner (`OperatorCyclotomicParafermions`):**
   For any operator $S$ and $K_1, K_2, Y \in B$, `comm S (K1 * K2) = comm S K1 * K2 + K1 * comm S K2`;
   if $S K_1 = K_1 S$ and $S K_2 = K_2 S$, then $S (K_1 + K_2) = (K_1 + K_2) S$,
   $S (K_1 K_2) = (K_1 K_2) S$, and $S (K_1 K_1) = (K_1 K_1) S$ (indirect co-occurrence closure).
   Moreover, the ordered Reynolds shift sum `parafermionReynoldsRaw n_rey S Y` has telescoping commutator
   `[S, R_n^{raw}(S, Y)] = S^n Y - Y S^n`, which vanishes when `operatorPower n_rey S = 1`
   (`parafermion_reynolds_commutes`), projecting $Y$ into the shift centralizer $\mathcal{Z}(S)$.
3. **Periodic Circulant Polynomial Expansion & Algebraic Bistochasticity (`SmithBlockCirculantMoorePenrose`, `GibsonBasicDoublyStochastic`):**
   `blockCirculant3 A0 A1 A2 = A0 • 1 + A1 • cyclicShift3 + A2 • (cyclicShift3 ^ 2)` with
   `cyclicShift3 ^ 3 = 1`, commutes with `cyclicShift3`, and satisfies
   `IsAlgebraicDoublyStochastic (blockCirculant3 A0 A1 A2)` whenever `A0 + A1 + A2 = 1`.
4. **Open-Interval Toeplitz Boundary Defect:**
   `(symmetricToeplitz3 t0 t1 t2 * cyclicShift3 - cyclicShift3 * symmetricToeplitz3 t0 t1 t2) 0 0 = t2 - t1`.
-/
theorem shift_centralizer_subalgebra_and_circulant_indirect_cooccurrence
    {G : Type*} [AddCommGroup G] [Fintype G]
    {R : Type*} [CommRing R]
    (K_pair : G → G → R) (f_rel g_rel : G → R) (a_g i_g j_g : G)
    {B : Type*} [Ring B] (S K1 K2 Y_rey : B) (n_rey : ℕ)
    (hK1 : S * K1 = K1 * S) (hK2 : S * K2 = K2 * S)
    (hSn_one : InfoGeometry.Algebra.OperatorCyclotomicParafermions.operatorPower n_rey S = 1)
    (A0 A1 A2 t0 t1 t2 : R)
    (hSum1 : A0 + A1 + A2 = 1) :
    ((∀ a x y : G, K_pair (x + a) (y + a) = K_pair x y) ↔
      ∃ c : G → R, ∀ x y, K_pair x y = DifferenceKernel c x y) ∧
    (relativeKernelMatrix f_rel * relativeKernelMatrix g_rel) (i_g + a_g) (j_g + a_g) =
      (relativeKernelMatrix f_rel * relativeKernelMatrix g_rel) i_g j_g ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm S (K1 * K2) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm S K1 * K2 +
        K1 * InfoGeometry.OperatorAlgebra.PeirceSpine.comm S K2 ∧
    (S * (K1 + K2) = (K1 + K2) * S ∧
     S * (K1 * K2) = (K1 * K2) * S ∧
     S * (K1 * K1) = (K1 * K1) * S ∧
     InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator S
       (InfoGeometry.Algebra.OperatorCyclotomicParafermions.parafermionReynoldsRaw n_rey S Y_rey) = 0 ∧
     InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator S
       (InfoGeometry.Algebra.OperatorCyclotomicParafermions.parafermionReynolds n_rey S Y_rey) = 0) ∧
    (blockCirculant3 A0 A1 A2 * cyclicShift3 = cyclicShift3 * blockCirculant3 A0 A1 A2 ∧
     (cyclicShift3 : Mat3 R) ^ 3 = 1 ∧
     blockCirculant3 A0 A1 A2 =
       A0 • (1 : Mat3 R) + A1 • (cyclicShift3 : Mat3 R) + A2 • ((cyclicShift3 : Mat3 R) ^ 2) ∧
     IsAlgebraicDoublyStochastic (blockCirculant3 A0 A1 A2)) ∧
    ((symmetricToeplitz3 t0 t1 t2 * (cyclicShift3 : Mat3 R) -
        (cyclicShift3 : Mat3 R) * symmetricToeplitz3 t0 t1 t2) 0 0 = t2 - t1) := by
  have hLeibniz :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm S (K1 * K2) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm S K1 * K2 +
          K1 * InfoGeometry.OperatorAlgebra.PeirceSpine.comm S K2 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  have hAdd : S * (K1 + K2) = (K1 + K2) * S := by
    calc
      S * (K1 + K2) = S * K1 + S * K2 := mul_add S K1 K2
      _ = K1 * S + K2 * S := by rw [hK1, hK2]
      _ = (K1 + K2) * S := (add_mul K1 K2 S).symm
  have hMul : S * (K1 * K2) = (K1 * K2) * S := by
    calc
      S * (K1 * K2) = (S * K1) * K2 := (mul_assoc S K1 K2).symm
      _ = (K1 * S) * K2 := by rw [hK1]
      _ = K1 * (S * K2) := mul_assoc K1 S K2
      _ = K1 * (K2 * S) := by rw [hK2]
      _ = (K1 * K2) * S := (mul_assoc K1 K2 S).symm
  have hSq : S * (K1 * K1) = (K1 * K1) * S := by
    calc
      S * (K1 * K1) = (S * K1) * K1 := (mul_assoc S K1 K1).symm
      _ = (K1 * S) * K1 := by rw [hK1]
      _ = K1 * (S * K1) := mul_assoc K1 S K1
      _ = K1 * (K1 * S) := by rw [hK1]
      _ = (K1 * K1) * S := (mul_assoc K1 K1 S).symm
  have hRey :=
    InfoGeometry.Algebra.OperatorCyclotomicParafermions.parafermion_reynolds_commutes
      n_rey S Y_rey hSn_one
  have hShiftCube : (cyclicShift3 : Mat3 R) ^ 3 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, pow_zero, cyclicShift3, Matrix.mul_apply, Fin.sum_univ_three]
  have hPoly :
      blockCirculant3 A0 A1 A2 =
        A0 • (1 : Mat3 R) + A1 • (cyclicShift3 : Mat3 R) + A2 • ((cyclicShift3 : Mat3 R) ^ 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockCirculant3, cyclicShift3, pow_succ, pow_zero]
  have hCircStoch : IsAlgebraicDoublyStochastic (blockCirculant3 A0 A1 A2) := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;>
        (simp [blockCirculant3, Fin.sum_univ_three]; linear_combination hSum1)
    · intro j
      fin_cases j <;>
        (simp [blockCirculant3, Fin.sum_univ_three]; linear_combination hSum1)
  have hToepCorner :
      (symmetricToeplitz3 t0 t1 t2 * (cyclicShift3 : Mat3 R) -
        (cyclicShift3 : Mat3 R) * symmetricToeplitz3 t0 t1 t2) 0 0 = t2 - t1 := by
    simp [symmetricToeplitz3, cyclicShift3]
  exact ⟨translationInvariant_iff_differenceKernel K_pair,
    relativeKernelMatrix_mul_translation_invariant f_rel g_rel a_g i_g j_g,
    hLeibniz,
    ⟨hAdd, hMul, hSq, hRey.1, hRey.2⟩,
    ⟨blockCirculant3_commutes_cyclicShift A0 A1 A2, hShiftCube, hPoly, hCircStoch⟩,
    hToepCorner⟩

/--
**Theorem 1B (`𝔏𝔖₁` — `cyclic_shift_nilpotency_separation_and_retrocirculant_penrose`):**
Welds the periodic-vs-open shift operator separation (`CyclicShiftNilpotencySeparation`),
the non-commutative geometric-sum inverse for nilpotent open shifts (`OperatorCyclotomicParafermions`),
and the conjugate two-cycle retrocirculant spectral/Penrose blocks (`ChaoRetrocirculant`,
`SmithRetrocirculantMoorePenrose`):
1. **Periodic `cycle` vs. Open-Boundary Nilpotent `truncatedShift` on `Fin 4 → ℂ` (`CyclicShiftNilpotencySeparation`):**
   `cycle ^ 4 = 1`, `cycle ^ 4 ≠ 0`, `truncatedShift ^ 4 = 0`, `truncatedShift ^ 3 ≠ 0`,
   both intertwine the Fourier coordinate projectors (`cyclic_projector_covariance`,
   `truncated_projector_covariance`), and `coordinateClock * cycle = Complex.I • (cycle * coordinateClock)`.
2. **Open-Boundary Nilpotent Geometric Resolvent & 3-Step Reynolds Centralizer (`OperatorCyclotomicParafermions`):**
   Whenever `T ^ n = 0` in `[Ring B]`, `(1 - T) * operatorGeometricSum n T = 1`; and whenever
   `S * (S * S) = 1` and `(S * S) * S = 1`, the 3-step Reynolds orbit sum
   `Y + S * Y * (S * S) + (S * S) * Y * S` commutes with `S`.
3. **Chao Two-Cycle Determinant & Smith Retrocirculant Moore–Penrose Inverse (`ChaoRetrocirculant`, `SmithRetrocirculantMoorePenrose`):**
   `(-lam) * (-lam) - b_chao * a_chao = twoCycleCharacteristic a_chao b_chao lam` and
   `AlgebraicMoorePenrosePair (retro2 a_ret b_ret) (retro2Plus a_ret b_ret)` for $a_{\mathrm{ret}}, b_{\mathrm{ret}} \neq 0$.
-/
theorem cyclic_shift_nilpotency_separation_and_retrocirculant_penrose
    (k_sec : Fin 4)
    {B : Type*} [Ring B] (n_nil : ℕ) (T S Y : B)
    (hT_nil : T ^ n_nil = 0)
    (hS3_R : S * (S * S) = 1) (hS3_L : (S * S) * S = 1)
    (a_chao b_chao lam : ℂ)
    {K : Type*} [Field K] {a_ret b_ret : K} (ha_ret : a_ret ≠ 0) (hb_ret : b_ret ≠ 0) :
    (InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.cycle ^ 4 = 1 ∧
     InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.cycle ^ 4 ≠ 0 ∧
     InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.truncatedShift ^ 4 = 0 ∧
     InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.truncatedShift ^ 3 ≠ 0 ∧
     InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.cycle *
       InfoGeometry.Algebra.FourthRootSpectralProjectors.projector
         InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.coordinateClock k_sec =
       InfoGeometry.Algebra.FourthRootSpectralProjectors.projector
         InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.coordinateClock
           (InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.nextSector k_sec) *
       InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.cycle ∧
     InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.coordinateClock *
       InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.cycle =
       Complex.I •
         (InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.cycle *
           InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.coordinateClock)) ∧
    ((1 - T) *
       InfoGeometry.Algebra.OperatorCyclotomicParafermions.operatorGeometricSum n_nil T = 1 ∧
     InfoGeometry.Algebra.OperatorCyclotomicParafermions.operatorGeometricSum n_nil T *
       (1 - T) = 1 ∧
     S * (Y + S * Y * (S * S) + (S * S) * Y * S) =
       (Y + S * Y * (S * S) + (S * S) * Y * S) * S) ∧
    ((-lam) * (-lam) - b_chao * a_chao =
       InfoGeometry.Canonical.ChaoRetrocirculant.twoCycleCharacteristic a_chao b_chao lam ∧
     InfoGeometry.Canonical.SmithRetrocirculantMoorePenrose.AlgebraicMoorePenrosePair
       (InfoGeometry.Canonical.SmithRetrocirculantMoorePenrose.retro2 a_ret b_ret)
       (InfoGeometry.Canonical.SmithRetrocirculantMoorePenrose.retro2Plus a_ret b_ret)) := by
  have hGeomInv :=
    InfoGeometry.Algebra.OperatorCyclotomicParafermions.operator_geometric_sum_inverse
      n_nil T hT_nil
  have hRey3 :
      S * (Y + S * Y * (S * S) + (S * S) * Y * S) =
        (Y + S * Y * (S * S) + (S * S) * Y * S) * S := by
    have hL : S * ((S * S) * Y * S) = Y * S := by
      calc
        S * ((S * S) * Y * S) = (S * (S * S)) * Y * S := by noncomm_ring
        _ = 1 * Y * S := by rw [hS3_R]
        _ = Y * S := by noncomm_ring
    have hR : (S * Y * (S * S)) * S = S * Y := by
      calc
        (S * Y * (S * S)) * S = S * Y * ((S * S) * S) := by noncomm_ring
        _ = S * Y * 1 := by rw [hS3_L]
        _ = S * Y := by noncomm_ring
    calc
      S * (Y + S * Y * (S * S) + (S * S) * Y * S) =
          S * Y + (S * S) * Y * (S * S) + S * ((S * S) * Y * S) := by noncomm_ring
      _ = S * Y + (S * S) * Y * (S * S) + Y * S := by rw [hL]
      _ = Y * S + (S * Y * (S * S)) * S + ((S * S) * Y * S) * S := by
          rw [hR]
          noncomm_ring
      _ = (Y + S * Y * (S * S) + (S * S) * Y * S) * S := by noncomm_ring
  exact ⟨⟨InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.cycle_fourth,
          InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.cycle_fourth_ne_zero,
          InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.truncatedShift_fourth,
          InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.truncatedShift_cube_ne_zero,
          InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.cyclic_projector_covariance k_sec,
          InfoGeometry.Algebra.CyclicShiftNilpotencySeparation.clock_shift_relation⟩,
         ⟨hGeomInv.1, hGeomInv.2, hRey3⟩,
         ⟨InfoGeometry.Canonical.ChaoRetrocirculant.twoCycle_det_identity a_chao b_chao lam,
          InfoGeometry.Canonical.SmithRetrocirculantMoorePenrose.retro2_penrose ha_ret hb_ret⟩⟩

/-- A strictly positive translation-invariant kernel induces a translation-
invariant row-softmax Markov kernel when its logarithm is used as the score.
Each softmax entry is exactly the row-normalized kernel. This gives an explicit
map between these finite carriers; it does not identify the kernel with a PMI
matrix or with trained model parameters. -/
theorem positiveTranslationKernel_softmax_bridge
    {G : Type*} [AddCommGroup G] [Fintype G] [Nonempty G]
    (K : G → G → ℝ)
    (hK : ∀ t x y, K (x + t) (y + t) = K x y)
    (hKpos : ∀ x y, 0 < K x y) :
    (∀ x y,
      InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionKernel
        (fun x y => Real.log (K x y)) x y = K x y / ∑ z, K x z) ∧
    (∀ t x y,
      (InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionKernel
        (fun x y => Real.log (K x y))) (x + t) (y + t) =
        InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionKernel
          (fun x y => Real.log (K x y)) x y) := by
  constructor
  · intro x y
    change Real.exp (Real.log (K x y)) /
        (∑ z, Real.exp (Real.log (K x z))) = K x y / ∑ z, K x z
    rw [Real.exp_log (hKpos x y)]
    congr 1
    apply Finset.sum_congr rfl
    intro z hz
    exact Real.exp_log (hKpos x z)
  · apply translationInvariant_softmaxKernel
    intro t x y
    exact congrArg Real.log (hK t x y)

-- ============================================================================
-- NODE 𝔏𝔖₂: Relative-Position Fourier Characters & Cosine/Sine Circle Degeneracy
-- ============================================================================

/--
**Theorem 2 (`𝔏𝔖₂` — `fourier_character_relative_kernel_and_cosine_sine_circle_degeneracy`):**
Unites the Fourier character diagonalization and circular/helical embedding laws of `arXiv:2602.15029`:
1. **Convolution Character Eigenmode (`TranslationSymmetryEmbeddings.character_is_convolution_eigenmode`):**
   Every multiplicative character $\chi : G \to \mathbb{C}^\times$ is an eigenvector of the
   displacement convolution operator `convolve c`, with eigenvalue $\mu_\chi = \sum_d c(d)\chi(d)$.
2. **Translation-Invariant Fourier Character Kernel (`FourierCharacterEncoding`, `FourierCharacterRepresentationBridge`):**
   $\chi(t + (-s)) = \chi(t - s)$, $\chi((a+t) - (a+s)) = \chi(t - s)$, and positional representation
   composition reproduces `fourierCharacterKernel χ t (-s)`.
3. **Symmetric Circulant Conjugate-Mode Eigenvalue Degeneracy ($\mu_k = \mu_{N-k}$):**
   For any symmetric lag coefficients $c_1, c_2$ and conjugate phase pair $(\omega, \omega^{-1})$,
   $c_0 + c_1 \omega + c_1 \omega^{-1} + c_2 \omega^2 + c_2 \omega^{-2}$ is invariant under
   $\omega \leftrightarrow \omega^{-1}$, producing a 2D degenerate eigenspace spanned by cosine
   and sine harmonics.
4. **Planar Circle & Clifford-Torus Embedding Radius (`Z4CirculantMassLadder`):**
   Whenever $c^2 + s^2 = 1$, the scaled harmonic coordinates $(r c, r s)$ lie on the circle of
   squared radius $(r c)^2 + (r s)^2 = r^2$, `det4 (charMat4 m ε phase x) = (x - m)^4 - ε^4 * phase`,
   `(m + ε * c)^2 + (ε * s)^2 = m^2 + ε^2 + 2 * m * ε * c`, and
   `m^2 + ε^2 + 2 * m * ε * (-c) < m^2 + ε^2 + 2 * m * ε * c` for $m, \varepsilon, c > 0$.
5. **Cyclotomic Character-Sum Projectors (`ParafermionCondensationGaloisCharacterPoset`):**
   `(1 - Ω) * cyclicCharacterSum3 Ω = 0` for $\Omega^3 = 1$ and `(U * U) * cyclicCharacterSum4 U = cyclicCharacterSum4 U`
   for $U^4 = 1$.
-/
theorem fourier_character_relative_kernel_and_cosine_sine_circle_degeneracy
    {G : Type*} [AddCommGroup G] [Fintype G]
    (c_conv : G → ℂ) (χ : FourierCharacter G) (a t s : G)
    {K : Type*} [CommRing K] (c0 c1 c2 ω ωInv : K)
    (r m ε phase x c_ang s_ang : ℝ)
    (hCircle : c_ang ^ 2 + s_ang ^ 2 = 1)
    (hm : 0 < m) (hε : 0 < ε) (hc : 0 < c_ang)
    {B : Type*} [Ring B] (Ω U : B)
    (hΩ : Ω * (Ω * Ω) = 1) (hU : U * (U * (U * U)) = 1) :
    (convolve c_conv (fun y => (χ y : ℂ)) t =
       (∑ d : G, c_conv d * (χ d : ℂ)) * (χ t : ℂ) ∧
     fourierCharacterKernel χ t (-s) = χ (t - s) ∧
     fourierCharacterKernel χ (a + t) (-(a + s)) = fourierCharacterKernel χ t (-s) ∧
     ((FourierCharacter.toPositionRepresentation χ).value t ∘
        (FourierCharacter.toPositionRepresentation χ).value (-s)) 1 =
       fourierCharacterKernel χ t (-s)) ∧
    (c0 + c1 * ω + c1 * ωInv + c2 * ω ^ 2 + c2 * ωInv ^ 2 =
       c0 + c1 * ωInv + c1 * ω + c2 * ωInv ^ 2 + c2 * ω ^ 2) ∧
    ((r * c_ang) ^ 2 + (r * s_ang) ^ 2 = r ^ 2 ∧
     det4 (charMat4 m ε phase x) = (x - m) ^ 4 - ε ^ 4 * phase ∧
     (m + ε * c_ang) ^ 2 + (ε * s_ang) ^ 2 = m ^ 2 + ε ^ 2 + 2 * m * ε * c_ang ∧
     m ^ 2 + ε ^ 2 + 2 * m * ε * (-c_ang) < m ^ 2 + ε ^ 2 + 2 * m * ε * c_ang) ∧
    ((1 - Ω) * cyclicCharacterSum3 Ω = 0 ∧
     (U * U) * cyclicCharacterSum4 U = cyclicCharacterSum4 U) := by
  have hConj :
      c0 + c1 * ω + c1 * ωInv + c2 * ω ^ 2 + c2 * ωInv ^ 2 =
        c0 + c1 * ωInv + c1 * ω + c2 * ωInv ^ 2 + c2 * ω ^ 2 := by ring
  have hRadius : (r * c_ang) ^ 2 + (r * s_ang) ^ 2 = r ^ 2 := by
    calc
      (r * c_ang) ^ 2 + (r * s_ang) ^ 2 = r ^ 2 * (c_ang ^ 2 + s_ang ^ 2) := by ring
      _ = r ^ 2 * 1 := by rw [hCircle]
      _ = r ^ 2 := mul_one (r ^ 2)
  have hChar := cyclic_character_sum_ring_identities Ω U hΩ hU
  exact ⟨⟨character_is_convolution_eigenmode c_conv χ χ.map_add' t,
          fourierCharacterKernel_eq_relative χ t s,
          fourierCharacterKernel_add_left χ a t s,
          FourierCharacter.toPositionRepresentation_relative_kernel χ t s⟩,
         hConj,
         ⟨hRadius,
          charMat4_det m ε phase x,
          squared_modulus m ε c_ang s_ang hCircle,
          opposite_phase_separation m ε c_ang hm hε hc⟩,
         ⟨hChar.1, hChar.2.2.2.1⟩⟩

-- ============================================================================
-- NODE 𝔏𝔖₃: RoPE Relative-Position Attention, PMI, & Native Cl(5,5) Spinor Trace
-- ============================================================================

/--
**Theorem 3 (`𝔏𝔖₃` — `rope_relative_position_attention_and_clifford_spinor_trace`):**
Welds the relative-displacement law $K(m, n) = K(m - n)$ and Pointwise Mutual Information (PMI)
of `arXiv:2602.15029` to `TranslationSymmetryEmbeddings.translationInvariant_softmaxKernel`,
`AttentionGlauberCopulaBridge`, rotary positional attention (`Cl55RoPEAttentionPairing`), the
concrete spinor matrix trace on `Cl(5,5)` (`Cl55AttentionRelativePositionBridge`), and the
rectangular row-stochastic Attention Polytope (`AttentionPolytope`):
1. **Translation-Invariant Row-Softmax Markov Kernel (`TranslationSymmetryEmbeddings`):**
   If `scores (x + t) (y + t) = scores x y`, then `TranslationInvariant (softmaxAttentionKernel scores)`.
2. **Pointwise Mutual Information & Expected PMI (`AttentionGlauberCopulaBridge`):**
   `Real.log (attentionDependenceRatio S_pmi i_pmi j_pmi) = Real.log (attentionMatrix S_pmi i_pmi j_pmi) - Real.log (colMarginal S_pmi j_pmi)`
   and `attentionMutualInformation S_pmi = expectedLogDependenceRatio S_pmi`.
3. **Abstract & Concrete `Cl(5,5)` Relative-Position Attention (`Cl55RoPEAttentionPairing`, `Cl55AttentionRelativePositionBridge`):**
   `P.attentionScore W_Q W_K theta0 m n xm xn = P.inner (W_Q xm) (P.R (((n - m : ℤ) : ℝ) * theta0) (W_K xn))`
   and `cliffordAttentionBilinear (rotatedQuery55 i theta posM q) (rotatedKey55 i theta posN k) = scalarTrace55 (ropeRotor55 i ((posM - posN) * theta) * (q * k))`.
4. **Attention Polytope Deterministic Route Decomposition (`AttentionPolytope`):**
   `∑ f, routeWeight A_att f • deterministicAttention f = A_att` with `∑ f, routeWeight A_att f = 1`.
-/
theorem rope_relative_position_attention_and_clifford_spinor_trace
    {G : Type*} [AddCommGroup G] [Fintype G] [Nonempty G]
    (scores : G → G → ℝ) (hScores : ∀ t x y, scores (x + t) (y + t) = scores x y)
    {N_pmi M_pmi : ℕ} [NeZero N_pmi] [NeZero M_pmi]
    (S_pmi : Matrix (Fin N_pmi) (Fin M_pmi) ℝ) (i_pmi : Fin N_pmi) (j_pmi : Fin M_pmi)
    {V X : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]
    (P : InvariantRotorPairing V) (W_Q W_K : X →ₗ[ℝ] V)
    (theta0 : ℝ) (m n : ℤ) (xm xn : X)
    (i : Fin 5) (theta posM posN a_shift : ℝ) (q k : Cl55)
    {N_row M_col : ℕ} (A_att : Matrix (Fin N_row) (Fin M_col) ℝ)
    (hrow : ∀ r_idx, ∑ c_idx, A_att r_idx c_idx = 1) :
    ((∀ t x y : G,
       InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionKernel
         scores (x + t) (y + t) =
       InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel.softmaxAttentionKernel
         scores x y) ∧
     Real.log (attentionDependenceRatio S_pmi i_pmi j_pmi) =
       Real.log (attentionMatrix S_pmi i_pmi j_pmi) - Real.log (colMarginal S_pmi j_pmi) ∧
     attentionMutualInformation S_pmi = expectedLogDependenceRatio S_pmi) ∧
    (P.attentionScore W_Q W_K theta0 m n xm xn =
      P.inner (W_Q xm) (P.R (((n - m : ℤ) : ℝ) * theta0) (W_K xn)) ∧
     (q * InfoGeometry.Clifford.Cl55RoPESplitTorusBridge.ropeRotor55 i (-(posM * theta))) *
        (InfoGeometry.Clifford.Cl55RoPESplitTorusBridge.ropeRotor55 i (posN * theta) * k) =
       q * InfoGeometry.Clifford.Cl55RoPESplitTorusBridge.ropeRotor55 i ((posN - posM) * theta) * k ∧
     cliffordAttentionBilinear (rotatedQuery55 i theta posM q) (rotatedKey55 i theta posN k) =
       scalarTrace55
         (InfoGeometry.Clifford.Cl55RoPESplitTorusBridge.ropeRotor55 i ((posM - posN) * theta) *
           (q * k)) ∧
     cliffordAttentionBilinear (rotatedQuery55 i theta (posM + a_shift) q)
         (rotatedKey55 i theta (posN + a_shift) k) =
       cliffordAttentionBilinear (rotatedQuery55 i theta posM q) (rotatedKey55 i theta posN k)) ∧
    (∑ f : Fin N_row → Fin M_col, routeWeight A_att f = 1 ∧
     (∑ f : Fin N_row → Fin M_col, routeWeight A_att f • deterministicAttention f) = A_att ∧
     convexHull ℝ (Set.range (deterministicAttention (N := N_row) (M := M_col))) =
       attentionPolytope N_row M_col) := by
  have hRoPEShift :
      cliffordAttentionBilinear (rotatedQuery55 i theta (posM + a_shift) q)
        (rotatedKey55 i theta (posN + a_shift) k) =
      cliffordAttentionBilinear (rotatedQuery55 i theta posM q)
        (rotatedKey55 i theta posN k) := by
    have hAngle : ((posM + a_shift) - (posN + a_shift)) * theta = (posM - posN) * theta := by ring
    rw [rotatedAttention_relative_position i theta (posM + a_shift) (posN + a_shift) q k,
        rotatedAttention_relative_position i theta posM posN q k, hAngle]
  exact ⟨⟨translationInvariant_softmaxKernel scores hScores,
          log_attentionDependenceRatio S_pmi i_pmi j_pmi,
          attentionMutualInformation_eq_expectedLogDependenceRatio S_pmi⟩,
         ⟨P.attentionScore_eq_relative W_Q W_K theta0 m n xm xn,
          clifford_relative_position_product i theta posM posN q k,
          rotatedAttention_relative_position i theta posM posN q k,
          hRoPEShift⟩,
         ⟨routeWeight_sum_one A_att hrow,
          reconstruct A_att hrow,
          convexHull_deterministic_eq⟩⟩

/--
**Theorem 3B (`𝔏𝔖₃` — `clifford_rope_torus_spiral_normalization_and_gibbs_attention`):**
Welds the preexisting RoPE and attention owners discovered across `InfoGeometry.Routing`,
`InfoGeometry.QuantumContext`, and `InfoGeometry.Canonical`:
1. **Elliptic & Hyperbolic Clifford RoPE Torus (`CliffordRoPETorus`):**
   `T_ell.R_plane j α * T_ell.R_plane j β = T_ell.R_plane j (α + β)`,
   `T_ell.R_plane j α * T_ell.R_plane j (-α) = 1`,
   `T_ell.transpose_involution (T_ell.R_plane j α) * T_ell.R_plane j α = 1`,
   `T_ell.R_plane i_plane α * T_ell.R_plane j β = T_ell.R_plane j β * T_ell.R_plane i_plane α`,
   and `T_hyp.H_plane j s_rap * T_hyp.H_plane j t_rap = T_hyp.H_plane j (s_rap + t_rap)`.
2. **Discrete RoPE Dot-Product Invariance, Spherical Normalization Commutation, & Limit-Cycle Collapse (`RotaryAttentionSpiralDynamics`):**
   `dotProduct (ropeRotor θ_rot m_pos *ᵥ q_vec) (ropeRotor θ_rot n_pos *ᵥ k_vec) = dotProduct q_vec (ropeRotor θ_rot (n_pos - m_pos) *ᵥ k_vec)`,
   `sphericalNorm2 γ_norm (ropeAct φ_rot v_vec) = ropeAct φ_rot (sphericalNorm2 γ_norm v_vec)`,
   `sphericalNorm2 γ_norm (spiralTrajectory a_sp b_sp θ_rot t_sp v_vec) = ropeAct (θ_rot * t_sp) (sphericalNorm2 γ_norm v_vec)`,
   and `DetailedBalance (softmaxWeight logits β_temp) (stationaryAttentionCoupling logits β_temp)`.
3. **Grand Canonical Gibbs Attention Partition of Unity (`InfoGeometry.Canonical.Attention`):**
   `∑ idx, attentionWeights q_sp ctx matchForm β_temp idx = 1`.
-/
theorem clifford_rope_torus_spiral_normalization_and_gibbs_attention
    {A_tor : Type*} [Ring A_tor] [Algebra ℝ A_tor] {k_tor : ℕ}
    (T_ell : InfoGeometry.Routing.CliffordRoPETorus.EllipticBivectorTorus k_tor A_tor)
    (T_hyp : InfoGeometry.Routing.CliffordRoPETorus.HyperbolicSplitTorus k_tor A_tor)
    (i_plane j : Fin k_tor) (α β s_rap t_rap : ℝ)
    (θ_rot φ_rot γ_norm a_sp b_sp t_sp β_temp : ℝ) (ha_sp : 0 < a_sp)
    (m_pos n_pos : ℤ) (q_vec k_vec v_vec : Fin 2 → ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (logits : ι → ℝ)
    {S_plus S_minus V_val : Type*}
    [AddCommGroup S_plus] [Module ℝ S_plus]
    [AddCommGroup S_minus] [Module ℝ S_minus]
    [AddCommMonoid V_val] [Module ℝ V_val]
    {n_ctx : ℕ} [Fact (0 < n_ctx)]
    (q_sp : S_plus) (ctx : InfoGeometry.Canonical.Attention.ContextWindow n_ctx S_minus V_val)
    (matchForm : S_plus →ₗ[ℝ] S_minus →ₗ[ℝ] ℝ) :
    (T_ell.R_plane j α * T_ell.R_plane j β = T_ell.R_plane j (α + β) ∧
     T_ell.R_plane j α * T_ell.R_plane j (-α) = 1 ∧
     T_ell.transpose_involution (T_ell.R_plane j α) * T_ell.R_plane j α = 1 ∧
     T_ell.R_plane i_plane α * T_ell.R_plane j β = T_ell.R_plane j β * T_ell.R_plane i_plane α ∧
     T_hyp.H_plane j s_rap * T_hyp.H_plane j t_rap = T_hyp.H_plane j (s_rap + t_rap)) ∧
    (dotProduct (InfoGeometry.Routing.DiscreteRoPERepresentation.ropeRotor θ_rot m_pos *ᵥ q_vec)
        (InfoGeometry.Routing.DiscreteRoPERepresentation.ropeRotor θ_rot n_pos *ᵥ k_vec) =
       dotProduct q_vec
         (InfoGeometry.Routing.DiscreteRoPERepresentation.ropeRotor θ_rot (n_pos - m_pos) *ᵥ k_vec) ∧
     InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.sphericalNorm2 γ_norm
        (InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.ropeAct φ_rot v_vec) =
       InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.ropeAct φ_rot
        (InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.sphericalNorm2 γ_norm v_vec) ∧
     InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.sphericalNorm2 γ_norm
        (InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.spiralTrajectory
          a_sp b_sp θ_rot t_sp v_vec) =
       InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.ropeAct (θ_rot * t_sp)
        (InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.sphericalNorm2 γ_norm v_vec) ∧
     InfoGeometry.Probability.DetailedBalance
       (InfoGeometry.QuantumContext.AttentionKMSState.softmaxWeight logits β_temp)
       (InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.stationaryAttentionCoupling
         logits β_temp)) ∧
    (∑ idx : Fin n_ctx,
       InfoGeometry.Canonical.Attention.attentionWeights q_sp ctx matchForm β_temp idx = 1) := by
  have hInv : T_ell.R_plane j α * T_ell.R_plane j (-α) = 1 := by
    rw [T_ell.R_plane_add j α (-α), add_neg_cancel, T_ell.R_plane_zero j]
  exact ⟨⟨T_ell.R_plane_add j α β,
          hInv,
          T_ell.R_plane_orthogonal j α,
          T_ell.R_plane_commute i_plane j α β,
          T_hyp.H_plane_add j s_rap t_rap⟩,
         ⟨InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.rope_dotProduct_relative_invariance
            θ_rot m_pos n_pos q_vec k_vec,
          InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.ropeAct_sphericalNorm2_comm
            γ_norm φ_rot v_vec,
          InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.sphericalNorm2_spiralTrajectory_eq_limitCycle
            a_sp b_sp θ_rot t_sp γ_norm ha_sp v_vec,
          InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics.stationaryAttentionCoupling_detailedBalance
            logits β_temp⟩,
         InfoGeometry.Canonical.Attention.attentionWeights_sum_one q_sp ctx matchForm β_temp⟩

-- ============================================================================
-- NODE 𝔏𝔖₄: Stochastic Grammar Born Sphere, Bhattacharyya Overlap, & Gram Log-Det
-- ============================================================================

/--
**Theorem 4 (`𝔏𝔖₄` — `stochastic_grammar_amplitude_sphere_and_gram_logdet_entropy`):**
Unites stochastic language transition amplitudes (`StochasticGrammarCuntzKriegerBridge`) with
Gramian embedding matrices $G = W^\top W$, permutation invariance of the right Gramian, and
log-det compression potentials (`FiniteGramDeformationEntropy`):
1. **Born-Amplitude Unit-Sphere Normalization:** $\sum_j \Psi(i, j)^2 = 1$ where $\Psi(i, j) = \sqrt{A(i, j)}$.
2. **Bhattacharyya Language Fidelity Inner Product:** $BC_i(M_1, M_2) = \sum_j \Psi_1(i, j)\Psi_2(i, j)$.
3. **Gramian Symmetry, Permutation Invariance, & Determinant Square Law:** For any matrix $J$ and
   permutation $\sigma \in S_n$, $(J^\top J)^\top = J^\top J$,
   $(J.\mathrm{submatrix}\;\sigma\;\mathrm{id})^\top (J.\mathrm{submatrix}\;\sigma\;\mathrm{id}) = J^\top J$,
   $\det(\mathrm{gramDistortion}\;J) = (\det J)^2$, and when $\det J \neq 0$,
   $\mathrm{gramCompressionPotential}\;J = -\log|\det J|$.
-/
theorem stochastic_grammar_amplitude_sphere_and_gram_logdet_entropy
    {n : ℕ} (M1 M2 : StochasticTransitionMatrix n) (i : Fin n)
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.det ≠ 0) (σ : Equiv.Perm (Fin n)) :
    ((Finset.univ : Finset (Fin n)).sum (fun j => (M1.amplitudeMatrix i j) ^ 2) = 1 ∧
     bhattacharyyaLanguageFidelity M1 M2 i =
       (Finset.univ : Finset (Fin n)).sum
         (fun j => M1.amplitudeMatrix i j * M2.amplitudeMatrix i j)) ∧
    ((gramDistortion J).transpose = gramDistortion J ∧
     (J.submatrix σ id).transpose * (J.submatrix σ id) = J.transpose * J ∧
     (gramDistortion J).det = J.det ^ 2 ∧
     0 < (gramDistortion J).det ∧
     gramCompressionPotential J = -Real.log |J.det|) := by
  have hGramSymm : (gramDistortion J).transpose = gramDistortion J := by
    dsimp [gramDistortion]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hGramPerm : (J.submatrix σ id).transpose * (J.submatrix σ id) = J.transpose * J := by
    ext r c
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
    exact Equiv.sum_comp σ (fun k => J k r * J k c)
  exact ⟨⟨M1.amplitude_row_l2_normalization i,
          bhattacharyya_language_fidelity_eq_inner_product M1 M2 i⟩,
         ⟨hGramSymm,
          hGramPerm,
          det_gramDistortion J,
          det_gramDistortion_pos J hJ,
          gramCompressionPotential_eq_neg_log_abs_det J hJ⟩⟩

-- ============================================================================
-- NODE 𝔏𝔖₅: Birkhoff Bistochastic Polytope, Permutations, & Clifford Markov Channel
-- ============================================================================

/--
**Theorem 5 (`𝔏𝔖₅` — `birkhoff_bistochastic_polytope_permutations_and_clifford_markov_channel`):**
Welds the Birkhoff–von Neumann bistochastic polytope (`BirkhoffVonNeumann`,
`GibsonBasicDoublyStochastic`) to faithful permutation representations (`PermutationOperator`),
full `Cl(n,n)` permutation symmetry averaging (`ClNNPermutationSymmetry`), and the split-Clifford
Fock Markov operator channel (`CliffordMarkovOperators`):
1. **Birkhoff–von Neumann Convex Hull Decomposition:** Every doubly stochastic matrix $W$ decomposes
   as $W = \sum_{\sigma \in S_n} w_\sigma P_\sigma$ with $w_\sigma \ge 0$ and $\sum_\sigma w_\sigma = 1$.
2. **Algebraic Bistochastic Multiplicative Closure & Basic $3 \times 3$ Determinant (`GibsonBasicDoublyStochastic`):**
   `IsAlgebraicDoublyStochastic (A * B)` holds whenever $A, B$ are algebraically doubly stochastic,
   and `Matrix.det (basic12 x) = 2 * x - 1`.
3. **Faithful Function-Space Permutation Group Representation (`PermutationOperator`):**
   `Function.Injective (operatorUnitRep (X := Fin n) (R := ℝ))`.
4. **Split-Clifford CAR Generators, `Cl(n,n)` Automorphism Average, & Birkhoff Fock Markov Average (`ClNNPermutationSymmetry`, `CliffordMarkovOperators`):**
   - `randomPermutationCliffordAverage n w 1 = 1` when $\sum_\sigma w(\sigma) = 1$,
   - Every $P \in \mathrm{doublyStochastic}\;\mathbb{R}\;(\mathrm{Fin}\;n)$ lifts to a Birkhoff weight
     distribution $w$ whose `Cl(n,n)` automorphism average acts on primal Clifford generators by
     `randomPermutationCliffordAverage n w (primalCliffordGenerator n v_vec) = primalCliffordGenerator n (P *ᵥ v_vec)`,
   - Each finite Cantor mode Clifford operator squares to $1$ (`cantorModeCliffordOperator n i ^ 2 = 1`)
     and transforms under $w : S_n \to \mathbb{R}$ by
     `randomFockOperatorAverage n w (cantorModeCliffordOperator n i) = ∑ σ, w σ • cantorModeCliffordOperator n (σ i)`.
-/
theorem birkhoff_bistochastic_polytope_permutations_and_clifford_markov_channel
    {n : ℕ} (W P_bvn A B : Matrix (Fin n) (Fin n) ℝ)
    (hW : BirkhoffRouting.IsDoublyStochastic W)
    (hP_bvn : P_bvn ∈ doublyStochastic ℝ (Fin n))
    (hA : IsAlgebraicDoublyStochastic A) (hB : IsAlgebraicDoublyStochastic B)
    (x : ℝ) (w : Equiv.Perm (Fin n) → ℝ) (hw_sum : ∑ σ, w σ = 1) (i : Fin n) :
    (∃ w_bvn : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w_bvn σ) ∧ ∑ σ, w_bvn σ = 1 ∧ ∑ σ, w_bvn σ • σ.permMatrix ℝ = W) ∧
    (IsAlgebraicDoublyStochastic (A * B) ∧
     IsAlgebraicDoublyStochastic A.transpose ∧
     IsAlgebraicDoublyStochastic (basic12 x) ∧
     Matrix.det (basic12 x) = 2 * x - 1 ∧
     Matrix.det (basic12 x) + Matrix.det (basic12 (1 - x)) = 0) ∧
    Function.Injective (operatorUnitRep (X := Fin n) (R := ℝ)) ∧
    (InfoGeometry.Clifford.ClNNPermutationSymmetry.randomPermutationCliffordAverage n w 1 = 1 ∧
     (∃ w_cl : Equiv.Perm (Fin n) → ℝ,
       (∀ σ, 0 ≤ w_cl σ) ∧ ∑ σ, w_cl σ = 1 ∧
       ∀ v_vec : Fin n → ℝ,
         InfoGeometry.Clifford.ClNNPermutationSymmetry.randomPermutationCliffordAverage n w_cl
           (InfoGeometry.Clifford.ClNNPermutationSymmetry.primalCliffordGenerator n v_vec) =
         InfoGeometry.Clifford.ClNNPermutationSymmetry.primalCliffordGenerator n (P_bvn *ᵥ v_vec)) ∧
     cantorModeCliffordOperator n i * cantorModeCliffordOperator n i = 1 ∧
     randomFockOperatorAverage n w (cantorModeCliffordOperator n i) =
       ∑ σ : Equiv.Perm (Fin n), w σ • cantorModeCliffordOperator n (σ i)) := by
  have hTrans : IsAlgebraicDoublyStochastic A.transpose := ⟨hA.2, hA.1⟩
  have hDetAntisymm : Matrix.det (basic12 x) + Matrix.det (basic12 (1 - x)) = 0 := by
    rw [basic12_det x, basic12_det (1 - x)]
    ring
  exact ⟨birkhoff_von_neumann_decomposition W hW,
         ⟨doublyStochastic_mul hA hB,
          hTrans,
          basic12_is_doubly_stochastic x,
          basic12_det x,
          hDetAntisymm⟩,
         operatorUnitRep_injective,
         ⟨InfoGeometry.Clifford.ClNNPermutationSymmetry.randomPermutationCliffordAverage_one n w hw_sum,
          InfoGeometry.Clifford.ClNNPermutationSymmetry.exists_randomPermutationCliffordAverage_primalMatrixAction
            n P_bvn hP_bvn,
          cantorModeCliffordOperator_sq n i,
          randomFockAverage_cantorMode n w i⟩⟩

-- ============================================================================
-- NODE 𝔏𝔖₆: Clifford–MoE Hypercube Peirce Routing & Logistic Sigmoid Partition
-- ============================================================================

/--
**Theorem 6 (`𝔏𝔖₆` — `moe_peirce_hypercube_routing_and_sigmoid_partition`):**
Unites `Cl55PeirceMoERouting.grand_clifford_moe_synthesis` with the canonical Mixture-of-Experts
Gibbs router (`InfoGeometry.Canonical.MoE`):
1. Single-channel split-involution ($K^2 = 1$) Peirce projector idempotence, orthogonality, and
   completeness ($P_+^2 = P_+$, $P_+ P_- = 0$, $P_+ + P_- = 1$), plus exact Peirce spectral
   eigenvalue readout:
   `peircePlus cs * normalizedRoutingFlow cs t = sigmoid (2 * t) • peircePlus cs`.
2. Logistic sigmoid partition identity $\sigma(2t) + \sigma(-2t) = 1$, variance factorization
   $\sigma(2t)(1 - \sigma(2t)) = \sigma(2t)\sigma(-2t)$, and unbiased initialization
   `normalizedRoutingFlow cs 0 = (1 / 2 : ℝ) • 1`.
3. Rank-2 commuting split-pair ($[K_1, K_2] = 0$) 4-expert hypercube completeness
   $P_{++} + P_{+-} + P_{-+} + P_{--} = 1$, mutual expert orthogonality ($P_{++} P_{+-} = 0$,
   $P_{++} P_{-+} = 0$, $P_{++} P_{--} = 0$), universal ring Peirce 4-quadrant partition
   $(P Q) + P(1-Q) + (1-P)Q + (1-P)(1-Q) = 1$, and `InfoGeometry.Canonical.MoE` Gibbs partition
   positivity `0 < routerPartition n_exp β_moe x_tok i_tok` and simplex normalization
   `∑ e : Fin n_exp, normalizedWeights n_exp β_moe x_tok i_tok e = 1`.
-/
theorem moe_peirce_hypercube_routing_and_sigmoid_partition
    {A : Type*} [Ring A] [Algebra ℝ A]
    (cs : SplitInvolution A) (csp : CommutingSplitPair A) (P Q : A) (t : ℝ)
    {Tok V_moe : Type*} [Fintype Tok] [DecidableEq Tok]
      [NormedAddCommGroup V_moe] [NormedSpace ℝ V_moe]
    {n_exp : ℕ} [Nonempty (Fin n_exp)]
    (layer : InfoGeometry.Canonical.MoE.MoELayer n_exp V_moe)
    (β_moe : ℝ) (x_tok : Tok → V_moe) (i_tok : Tok) :
    (peircePlus cs * peircePlus cs = peircePlus cs ∧
     peircePlus cs * peirceMinus cs = 0 ∧
     peircePlus cs + peirceMinus cs = 1 ∧
     peircePlus cs * normalizedRoutingFlow cs t = sigmoid (2 * t) • peircePlus cs ∧
     sigmoid (2 * t) + sigmoid (-(2 * t)) = 1 ∧
     sigmoid (2 * t) * (1 - sigmoid (2 * t)) = sigmoid (2 * t) * sigmoid (-(2 * t)) ∧
     normalizedRoutingFlow cs 0 = (1 / 2 : ℝ) • (1 : A)) ∧
    (expertPlusPlus csp + expertPlusMinus csp + expertMinusPlus csp + expertMinusMinus csp = 1 ∧
     expertPlusPlus csp * expertPlusMinus csp = 0 ∧
     expertPlusPlus csp * expertMinusPlus csp = 0 ∧
     expertPlusPlus csp * expertMinusMinus csp = 0 ∧
     (P * Q) + (P * (1 - Q)) + ((1 - P) * Q) + ((1 - P) * (1 - Q)) = (1 : A)) ∧
    (0 < InfoGeometry.Canonical.MoE.routerPartition n_exp β_moe x_tok i_tok ∧
     (∑ e : Fin n_exp, InfoGeometry.Canonical.MoE.normalizedWeights n_exp β_moe x_tok i_tok e) = 1 ∧
     InfoGeometry.Canonical.MoE.normalizedMixture layer β_moe x_tok i_tok =
       (InfoGeometry.Canonical.MoE.routerPartition n_exp β_moe x_tok i_tok)⁻¹ •
         InfoGeometry.Canonical.MoE.unnormalizedMixture layer β_moe x_tok i_tok) := by
  have hPeirceReadout :
      peircePlus cs * normalizedRoutingFlow cs t = sigmoid (2 * t) • peircePlus cs := by
    dsimp [normalizedRoutingFlow]
    rw [mul_add, Algebra.mul_smul_comm, Algebra.mul_smul_comm,
        peircePlus_idem cs, peirce_orthogonal_pm cs, smul_zero, add_zero]
  have hSigVar : sigmoid (2 * t) * (1 - sigmoid (2 * t)) = sigmoid (2 * t) * sigmoid (-(2 * t)) := by
    have hCompl : 1 - sigmoid (2 * t) = sigmoid (-(2 * t)) := by
      linear_combination -(normalizedRoutingFlow_weights_sum_one t)
    rw [hCompl]
  have hFourQuad : (P * Q) + (P * (1 - Q)) + ((1 - P) * Q) + ((1 - P) * (1 - Q)) = (1 : A) := by
    noncomm_ring
  have hGauge :
      InfoGeometry.Canonical.MoE.normalizedMixture layer β_moe x_tok i_tok =
        (InfoGeometry.Canonical.MoE.routerPartition n_exp β_moe x_tok i_tok)⁻¹ •
          InfoGeometry.Canonical.MoE.unnormalizedMixture layer β_moe x_tok i_tok := by
    unfold InfoGeometry.Canonical.MoE.normalizedMixture
      InfoGeometry.Canonical.MoE.unnormalizedMixture
      InfoGeometry.Canonical.MoE.normalizedWeights
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro e _
    rw [div_eq_inv_mul, mul_smul]
  exact ⟨⟨peircePlus_idem cs,
          peirce_orthogonal_pm cs,
          peirce_sum_one cs,
          hPeirceReadout,
          normalizedRoutingFlow_weights_sum_one t,
          hSigVar,
          normalizedRoutingFlow_zero cs⟩,
         ⟨hypercube_expert_sum_one csp,
          hypercube_expert_orthogonal_pp_pm csp,
          hypercube_expert_orthogonal_pp_mp csp,
          hypercube_expert_orthogonal_pp_mm csp,
          hFourQuad⟩,
         ⟨InfoGeometry.Canonical.MoE.routerPartition_pos n_exp β_moe x_tok i_tok,
          InfoGeometry.Canonical.MoE.normalizedWeights_sum_one n_exp β_moe x_tok i_tok,
          hGauge⟩⟩

-- ============================================================================
-- NODE 𝔏𝔖₇: Yang–Baxter q-Swap Braid & Amplituhedron BCFW / Plabic Polytope Gluing
-- ============================================================================

/--
**Theorem 7 (`𝔏𝔖₇` — `yangian_qswap_braid_and_amplituhedron_bcfw_polytope_gluing`):**
Unites the Yang–Baxter $q$-swap braid identity (`YangBaxterQSwap`), Yangian coproduct tensor
action (`YangianCoproductTensorAction`), and split-octonion Peirce-compressed Yang–Baxter braid
readout (`SplitOctonionPeirceYangBaxterBridge`) with Grassmann–Plücker minor syzygies, Cantor
Plücker transfer weights, and BCFW / plabic polytope gluing (`AmplituhedronBCFW`,
`CantorPlabicTwistorBridge`, `DoubledPlabicTwistedAmplituhedronFoam`):
1. **Yang–Baxter Braid Relation on `Matrix (Fin 8) (Fin 8) ℂ` (`YangBaxterQSwap`):**
   `C12 q * C23 q * C12 q = C23 q * C12 q * C23 q`.
2. **Parametric Braided Yangian R-Matrix QYBE over `[Ring B]`:**
   Whenever $P_{12}^2 = 1$, $P_{23}^2 = 1$, and $P_{12} P_{23} P_{12} = P_{23} P_{12} P_{23}$,
   $(1 + P_{12})(1 + 2 P_{23})(1 + P_{12}) = (1 + P_{23})(1 + 2 P_{12})(1 + P_{23})$.
3. **Yangian Coproduct Tensor Annihilation (`YangianCoproductTensorAction`) & Split-Octonion Peirce Braid Rewrite (`SplitOctonionPeirceYangBaxterBridge`):**
   `T_yang.rhoTensor a_yang (v_yang ⊗ₜ[R_yang] w_yang) = 0` when $\varepsilon(a) = 0$, $\rho_V(a)v = 0$, $\rho_W(a)w = 0$;
   and `peirceCompressedBraidReadout Gate readout X_oct (left_w ++ [i_br, i_br + 1, i_br] ++ right_w) = peirceCompressedBraidReadout Gate readout X_oct (left_w ++ [i_br + 1, i_br, i_br + 1] ++ right_w)`.
4. **Grassmann–Plücker 3-Term Minor Syzygy & Cantor Transfer Weight (`AmplituhedronBCFW`, `CantorPlabicTwistorBridge`):**
   $p_{01} p_{23} + p_{12} p_{03} = p_{02} p_{13}$ for any $2 \times 4$ real matrix $C$,
   `pathTransferWeight u_spec (pluckerAddress i_pl) = (u_spec - 1) ^ 2 * (u_spec + 1) ^ 3`, and
   `projectedTwistorMinor C Z_tw a_tw b_tw` expands by the 6-channel Cauchy–Binet Plücker pairing.
5. **BCFW Polytope Cell Gluing & Plabic Spurious-Pole Cancellation (`AmplituhedronBCFW`, `DoubledPlabicTwistedAmplituhedronFoam`):**
   `cellA p S N_A + cellB p S N_B = globalAmplituhedronForm p N₅` when $S \neq 0$,
   `residueCellA p N_A + residueCellB p N_B = 0` at $S = 0$, and
   `(X_cell + S_spurious) + (Y_cell - S_spurious) = (X_cell + T_spurious) + (Y_cell - T_spurious)`.
-/
theorem yangian_qswap_braid_and_amplituhedron_bcfw_polytope_gluing
    (q : ℂ)
    {B : Type*} [Ring B] (P12 P23 : B)
    (h12_sq : P12 * P12 = 1) (h23_sq : P23 * P23 = 1)
    (h_braid : P12 * P23 * P12 = P23 * P12 * P23)
    {R_yang A_yang V_yang W_yang : Type*}
    [CommRing R_yang] [Ring A_yang] [Module R_yang A_yang] [Coalgebra R_yang A_yang]
    [AddCommGroup V_yang] [Module R_yang V_yang] [AddCommGroup W_yang] [Module R_yang W_yang]
    (T_yang : InfoGeometry.Algebra.YangianCoproductTensorAction
      (R := R_yang) (A := A_yang) (V := V_yang) (W := W_yang))
    (a_yang : A_yang) (v_yang : V_yang) (w_yang : W_yang)
    (hc_yang : (Coalgebra.counit : A_yang →ₗ[R_yang] R_yang) a_yang = 0)
    (hv_yang : T_yang.rhoV a_yang v_yang = 0) (hw_yang : T_yang.rhoW a_yang w_yang = 0)
    {Gate : Type*} (readout : Equiv.Perm ℕ →
      InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct → Gate)
    (X_oct : InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct)
    (i_br : ℕ) (left_w right_w : InfoGeometry.Canonical.FiniteMajoranaBraiding.BraidWord)
    (C : Matrix (Fin 2) (Fin 4) ℝ) (u_spec : ℝ) (i_pl : Fin 6)
    {F : Type*} [Field F] (p : PhysicalFacets F) (S N_A N_B N₅ : F)
    (hp : PhysicalFacetsNonzero p) (hS : S ≠ 0)
    (h_match : BCFWMatchingCondition p S N_A N_B N₅)
    (h_match_zero : BCFWMatchingCondition p 0 N_A N_B N₅)
    {R : Type*} [Ring R] (X_cell Y_cell S_spurious T_spurious : R) :
    C12 q * C23 q * C12 q = C23 q * C12 q * C23 q ∧
    ((1 : B) + P12) * ((1 : B) + P23 + P23) * ((1 : B) + P12) =
      ((1 : B) + P23) * ((1 : B) + P12 + P12) * ((1 : B) + P23) ∧
    (T_yang.rhoTensor a_yang (v_yang ⊗ₜ[R_yang] w_yang) = 0 ∧
     InfoGeometry.OperatorAlgebra.SplitOctonions.PeirceYangBaxterBridge.peirceCompressedBraidReadout
        Gate readout X_oct (left_w ++ [i_br, i_br + 1, i_br] ++ right_w) =
      InfoGeometry.OperatorAlgebra.SplitOctonions.PeirceYangBaxterBridge.peirceCompressedBraidReadout
        Gate readout X_oct (left_w ++ [i_br + 1, i_br, i_br + 1] ++ right_w)) ∧
    InfoGeometry.Canonical.AmplituhedronBCFW.pluckerMinor C 0 1 *
        InfoGeometry.Canonical.AmplituhedronBCFW.pluckerMinor C 2 3 +
      InfoGeometry.Canonical.AmplituhedronBCFW.pluckerMinor C 1 2 *
        InfoGeometry.Canonical.AmplituhedronBCFW.pluckerMinor C 0 3 =
      InfoGeometry.Canonical.AmplituhedronBCFW.pluckerMinor C 0 2 *
        InfoGeometry.Canonical.AmplituhedronBCFW.pluckerMinor C 1 3 ∧
    InfoGeometry.Canonical.CantorPlabicTwistorBridge.pathTransferWeight u_spec
        (InfoGeometry.Canonical.ParaKahlerCantorBridge32.pluckerAddress i_pl) =
      (u_spec - 1) ^ 2 * (u_spec + 1) ^ 3 ∧
    cellA p S N_A + cellB p S N_B = globalAmplituhedronForm p N₅ ∧
    residueCellA p N_A + residueCellB p N_B = 0 ∧
    (X_cell + S_spurious) + (Y_cell - S_spurious) =
      (X_cell + T_spurious) + (Y_cell - T_spurious) := by
  have hQYBE :
      ((1 : B) + P12) * ((1 : B) + P23 + P23) * ((1 : B) + P12) =
        ((1 : B) + P23) * ((1 : B) + P12 + P12) * ((1 : B) + P23) := by
    have hDiff :
        ((1 : B) + P12) * ((1 : B) + P23 + P23) * ((1 : B) + P12) -
        ((1 : B) + P23) * ((1 : B) + P12 + P12) * ((1 : B) + P23) =
          (P12 * P12 - 1) +
          (P12 * P23 * P12 - P23 * P12 * P23) +
          (P12 * P23 * P12 - P23 * P12 * P23) -
          (P23 * P23 - 1) := by
      noncomm_ring
    have hZero :
        (P12 * P12 - 1) +
          (P12 * P23 * P12 - P23 * P12 * P23) +
          (P12 * P23 * P12 - P23 * P12 * P23) -
          (P23 * P23 - 1) = 0 := by
      rw [h12_sq, h23_sq, h_braid]
      abel
    exact sub_eq_zero.mp (hDiff.trans hZero)
  exact ⟨yang_baxter_relation q,
         hQYBE,
         ⟨InfoGeometry.Algebra.tensor_annihilated_of_zero_counit
            T_yang a_yang v_yang w_yang hc_yang hv_yang hw_yang,
          InfoGeometry.OperatorAlgebra.SplitOctonions.PeirceYangBaxterBridge.peirceCompressedBraidReadout_yangBaxter_rewrite
            Gate readout X_oct i_br left_w right_w⟩,
         plucker_spurious_factor C,
         InfoGeometry.Canonical.CantorPlabicTwistorBridge.plucker_paths_transfer_weight u_spec i_pl,
         bcfw_spurious_pole_cancellation p S N_A N_B N₅ hp hS h_match,
         spurious_residue_cancellation p N_A N_B N₅ hp h_match_zero,
         (plabic_square_move_spurious_pole_cancellation X_cell Y_cell S_spurious T_spurious).2.2⟩

-- ============================================================================
-- NODE 𝔏𝔖₈: Recursive Tensor–Peirce Centralizer Decomposition & Master Synthesis
-- ============================================================================

/--
**Theorem 8A (`𝔏𝔖₈` — `peirce_centralizer_projection_and_recursive_tensor_homogenization`):**
Establishes the exact bridge between Peirce centralizers, recursive $2^n \times 2^n$ dyadic
Tensor–Peirce towers (`TensorPeirceDecomposition`), Kronecker stage factorization
(`Cl11TensorStageFactorization`), and the square-zero centralizer differential
(`PeirceSpine.CentralizerDifferential`):
1. **Peirce Centralizer Projection & Off-Diagonal Defect (`PeirceSpine`):**
   For any idempotent $P^2 = P$ in `[Ring B]` and any $X \in B$:
   - The diagonal Peirce projection $\mathtt{evenGrade}\;P\;X = P X P + (1 - P) X (1 - P)$ always
     lies in the centralizer of $P$: $\mathtt{comm}\;P\;(\mathtt{evenGrade}\;P\;X) = 0$.
   - The off-diagonal residual is $\mathtt{oddGrade}\;P\;X$: $X - \mathtt{evenGrade}\;P\;X = \mathtt{oddGrade}\;P\;X$.
   - $X$ commutes with $P$ ($\mathtt{comm}\;P\;X = 0$) if and only if $\mathtt{oddGrade}\;P\;X = 0$
     (equivalently, $X = \mathtt{evenGrade}\;P\;X$).
2. **Centralizer Cochain Differential (`PeirceSpine.CentralizerDifferential`):**
   $\mathtt{superDerivPhi}\;P\;A\;C\;(\mathtt{superDerivPhi}\;P\;A\;C\;X) = 0 \iff \mathtt{genV}\;P\;A\;C \cdot X = X \cdot \mathtt{genV}\;P\;A\;C$.
3. **Recursive Tensor–Peirce Tower & Centralizer Homogenization (`TensorPeirceDecomposition`):**
   - `toTensorTower d (ofTensorTower d T) = T` and `ofTensorTower d (toTensorTower d M) = M` at every
     dyadic depth $d \in \mathbb{N}$,
   - The four homogenized projections `pi00`, `pi01`, `pi10`, `pi11` embed each $m \times m$ Peirce
     block $M_{ab}$ into the diagonal centralizer `Matrix.fromBlocks M_{ab} 0 0 M_{ab} = I_2 ⊗ M_{ab}`.
4. **Finite-Stage Kronecker Tensor Factorization (`Cl11TensorStageFactorization`):**
   `stageTensorFactorization d1 d2 (Matrix.reindex ... (A ⊗ₖ B)) = A ⊗ₜ[ℝ] B`.
-/
theorem peirce_centralizer_projection_and_recursive_tensor_homogenization
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B)
    {R : Type*} [Ring R] (d : ℕ) (T : TensorTower R d) (M : FlatMat R d)
    {m : Type*} [Fintype m] [DecidableEq m] (M00 M01 M10 M11 : Matrix m m R)
    (d1 d2 : ℕ) (A_stage : MatStage d1) (B_stage : MatStage d2) :
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (evenGrade P X) = 0 ∧
     X - evenGrade P X = oddGrade P X ∧
     (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X = 0 ↔ oddGrade P X = 0) ∧
     (superDerivPhi P A C (superDerivPhi P A C X) = 0 ↔
       genV P A C * X = X * genV P A C)) ∧
    (toTensorTower d (ofTensorTower d T) = T ∧
     ofTensorTower d (toTensorTower d M) = M ∧
     pi00 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
       Matrix.fromBlocks M00 0 0 M00 ∧
     pi01 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
       Matrix.fromBlocks M01 0 0 M01 ∧
     pi10 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
       Matrix.fromBlocks M10 0 0 M10 ∧
     pi11 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
       Matrix.fromBlocks M11 0 0 M11) ∧
    stageTensorFactorization d1 d2
        (Matrix.reindex (idxAddEquiv d1 d2).symm (idxAddEquiv d1 d2).symm (A_stage ⊗ₖ B_stage)) =
      A_stage ⊗ₜ[ℝ] B_stage := by
  have hEvenComm : InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (evenGrade P X) = 0 := by
    peirce_nf hP
  have hDiffOdd : X - evenGrade P X = oddGrade P X := by
    dsimp [evenGrade, oddGrade]
    noncomm_ring
  have hCommIffOdd : InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X = 0 ↔ oddGrade P X = 0 := by
    constructor
    · intro hComm
      have hId : P * InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X -
          InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X * P = oddGrade P X := by
        peirce_nf hP
      rw [← hId, hComm, mul_zero, zero_mul, sub_self]
    · intro hOdd
      have hId : P * oddGrade P X - oddGrade P X * P =
          InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X := by
        peirce_nf hP
      rw [← hId, hOdd, mul_zero, zero_mul, sub_self]
  exact ⟨⟨hEvenComm, hDiffOdd, hCommIffOdd, superDerivPhi_square_zero_iff hP A C X⟩,
         ⟨toTensorTower_ofTensorTower d T,
          ofTensorTower_toTensorTower d M,
          fromBlocks_pi_homogenization M00 M01 M10 M11⟩,
         stageTensorFactorization_reindex_kronecker d1 d2 A_stage B_stage⟩

/--
**Theorem 8B (`𝔏𝔖₈` — `recursive_commuting_peirce_and_artin_wedderburn_centralizer`):**
Proves over any associative ring `[Ring B]` the two core algebraic laws of **repeated recursive
tensor decomposition by Peirce projection with centralizers**:
1. **Repeated Two-Stage Commuting Peirce Projection (`evenGrade Q (evenGrade P X)`):**
   For any commuting idempotents $P, Q \in B$ ($P^2 = P$, $Q^2 = Q$, $P Q = Q P$) and any $X \in B$:
   - Order-independence: `evenGrade Q (evenGrade P X) = evenGrade P (evenGrade Q X)`,
   - Four-sector hypercube expansion:
     `evenGrade Q (evenGrade P X) = (P * Q) * X * (P * Q) + (P * (1 - Q)) * X * (P * (1 - Q)) + ((1 - P) * Q) * X * ((1 - P) * Q) + ((1 - P) * (1 - Q)) * X * ((1 - P) * (1 - Q))`,
   - Joint centralizer membership:
     `comm P (evenGrade Q (evenGrade P X)) = 0 ∧ comm Q (evenGrade Q (evenGrade P X)) = 0`.
2. **Artin–Wedderburn Outer Matrix-Unit Centralizer Commutation (`pi00 E00 E01 E10 E11 M`):**
   For any $2 \times 2$ matrix-unit system $E_{00}, E_{01}, E_{10}, E_{11} \in B$ satisfying
   $E_{ij} E_{kl} = \delta_{jk} E_{il}$ and $E_{00} + E_{11} = 1$, the homogenized Tensor–Peirce
   component $\pi_{00}(M) = E_{00} M E_{00} + E_{10} M E_{01}$ commutes with **all four** outer
   matrix units (`comm E00 (pi00 ...) = 0`, `comm E01 (pi00 ...) = 0`, `comm E10 (pi00 ...) = 0`,
   `comm E11 (pi00 ...) = 0`), and $M$ reconstructs as
   $M = E_{00}\pi_{00}(M) + E_{01}\pi_{01}(M) + E_{10}\pi_{10}(M) + E_{11}\pi_{11}(M)$.
-/
theorem recursive_commuting_peirce_and_artin_wedderburn_centralizer
    {B : Type*} [Ring B] {P Q : B}
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = Q * P) (X : B)
    (E00 E01 E10 E11 M : B)
    (h_sum : E00 + E11 = 1)
    (h00_00 : E00 * E00 = E00) (h00_01 : E00 * E01 = E01)
    (h00_10 : E00 * E10 = 0)   (h00_11 : E00 * E11 = 0)
    (h01_00 : E01 * E00 = 0)   (h01_01 : E01 * E01 = 0)
    (h01_10 : E01 * E10 = E00) (h01_11 : E01 * E11 = E01)
    (h10_00 : E10 * E00 = E10) (h10_01 : E10 * E01 = E11)
    (h10_10 : E10 * E10 = 0)   (h10_11 : E10 * E11 = 0)
    (h11_00 : E11 * E00 = 0)   (h11_01 : E11 * E01 = 0)
    (h11_10 : E11 * E10 = E10) (h11_11 : E11 * E11 = E11) :
    (evenGrade Q (evenGrade P X) = evenGrade P (evenGrade Q X) ∧
     evenGrade Q (evenGrade P X) =
       (P * Q) * X * (P * Q) +
       (P * (1 - Q)) * X * (P * (1 - Q)) +
       ((1 - P) * Q) * X * ((1 - P) * Q) +
       ((1 - P) * (1 - Q)) * X * ((1 - P) * (1 - Q)) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (evenGrade Q (evenGrade P X)) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q (evenGrade Q (evenGrade P X)) = 0) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm E00 (pi00 E00 E01 E10 E11 M) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm E01 (pi00 E00 E01 E10 E11 M) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm E10 (pi00 E00 E01 E10 E11 M) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm E11 (pi00 E00 E01 E10 E11 M) = 0 ∧
     E00 * pi00 E00 E01 E10 E11 M +
     E01 * pi01 E00 E01 E10 E11 M +
     E10 * pi10 E00 E01 E10 E11 M +
     E11 * pi11 E00 E01 E10 E11 M = M) := by
  have hQP : Q * P = P * Q := hPQ.symm
  have hPQ_assoc : ∀ z : B, Q * (P * z) = P * (Q * z) := fun z => by
    rw [← mul_assoc, hQP, mul_assoc]
  have hEvenCommOrder : evenGrade Q (evenGrade P X) = evenGrade P (evenGrade Q X) := by
    dsimp [evenGrade]
    simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one,
      mul_assoc, hQP, hPQ_assoc]
    abel
  have hEvenExpand :
      evenGrade Q (evenGrade P X) =
        (P * Q) * X * (P * Q) +
        (P * (1 - Q)) * X * (P * (1 - Q)) +
        ((1 - P) * Q) * X * ((1 - P) * Q) +
        ((1 - P) * (1 - Q)) * X * ((1 - P) * (1 - Q)) := by
    dsimp [evenGrade]
    simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one,
      mul_assoc, hPQ_assoc]
    abel
  have hCommQ : InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q (evenGrade Q (evenGrade P X)) = 0 := by
    peirce_nf hQ
  have hCommP : InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (evenGrade Q (evenGrade P X)) = 0 := by
    rw [hEvenCommOrder]
    peirce_nf hP
  have h00_00' : ∀ z : B, E00 * (E00 * z) = E00 * z := fun z => by rw [← mul_assoc, h00_00]
  have h00_01' : ∀ z : B, E00 * (E01 * z) = E01 * z := fun z => by rw [← mul_assoc, h00_01]
  have h00_10' : ∀ z : B, E00 * (E10 * z) = 0 := fun z => by rw [← mul_assoc, h00_10, zero_mul]
  have h01_00' : ∀ z : B, E01 * (E00 * z) = 0 := fun z => by rw [← mul_assoc, h01_00, zero_mul]
  have h01_01' : ∀ z : B, E01 * (E01 * z) = 0 := fun z => by rw [← mul_assoc, h01_01, zero_mul]
  have h01_10' : ∀ z : B, E01 * (E10 * z) = E00 * z := fun z => by rw [← mul_assoc, h01_10]
  have h01_11' : ∀ z : B, E01 * (E11 * z) = E01 * z := fun z => by rw [← mul_assoc, h01_11]
  have h10_00' : ∀ z : B, E10 * (E00 * z) = E10 * z := fun z => by rw [← mul_assoc, h10_00]
  have h10_01' : ∀ z : B, E10 * (E01 * z) = E11 * z := fun z => by rw [← mul_assoc, h10_01]
  have h10_10' : ∀ z : B, E10 * (E10 * z) = 0 := fun z => by rw [← mul_assoc, h10_10, zero_mul]
  have h11_00' : ∀ z : B, E11 * (E00 * z) = 0 := fun z => by rw [← mul_assoc, h11_00, zero_mul]
  have h11_01' : ∀ z : B, E11 * (E01 * z) = 0 := fun z => by rw [← mul_assoc, h11_01, zero_mul]
  have h11_10' : ∀ z : B, E11 * (E10 * z) = E10 * z := fun z => by rw [← mul_assoc, h11_10]
  have hE00 : InfoGeometry.OperatorAlgebra.PeirceSpine.comm E00 (pi00 E00 E01 E10 E11 M) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, pi00]
    simp only [mul_add, add_mul, mul_assoc, h00_00, h00_00', h00_10', h01_00, mul_zero,
      add_zero, sub_self]
  have hE01 : InfoGeometry.OperatorAlgebra.PeirceSpine.comm E01 (pi00 E00 E01 E10 E11 M) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, pi00]
    simp only [mul_add, add_mul, mul_assoc, h00_01, h01_00', h01_01, h01_10', mul_zero,
      zero_add, add_zero, sub_self]
  have hE10 : InfoGeometry.OperatorAlgebra.PeirceSpine.comm E10 (pi00 E00 E01 E10 E11 M) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, pi00]
    simp only [mul_add, add_mul, mul_assoc, h10_00', h10_10', h00_10, h01_10, mul_zero,
      add_zero, zero_add, sub_self]
  have hE11 : InfoGeometry.OperatorAlgebra.PeirceSpine.comm E11 (pi00 E00 E01 E10 E11 M) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, pi00]
    simp only [mul_add, add_mul, mul_assoc, h11_00', h11_10', h00_11, h01_11, mul_zero,
      zero_add, sub_self]
  exact ⟨⟨hEvenCommOrder, hEvenExpand, hCommP, hCommQ⟩,
         ⟨hE00, hE01, hE10, hE11,
          tensor_peirce_exact_reconstruction E00 E01 E10 E11 M h_sum
            h00_00 h00_10 h01_00 h01_10 h10_01 h10_11 h11_01 h11_11⟩⟩

/--
**Theorem 8C (`𝔏𝔖₈` — `language_statistics_circulant_birkhoff_yangian_peirce_master_synthesis`):**
Finite conjunction collecting results from eight indexed stages. The stage order is a declared
catalog order; the theorem does not prove cross-domain maps or causal implications between all
listed components:
1. Strict poset acyclicity (`LanguageStatisticsPeirceStage.causalEdge_acyclic`),
2. Shift centralizer closure $S K = K S \implies S K^2 = K^2 S$, $3 \times 3$ circulant
   shift commutation, and open-interval Toeplitz corner defect $t_2 - t_1$ (`𝔏𝔖₁`),
3. Convolution character eigenmode `convolve c_conv χ = μ_χ χ`, translation-invariant Fourier
   character kernel $\chi((a+t)-(a+s)) = \chi(t-s)$, and harmonic circle radius $(r c)^2 + (r s)^2 = r^2$ (`𝔏𝔖₂`),
4. Native `Cl(5,5)` RoPE relative-position spinor trace identity and Pointwise Mutual Information
   `Real.log (attentionDependenceRatio S i j) = Real.log (attentionMatrix S i j) - Real.log (colMarginal S j)` (`𝔏𝔖₃`),
5. Stochastic grammar Born-amplitude unit sphere $\sum_j \Psi(i, j)^2 = 1$ and Gramian determinant
   square law $\det(J^\top J) = (\det J)^2$ (`𝔏𝔖₄`),
6. Birkhoff–von Neumann bistochastic decomposition $W = \sum_{\sigma \in S_n} w_\sigma P_\sigma$
   and split-Clifford Fock Markov average (`𝔏𝔖₅`),
7. Clifford–MoE 4-expert hypercube completeness $P_{++} + P_{+-} + P_{-+} + P_{--} = 1$ and
   sigmoid partition $\sigma(2t) + \sigma(-2t) = 1$ (`𝔏𝔖₆`),
8. Yang–Baxter $q$-swap braid identity $C_{12}(q) C_{23}(q) C_{12}(q) = C_{23}(q) C_{12}(q) C_{23}(q)$ (`𝔏𝔖₇`),
9. Recursive Tensor–Peirce dyadic round-trip `ofTensorTower d (toTensorTower d M) = M`,
   Peirce centralizer characterization $\mathtt{comm}\;P\;X = 0 \iff \mathtt{oddGrade}\;P\;X = 0$,
   and commuting two-stage Peirce centralizer commutativity `evenGrade Q (evenGrade P X) = evenGrade P (evenGrade Q X)` (`𝔏𝔖₈`).
-/
theorem language_statistics_circulant_birkhoff_yangian_peirce_master_synthesis
    {B : Type*} [Ring B] {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = Q * P)
    (S K X : B) (hSK : S * K = K * S)
    {R : Type*} [CommRing R] (A0 A1 A2 t0 t1 t2 : R)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (c_conv : G → ℂ) (χ : FourierCharacter G) (a t_pos s_pos : G)
    (r c_ang s_ang : ℝ) (hCircle : c_ang ^ 2 + s_ang ^ 2 = 1)
    {N_pmi M_pmi : ℕ} [NeZero N_pmi] [NeZero M_pmi]
    (S_pmi : Matrix (Fin N_pmi) (Fin M_pmi) ℝ) (i_pmi : Fin N_pmi) (j_pmi : Fin M_pmi)
    (i_plane : Fin 5) (theta posM posN : ℝ) (q_cl k_cl : Cl55)
    {n : ℕ} (M_gram : StochasticTransitionMatrix n) (i_state : Fin n)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : BirkhoffRouting.IsDoublyStochastic W)
    (w_perm : Equiv.Perm (Fin n) → ℝ)
    {A_alg : Type*} [Ring A_alg] [Algebra ℝ A_alg] (csp : CommutingSplitPair A_alg) (t_route : ℝ)
    (q_yb : ℂ) (d : ℕ) (M_dyadic : FlatMat R d) :
    ((∀ u : LanguageStatisticsPeirceStage, LanguageStatisticsPeirceStage.causalEdge u u = false) ∧
     S * (K * K) = (K * K) * S ∧
     blockCirculant3 A0 A1 A2 * cyclicShift3 = cyclicShift3 * blockCirculant3 A0 A1 A2 ∧
     (symmetricToeplitz3 t0 t1 t2 * (cyclicShift3 : Mat3 R) -
        (cyclicShift3 : Mat3 R) * symmetricToeplitz3 t0 t1 t2) 0 0 = t2 - t1) ∧
    (convolve c_conv (fun y => (χ y : ℂ)) t_pos =
       (∑ d_g : G, c_conv d_g * (χ d_g : ℂ)) * (χ t_pos : ℂ) ∧
     fourierCharacterKernel χ (a + t_pos) (-(a + s_pos)) = fourierCharacterKernel χ t_pos (-s_pos) ∧
     (r * c_ang) ^ 2 + (r * s_ang) ^ 2 = r ^ 2 ∧
     Real.log (attentionDependenceRatio S_pmi i_pmi j_pmi) =
       Real.log (attentionMatrix S_pmi i_pmi j_pmi) - Real.log (colMarginal S_pmi j_pmi) ∧
     cliffordAttentionBilinear (rotatedQuery55 i_plane theta posM q_cl)
         (rotatedKey55 i_plane theta posN k_cl) =
       scalarTrace55
         (InfoGeometry.Clifford.Cl55RoPESplitTorusBridge.ropeRotor55 i_plane
            ((posM - posN) * theta) * (q_cl * k_cl))) ∧
    ((Finset.univ : Finset (Fin n)).sum (fun j => (M_gram.amplitudeMatrix i_state j) ^ 2) = 1 ∧
     (gramDistortion J).det = J.det ^ 2 ∧
     (∃ w_bvn : Equiv.Perm (Fin n) → ℝ,
       (∀ σ, 0 ≤ w_bvn σ) ∧ ∑ σ, w_bvn σ = 1 ∧ ∑ σ, w_bvn σ • σ.permMatrix ℝ = W) ∧
     randomFockOperatorAverage n w_perm (cantorModeCliffordOperator n i_state) =
       ∑ σ : Equiv.Perm (Fin n), w_perm σ • cantorModeCliffordOperator n (σ i_state)) ∧
    (expertPlusPlus csp + expertPlusMinus csp + expertMinusPlus csp + expertMinusMinus csp = 1 ∧
     sigmoid (2 * t_route) + sigmoid (-(2 * t_route)) = 1 ∧
     C12 q_yb * C23 q_yb * C12 q_yb = C23 q_yb * C12 q_yb * C23 q_yb ∧
     ofTensorTower d (toTensorTower d M_dyadic) = M_dyadic ∧
     (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X = 0 ↔ oddGrade P X = 0) ∧
     evenGrade Q (evenGrade P X) = evenGrade P (evenGrade Q X) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q (evenGrade Q (evenGrade P X)) = 0) := by
  have hSq : S * (K * K) = (K * K) * S := by
    calc
      S * (K * K) = (S * K) * K := (mul_assoc S K K).symm
      _ = (K * S) * K := by rw [hSK]
      _ = K * (S * K) := mul_assoc K S K
      _ = K * (K * S) := by rw [hSK]
      _ = (K * K) * S := (mul_assoc K K S).symm
  have hToepCorner :
      (symmetricToeplitz3 t0 t1 t2 * (cyclicShift3 : Mat3 R) -
        (cyclicShift3 : Mat3 R) * symmetricToeplitz3 t0 t1 t2) 0 0 = t2 - t1 := by
    simp [symmetricToeplitz3, cyclicShift3]
  have hRadius : (r * c_ang) ^ 2 + (r * s_ang) ^ 2 = r ^ 2 := by
    calc
      (r * c_ang) ^ 2 + (r * s_ang) ^ 2 = r ^ 2 * (c_ang ^ 2 + s_ang ^ 2) := by ring
      _ = r ^ 2 * 1 := by rw [hCircle]
      _ = r ^ 2 := mul_one (r ^ 2)
  have hCommIffOdd : InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X = 0 ↔ oddGrade P X = 0 := by
    constructor
    · intro hComm
      have hId : P * InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X -
          InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X * P = oddGrade P X := by
        peirce_nf hP
      rw [← hId, hComm, mul_zero, zero_mul, sub_self]
    · intro hOdd
      have hId : P * oddGrade P X - oddGrade P X * P =
          InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X := by
        peirce_nf hP
      rw [← hId, hOdd, mul_zero, zero_mul, sub_self]
  have hQP : Q * P = P * Q := hPQ.symm
  have hPQ_assoc : ∀ z : B, Q * (P * z) = P * (Q * z) := fun z => by
    rw [← mul_assoc, hQP, mul_assoc]
  have hEvenCommOrder : evenGrade Q (evenGrade P X) = evenGrade P (evenGrade Q X) := by
    dsimp [evenGrade]
    simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one,
      mul_assoc, hQP, hPQ_assoc]
    abel
  have hCommQ : InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q (evenGrade Q (evenGrade P X)) = 0 := by
    peirce_nf hQ
  exact ⟨⟨LanguageStatisticsPeirceStage.causalEdge_acyclic.1,
          hSq,
          blockCirculant3_commutes_cyclicShift A0 A1 A2,
          hToepCorner⟩,
         ⟨character_is_convolution_eigenmode c_conv χ χ.map_add' t_pos,
          fourierCharacterKernel_add_left χ a t_pos s_pos,
          hRadius,
          log_attentionDependenceRatio S_pmi i_pmi j_pmi,
          rotatedAttention_relative_position i_plane theta posM posN q_cl k_cl⟩,
         ⟨M_gram.amplitude_row_l2_normalization i_state,
          det_gramDistortion J,
          birkhoff_von_neumann_decomposition W hW,
          randomFockAverage_cantorMode n w_perm i_state⟩,
         ⟨hypercube_expert_sum_one csp,
          normalizedRoutingFlow_weights_sum_one t_route,
          yang_baxter_relation q_yb,
          ofTensorTower_toTensorTower d M_dyadic,
          hCommIffOdd,
          hEvenCommOrder,
          hCommQ⟩⟩

/--
**Theorem 8D (`𝔏𝔖₈` — `cyclic_gram_fourier_centering_peirce_centralizer_bridge`):**
Welds the 5 finite cyclic Gram and Fourier centering pillars of `arXiv:2602.15029v3`
(Proposition 1 / Appendix E.2, formalized in `ZModFourierBridge` and `CyclicGramGeometry`)
directly to the repository's `PeirceSpine` (`comm`, `peirce11`, `oddGrade`):
1. **Translation Symmetry $\iff$ Circulant Matrix (`matrix_translation_invariant_iff_eq_circulant`):**
   `(∀ i j a, M_zmod (i + a) (j + a) = M_zmod i j) ↔ M_zmod = Matrix.circulant (fun i => M_zmod i 0)`.
2. **Fourier Character Eigenvectors & Full `ZMod.dft` Diagonalization (`ZModFourierBridge`):**
   `Module.End.HasEigenvector (Matrix.circulant κ).mulVecLin (ZMod.dft κ k) (fun i => ZMod.stdAddChar (k * i))`
   and `ZMod.dft (Matrix.circulant κ *ᵥ v) = ZMod.dft κ * ZMod.dft v`.
3. **Cyclic Centering $P = I - N^{-1} J$ as a Self-Adjoint Peirce Centralizer Projector (`CyclicGramGeometry` + `PeirceSpine`):**
   - $P^2 = P$ (`cyclicCentering_mul_self`) and $P^* = P$ (`cyclicCentering_conjTranspose`),
   - Every circulant matrix lies in the Peirce centralizer of `cyclicCentering N`:
     `comm (cyclicCentering N) (Matrix.circulant κ) = 0` and `oddGrade (cyclicCentering N) (Matrix.circulant κ) = 0`,
   - The $(1, 1)$ Peirce corner `peirce11 (cyclicCentering N) (Matrix.circulant κ)` equals the
     mean-subtracted circulant `Matrix.circulant (fun a => κ a - (N : ℂ)⁻¹ * ∑ b, κ b)`,
   - Full inverse-DFT reconstruction (`centered_circulant_mulVec_eq_invDFT`):
     `(cyclicCentering N * Matrix.circulant κ * cyclicCentering N) *ᵥ v = ZMod.dft.symm (fun k => (if k = 0 then 0 else ZMod.dft κ k) * ZMod.dft v k)`.
4. **Autocorrelation Positive Semidefinite Gram Matrix & Spectrum (`CyclicGramGeometry`):**
   `Matrix.circulant (cyclicAutocorrelation g) = Matrix.circulant g * (Matrix.circulant g)ᴴ`,
   `(Matrix.circulant (cyclicAutocorrelation g)).PosSemidef`, and
   `ZMod.dft (cyclicAutocorrelation g) k = (Complex.normSq (ZMod.dft g k) : ℂ)`.
5. **Explicit 2D Real Fourier Coordinate Embedding (`cyclicRealFourierPair`):**
   `(cyclicRealFourierPair a_amp k * (cyclicRealFourierPair a_amp k).transpose) i j = a_amp ^ 2 * (ZMod.stdAddChar (k * (i - j))).re`,
   `cyclicRealFourierPair a_amp k * (cyclicRealFourierPair a_amp k).transpose = Matrix.circulant (fun i => a_amp ^ 2 * (ZMod.stdAddChar (k * i)).re)`,
   and constant diagonal `(cyclicRealFourierPair a_amp k * (cyclicRealFourierPair a_amp k).transpose) i i = a_amp ^ 2`.
-/
theorem cyclic_gram_fourier_centering_peirce_centralizer_bridge
    {N : ℕ} [NeZero N]
    (M_zmod : Matrix (ZMod N) (ZMod N) ℂ)
    (κ v g : ZMod N → ℂ) (k i j : ZMod N) (a_amp : ℝ) :
    (((∀ i' j' a', M_zmod (i' + a') (j' + a') = M_zmod i' j') ↔
        M_zmod = Matrix.circulant (fun i' => M_zmod i' 0)) ∧
     Module.End.HasEigenvector (Matrix.circulant κ).mulVecLin
       (ZMod.dft κ k) (fun i' => ZMod.stdAddChar (k * i')) ∧
     ZMod.dft (Matrix.circulant κ *ᵥ v) = ZMod.dft κ * ZMod.dft v) ∧
    (cyclicCentering N * cyclicCentering N = cyclicCentering N ∧
     (cyclicCentering N)ᴴ = cyclicCentering N ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm (cyclicCentering N) (Matrix.circulant κ) = 0 ∧
     oddGrade (cyclicCentering N) (Matrix.circulant κ) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (cyclicCentering N) (Matrix.circulant κ) =
       Matrix.circulant (fun a => κ a - (N : ℂ)⁻¹ * ∑ b, κ b) ∧
     (cyclicCentering N * Matrix.circulant κ * cyclicCentering N) *ᵥ v =
       ZMod.dft.symm (fun k' => (if k' = 0 then 0 else ZMod.dft κ k') * ZMod.dft v k')) ∧
    (Matrix.circulant (cyclicAutocorrelation g) = Matrix.circulant g * (Matrix.circulant g)ᴴ ∧
     (Matrix.circulant (cyclicAutocorrelation g)).PosSemidef ∧
     ZMod.dft (cyclicAutocorrelation g) k = (Complex.normSq (ZMod.dft g k) : ℂ)) ∧
    ((cyclicRealFourierPair a_amp k * (cyclicRealFourierPair a_amp k).transpose) i j =
       a_amp ^ 2 * (ZMod.stdAddChar (k * (i - j))).re ∧
     cyclicRealFourierPair a_amp k * (cyclicRealFourierPair a_amp k).transpose =
       Matrix.circulant (fun i' => a_amp ^ 2 * (ZMod.stdAddChar (k * i')).re) ∧
     (cyclicRealFourierPair a_amp k * (cyclicRealFourierPair a_amp k).transpose) i i =
       a_amp ^ 2) := by
  have hCenterComm :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (cyclicCentering N) (Matrix.circulant κ) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    rw [cyclicCentering_mul_circulant_comm κ, sub_self]
  have hCenterOdd : oddGrade (cyclicCentering N) (Matrix.circulant κ) = 0 := by
    have hPlus : cyclicCentering N * Matrix.circulant κ * (1 - cyclicCentering N) = 0 := by
      calc
        cyclicCentering N * Matrix.circulant κ * (1 - cyclicCentering N) =
            cyclicCentering N * Matrix.circulant κ -
              (cyclicCentering N * Matrix.circulant κ) * cyclicCentering N := by
          noncomm_ring
        _ = cyclicCentering N * Matrix.circulant κ -
              (Matrix.circulant κ * cyclicCentering N) * cyclicCentering N := by
          rw [cyclicCentering_mul_circulant_comm κ]
        _ = cyclicCentering N * Matrix.circulant κ -
              Matrix.circulant κ * (cyclicCentering N * cyclicCentering N) := by
          rw [mul_assoc]
        _ = 0 := by
          rw [cyclicCentering_mul_self, cyclicCentering_mul_circulant_comm κ, sub_self]
    have hMinus : (1 - cyclicCentering N) * Matrix.circulant κ * cyclicCentering N = 0 := by
      calc
        (1 - cyclicCentering N) * Matrix.circulant κ * cyclicCentering N =
            Matrix.circulant κ * cyclicCentering N -
              cyclicCentering N * (Matrix.circulant κ * cyclicCentering N) := by
          noncomm_ring
        _ = Matrix.circulant κ * cyclicCentering N -
              cyclicCentering N * (cyclicCentering N * Matrix.circulant κ) := by
          rw [← cyclicCentering_mul_circulant_comm κ]
        _ = Matrix.circulant κ * cyclicCentering N -
              (cyclicCentering N * cyclicCentering N) * Matrix.circulant κ := by
          rw [← mul_assoc]
        _ = 0 := by
          rw [cyclicCentering_mul_self, cyclicCentering_mul_circulant_comm κ, sub_self]
    dsimp [oddGrade]
    rw [hPlus, hMinus, zero_add]
  have hPeirce11 :
      InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (cyclicCentering N) (Matrix.circulant κ) =
        Matrix.circulant (fun a => κ a - (N : ℂ)⁻¹ * ∑ b, κ b) := by
    simpa [InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11] using
      (cyclicCentering_circulant κ)
  exact ⟨⟨matrix_translation_invariant_iff_eq_circulant M_zmod,
          circulant_hasEigenvector_stdAddChar κ k,
          dft_circulant_mulVec κ v⟩,
         ⟨cyclicCentering_mul_self,
          cyclicCentering_conjTranspose,
          hCenterComm,
          hCenterOdd,
          hPeirce11,
          centered_circulant_mulVec_eq_invDFT κ v⟩,
         ⟨cyclicAutocorrelation_gram g,
          cyclicAutocorrelation_posSemidef g,
          dft_cyclicAutocorrelation_eq_normSq g k⟩,
         ⟨cyclicRealFourierPair_gram_apply a_amp k i j,
          cyclicRealFourierPair_gram_eq_circulant a_amp k,
          cyclicRealFourierPair_gram_diag a_amp k i⟩⟩

/--
The $3 \times 3$ tridiagonal discrete Laplacian / AR(1) precision matrix associated to the
Kac–Murdock–Szegő open-chain exponential Toeplitz matrix `symmetricToeplitz3 1 ρ (ρ ^ 2)`:
`kmsTridiagonalLaplacian3 ρ = !![1, -ρ, 0; -ρ, 1 + ρ^2, -ρ; 0, -ρ, 1]`.
-/
def kmsTridiagonalLaplacian3 {R : Type*} [Ring R] (ρ : R) : Mat3 R :=
  !![1, -ρ, 0;
     -ρ, 1 + ρ ^ 2, -ρ;
     0, -ρ, 1]

/--
**Theorem 8E (`𝔏𝔖₈` — `peirce_helper_excursion_attribute_surprisal_and_kms_toeplitz_laplacian`):**
Formalizes the four structural representation-geometry laws of `arXiv:2602.15029`
(Sections 2.1.1–2.1.2 and Appendix D Eq. (44)):
1. **Two-Hop Helper-Word Peirce Excursion (`Q_+ = N_+ N_- = conePlus P M * coneMinus P M`):**
   - For any idempotent $P^2 = P$ and operator $M \in B$ in `[Ring B]`, the $(1, 1)$ Peirce block
     of the two-hop square $M^2$ decomposes as:
     `P * (M * M) * P = (P * M * P) * (P * M * P) + conePlus P M * coneMinus P M`.
   - When direct co-occurrences inside the $P$-subspace (e.g., month-to-month co-occurrences) are
     deleted (`P * M * P = 0`), the two-hop $(1, 1)$ block reduces purely to the off-diagonal
     helper-word excursion `P * (M * M) * P = conePlus P M * coneMinus P M`.
   - Whenever a shift operator $S \in B$ commutes with $P$ (`comm S P = 0`) and with $M$
     (`comm S M = 0`), $S$ commutes with both off-diagonal transitions (`comm S (conePlus P M) = 0`,
     `comm S (coneMinus P M) = 0`) and with their excursion product
     `comm S (conePlus P M * coneMinus P M) = 0`, preserving the translation-invariant circulant
     Fourier circle even when `P * M * P = 0`.
2. **Binary Attribute PMI Eq. (44) (`log(1 + s (a b))`) Affine Collapse (`binary_attribute_log_affine`):**
   Whenever $-1 < s < 1$ and $x^2 = 1$,
   `Real.log (1 + s * x) = (Real.log (1 + s) + Real.log (1 - s)) / 2 + ((Real.log (1 + s) - Real.log (1 - s)) / 2) * x`.
3. **Open 1D Chain Kac–Murdock–Szegő Symmetric Toeplitz Matrix & Exact Tridiagonal Discrete Laplacian Inverse:**
   Over any `[CommRing R]`, `symmetricToeplitz3 1 ρ (ρ ^ 2) * kmsTridiagonalLaplacian3 ρ = (1 - ρ ^ 2) • 1`
   and `kmsTridiagonalLaplacian3 ρ * symmetricToeplitz3 1 ρ (ρ ^ 2) = (1 - ρ ^ 2) • 1`, with zero
   long-range corners (`kmsTridiagonalLaplacian3 ρ 0 2 = 0 ∧ kmsTridiagonalLaplacian3 ρ 2 0 = 0`) and
   interior-vs-boundary diagonal excess `kmsTridiagonalLaplacian3 ρ 1 1 - kmsTridiagonalLaplacian3 ρ 0 0 = ρ ^ 2`.
4. **Higher-Harmonic Lissajous Extrinsic Curvature Excess:**
   Whenever $c_2^2 + s_2^2 = 1$,
   `((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (4 * r₂ * c₂) ^ 2 + (4 * r₂ * s₂) ^ 2) - ((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (2 * r₂ * c₂) ^ 2 + (2 * r₂ * s₂) ^ 2) = 12 * r₂ ^ 2`.
-/
theorem peirce_helper_excursion_attribute_surprisal_and_kms_toeplitz_laplacian
    {B : Type*} [Ring B] {P : B} (hP : P * P = P)
    (S M : B)
    (hSP : InfoGeometry.OperatorAlgebra.PeirceSpine.comm S P = 0)
    (hSM : InfoGeometry.OperatorAlgebra.PeirceSpine.comm S M = 0)
    (s x r₁ r₂ c₁ s₁ c₂ s₂ : ℝ)
    (hs_lower : -1 < s) (hs_upper : s < 1) (hx : x * x = 1)
    (hC2 : c₂ ^ 2 + s₂ ^ 2 = 1)
    {R : Type*} [CommRing R] (ρ : R) :
    (P * (M * M) * P = (P * M * P) * (P * M * P) + conePlus P M * coneMinus P M ∧
     (P * M * P = 0 → P * (M * M) * P = conePlus P M * coneMinus P M) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm S (conePlus P M) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm S (coneMinus P M) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm S (conePlus P M * coneMinus P M) = 0) ∧
    (Real.log (1 + s * x) =
       (Real.log (1 + s) + Real.log (1 - s)) / 2 +
         ((Real.log (1 + s) - Real.log (1 - s)) / 2) * x) ∧
    (symmetricToeplitz3 1 ρ (ρ ^ 2) * kmsTridiagonalLaplacian3 ρ =
       (1 - ρ ^ 2) • (1 : Mat3 R) ∧
     kmsTridiagonalLaplacian3 ρ * symmetricToeplitz3 1 ρ (ρ ^ 2) =
       (1 - ρ ^ 2) • (1 : Mat3 R) ∧
     kmsTridiagonalLaplacian3 ρ 0 2 = 0 ∧
     kmsTridiagonalLaplacian3 ρ 2 0 = 0 ∧
     kmsTridiagonalLaplacian3 ρ 1 1 - kmsTridiagonalLaplacian3 ρ 0 0 = ρ ^ 2) ∧
    (((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (4 * r₂ * c₂) ^ 2 + (4 * r₂ * s₂) ^ 2) -
       ((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (2 * r₂ * c₂) ^ 2 + (2 * r₂ * s₂) ^ 2) =
       12 * r₂ ^ 2) := by
  have hExcursion : P * (M * M) * P = (P * M * P) * (P * M * P) + conePlus P M * coneMinus P M := by
    dsimp [conePlus, coneMinus]
    peirce_nf hP
  have hDel : P * M * P = 0 → P * (M * M) * P = conePlus P M * coneMinus P M := by
    intro hZero
    rw [hExcursion, hZero, zero_mul, zero_add]
  have hSP_eq : S * P = P * S := sub_eq_zero.mp hSP
  have hSM_eq : S * M = M * S := sub_eq_zero.mp hSM
  have hS1P : (1 - P) * S = S * (1 - P) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, ← hSP_eq]
  have hCommPlus : InfoGeometry.OperatorAlgebra.PeirceSpine.comm S (conePlus P M) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, conePlus]
    calc
      S * (P * M * (1 - P)) - P * M * (1 - P) * S =
          ((S * P) * M) * (1 - P) - (P * M) * ((1 - P) * S) := by noncomm_ring
      _ = ((P * S) * M) * (1 - P) - (P * M) * (S * (1 - P)) := by rw [hSP_eq, hS1P]
      _ = (P * (S * M)) * (1 - P) - (P * M) * (S * (1 - P)) := by rw [mul_assoc P S M]
      _ = (P * (M * S)) * (1 - P) - (P * M) * (S * (1 - P)) := by rw [hSM_eq]
      _ = 0 := by noncomm_ring
  have hCommMinus : InfoGeometry.OperatorAlgebra.PeirceSpine.comm S (coneMinus P M) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, coneMinus]
    calc
      S * ((1 - P) * M * P) - (1 - P) * M * P * S =
          ((S * (1 - P)) * M) * P - ((1 - P) * M) * (P * S) := by noncomm_ring
      _ = (((1 - P) * S) * M) * P - ((1 - P) * M) * (S * P) := by rw [← hS1P, hSP_eq]
      _ = ((1 - P) * (S * M)) * P - ((1 - P) * M) * (S * P) := by rw [mul_assoc (1 - P) S M]
      _ = ((1 - P) * (M * S)) * P - ((1 - P) * M) * (S * P) := by rw [hSM_eq]
      _ = 0 := by noncomm_ring
  have hPlusEq : S * conePlus P M = conePlus P M * S := sub_eq_zero.mp hCommPlus
  have hMinusEq : S * coneMinus P M = coneMinus P M * S := sub_eq_zero.mp hCommMinus
  have hCommProd :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm S (conePlus P M * coneMinus P M) = 0 := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    calc
      S * (conePlus P M * coneMinus P M) - conePlus P M * coneMinus P M * S =
          (S * conePlus P M) * coneMinus P M - conePlus P M * (coneMinus P M * S) := by
        rw [← mul_assoc, ← mul_assoc]
      _ = (conePlus P M * S) * coneMinus P M - conePlus P M * (S * coneMinus P M) := by
        rw [hPlusEq, hMinusEq]
      _ = 0 := by rw [mul_assoc, sub_self]
  have hKMS_right :
      symmetricToeplitz3 1 ρ (ρ ^ 2) * kmsTridiagonalLaplacian3 ρ =
        (1 - ρ ^ 2) • (1 : Mat3 R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetricToeplitz3, kmsTridiagonalLaplacian3, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring
  have hKMS_left :
      kmsTridiagonalLaplacian3 ρ * symmetricToeplitz3 1 ρ (ρ ^ 2) =
        (1 - ρ ^ 2) • (1 : Mat3 R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetricToeplitz3, kmsTridiagonalLaplacian3, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring
  have hKMS_02 : kmsTridiagonalLaplacian3 ρ 0 2 = 0 := by
    simp [kmsTridiagonalLaplacian3]
  have hKMS_20 : kmsTridiagonalLaplacian3 ρ 2 0 = 0 := by
    simp [kmsTridiagonalLaplacian3]
  have hKMS_defect : kmsTridiagonalLaplacian3 ρ 1 1 - kmsTridiagonalLaplacian3 ρ 0 0 = ρ ^ 2 := by
    simp [kmsTridiagonalLaplacian3]
  have hLissajous :
      ((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (4 * r₂ * c₂) ^ 2 + (4 * r₂ * s₂) ^ 2) -
        ((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (2 * r₂ * c₂) ^ 2 + (2 * r₂ * s₂) ^ 2) =
        12 * r₂ ^ 2 := by
    calc
      ((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (4 * r₂ * c₂) ^ 2 + (4 * r₂ * s₂) ^ 2) -
          ((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (2 * r₂ * c₂) ^ 2 + (2 * r₂ * s₂) ^ 2) =
          12 * r₂ ^ 2 * (c₂ ^ 2 + s₂ ^ 2) := by ring
      _ = 12 * r₂ ^ 2 * 1 := by rw [hC2]
      _ = 12 * r₂ ^ 2 := mul_one (12 * r₂ ^ 2)
  exact ⟨⟨hExcursion, hDel, hCommPlus, hCommMinus, hCommProd⟩,
         (binary_attribute_log_affine s x hs_lower hs_upper hx).2,
         ⟨hKMS_right, hKMS_left, hKMS_02, hKMS_20, hKMS_defect⟩,
         hLissajous⟩

-- ============================================================================
-- SECTION 9: FINITE RESIDUE ARITHMETIC & CONDITIONAL PEIRCE COMPRESSION IDENTITIES
-- ============================================================================

/--
**Theorem 8F (`z12_residue_arithmetic_and_character_argument`):**
This theorem proves the fixed natural-number calculation
`Nat.totient 1 + Nat.totient 2 + Nat.totient 3 + Nat.totient 4 + Nat.totient 6 + Nat.totient 12 = 12`,
`Nat.totient 12 = 4`, and listed products modulo 12. It also proves
`ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x))` by reassociating and commuting
multiplication in `ZMod N`. It does not construct a cyclotomic-field automorphism or prove an
orbit action.
-/
theorem z12_residue_arithmetic_and_character_argument
    {N : ℕ} [NeZero N] (p k x : ZMod N) :
    (Nat.totient 1 + Nat.totient 2 + Nat.totient 3 +
      Nat.totient 4 + Nat.totient 6 + Nat.totient 12 = 12 ∧
     Nat.totient 12 = 4 ∧
     (1 * 1) % 12 = 1 ∧ (5 * 5) % 12 = 1 ∧ (7 * 7) % 12 = 1 ∧ (11 * 11) % 12 = 1 ∧
     (5 * 1) % 12 = 5 ∧ (5 * 5) % 12 = 1 ∧
     (5 * 3) % 12 = 3 ∧ (5 * 6) % 12 = 6) ∧
    ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x)) := by
  refine ⟨by decide, ?_⟩
  congr 1
  ring

/--
The 2D Peter–Weyl rotation rotor `peirceRotor2D P X Y c s = c + s * genJ P X Y`
in the `(1, J₁)` plane of `[Ring B]`, where `J₁ = genJ P X Y = conePlus P X - coneMinus P Y`.
-/
def peirceRotor2D {B : Type*} [Ring B] (P X Y c s : B) : B :=
  c + s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y

/--
**Theorem 8G (`peirce_rotor_conjugation_and_commutator`):**
For an idempotent `P` in an associative ring and coefficients `c,s` commuting with `invS P`,
the theorem proves conjugation of `c + s * genJ P X Y` by `invS P` changes `s` to `-s`, and
computes the commutator as `s * (genPhi P X Y + genPhi P X Y)`. This is a conditional Peirce
identity, not a `D_N` representation or a Peter–Weyl decomposition.
-/
theorem peirce_rotor_conjugation_and_commutator
    {B : Type*} [Ring B] (P X Y c s : B) (hP : P * P = P)
    (hc_S : InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * c =
      c * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
    (hs_S : InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * s =
      s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
        peirceRotor2D P X Y c s *
        InfoGeometry.OperatorAlgebra.PeirceSpine.invS P =
      peirceRotor2D P X Y c (-s) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
        (peirceRotor2D P X Y c s) =
      s * (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y +
           InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y) := by
  have hS2 :
      InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
        InfoGeometry.OperatorAlgebra.PeirceSpine.invS P = 1 := by
    peirce_nf hP
  have hSJ :
      InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
        InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y =
        InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y := by
    peirce_nf hP
  have hJS :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
        InfoGeometry.OperatorAlgebra.PeirceSpine.invS P =
        -InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y := by
    peirce_nf hP
  have hSJS :
      InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
        InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
        InfoGeometry.OperatorAlgebra.PeirceSpine.invS P =
        -InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y := by
    peirce_nf hP
  refine ⟨?_, ?_⟩
  · dsimp [peirceRotor2D]
    calc
      InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
          (c + s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) *
          InfoGeometry.OperatorAlgebra.PeirceSpine.invS P =
          (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * c) *
            InfoGeometry.OperatorAlgebra.PeirceSpine.invS P +
          (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * s) *
            InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
            InfoGeometry.OperatorAlgebra.PeirceSpine.invS P := by
        simp only [mul_add, add_mul, mul_assoc]
      _ = c * (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
            InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) +
          s * (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
            InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
            InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) := by
        rw [hc_S, hs_S]
        simp only [mul_assoc]
      _ = c + (-s) * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y := by
        rw [hS2, hSJS, mul_one, mul_neg, neg_mul]
  · dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, peirceRotor2D]
    calc
      InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
          (c + s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) -
          (c + s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) *
          InfoGeometry.OperatorAlgebra.PeirceSpine.invS P =
          (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * c -
            c * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) +
          ((InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * s) *
            InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y -
            s * (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
              InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)) := by
        simp only [mul_add, add_mul, mul_assoc]
        abel
      _ = 0 + (s * (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
            InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) -
            s * (-InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y)) := by
        rw [hc_S, sub_self, hs_S, hJS]
        simp only [mul_assoc]
      _ = s * (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y +
            InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y) := by
        rw [hSJ, mul_neg, sub_neg_eq_add, ← mul_add, zero_add]

/--
An algebraic expression `surprisalNormalFormOp u_bar delta_u σ = u_bar + delta_u * σ`.
Here these parameters are arbitrary ring elements; this definition does not construct logarithms,
hyperbolic functions, or an attribute probability model.
-/
def surprisalNormalFormOp {B : Type*} [Ring B] (u_bar delta_u σ : B) : B :=
  u_bar + delta_u * σ

/--
**Theorem 8H (`conditional_involution_compression_variance`):**
Let `P_H` be an idempotent in `[Ring B]`, and let `L = surprisalNormalFormOp u_bar delta_u σ`
with `σ * σ = 1`. Under the stated coefficient-commutation assumptions:
1. **Macro-Attribute (`h_macro : P_H * σ * P_H = σ * P_H`):**
   The linearized surprisal normal form descends intact at 1st order:
   `P_H * L * P_H = L * P_H`.
2. **Micro-Compression (`h_micro : P_H * σ * P_H = 0`):**
   - At **1st order**, `P_H * L * P_H = u_bar * P_H`.
   - At **2nd order**, the compression defect equals the squared coefficient times the idempotent:
     `P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H`.
This is an equality only. Nonvanishing and a quotient-variance interpretation require additional
hypotheses and a concrete quotient construction.
-/
theorem conditional_involution_compression_variance
    {B : Type*} [Ring B] (P_H u_bar delta_u σ : B)
    (hPH : P_H * P_H = P_H)
    (hσ2 : σ * σ = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_σ : u_bar * σ = σ * u_bar)
    (hd_σ : delta_u * σ = σ * delta_u) :
    let L := surprisalNormalFormOp u_bar delta_u σ
    (P_H * σ * P_H = σ * P_H → P_H * L * P_H = L * P_H) ∧
    (P_H * σ * P_H = 0 →
      P_H * L * P_H = u_bar * P_H ∧
      P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H) := by
  refine ⟨?_, ?_⟩
  · intro h_macro
    dsimp [surprisalNormalFormOp]
    calc
      P_H * (u_bar + delta_u * σ) * P_H
        = (P_H * u_bar) * P_H + (P_H * delta_u) * σ * P_H := by
          simp only [mul_add, add_mul, mul_assoc]
      _ = u_bar * (P_H * P_H) + delta_u * (P_H * σ * P_H) := by
          rw [hu_P, hd_P]
          simp only [mul_assoc]
      _ = (u_bar + delta_u * σ) * P_H := by
          rw [hPH, h_macro, add_mul, mul_assoc]
  · intro h_micro
    have h1 : P_H * surprisalNormalFormOp u_bar delta_u σ * P_H = u_bar * P_H := by
      dsimp [surprisalNormalFormOp]
      calc
        P_H * (u_bar + delta_u * σ) * P_H
          = (P_H * u_bar) * P_H + (P_H * delta_u) * σ * P_H := by
            simp only [mul_add, add_mul, mul_assoc]
        _ = u_bar * (P_H * P_H) + delta_u * (P_H * σ * P_H) := by
            rw [hu_P, hd_P]
            simp only [mul_assoc]
        _ = u_bar * P_H := by
            rw [hPH, h_micro, mul_zero, add_zero]
    refine ⟨h1, ?_⟩
    have hL2 :
        surprisalNormalFormOp u_bar delta_u σ * surprisalNormalFormOp u_bar delta_u σ =
          (u_bar * u_bar + delta_u * delta_u) + (u_bar * delta_u + delta_u * u_bar) * σ := by
      dsimp [surprisalNormalFormOp]
      have hdσ2 : delta_u * σ * (delta_u * σ) = delta_u * delta_u := by
        calc
          delta_u * σ * (delta_u * σ) = delta_u * (σ * delta_u) * σ := by simp only [mul_assoc]
          _ = delta_u * delta_u * (σ * σ) := by rw [← hd_σ]; simp only [mul_assoc]
          _ = delta_u * delta_u := by rw [hσ2, mul_one]
      have Cross :
          u_bar * (delta_u * σ) + delta_u * σ * u_bar =
            (u_bar * delta_u + delta_u * u_bar) * σ := by
        calc
          u_bar * (delta_u * σ) + delta_u * σ * u_bar
            = u_bar * delta_u * σ + delta_u * (σ * u_bar) := by simp only [mul_assoc]
          _ = (u_bar * delta_u + delta_u * u_bar) * σ := by
              rw [← hu_σ, add_mul]
              simp only [mul_assoc]
      calc
        (u_bar + delta_u * σ) * (u_bar + delta_u * σ)
          = u_bar * u_bar + (u_bar * (delta_u * σ) + delta_u * σ * u_bar) +
              delta_u * σ * (delta_u * σ) := by
              simp only [add_mul, mul_add, mul_assoc]
              abel
        _ = (u_bar * u_bar + delta_u * delta_u) + (u_bar * delta_u + delta_u * u_bar) * σ := by
            rw [Cross, hdσ2]
            abel
    have h_cross_zero : P_H * ((u_bar * delta_u + delta_u * u_bar) * σ) * P_H = 0 := by
      calc
        P_H * ((u_bar * delta_u + delta_u * u_bar) * σ) * P_H
          = (P_H * u_bar * delta_u + P_H * delta_u * u_bar) * σ * P_H := by
              simp only [mul_add, add_mul, mul_assoc]
        _ = (u_bar * P_H * delta_u + delta_u * P_H * u_bar) * σ * P_H := by
              rw [hu_P, hd_P]
        _ = (u_bar * (P_H * delta_u) + delta_u * (P_H * u_bar)) * σ * P_H := by
              simp only [mul_assoc]
        _ = (u_bar * delta_u + delta_u * u_bar) * (P_H * σ * P_H) := by
              rw [hd_P, hu_P]
              simp only [add_mul, mul_assoc]
        _ = 0 := by rw [h_micro, mul_zero]
    rw [h1, hL2]
    calc
      P_H * ((u_bar * u_bar + delta_u * delta_u) + (u_bar * delta_u + delta_u * u_bar) * σ) * P_H -
          u_bar * P_H * (u_bar * P_H)
        = P_H * (u_bar * u_bar + delta_u * delta_u) * P_H +
            P_H * ((u_bar * delta_u + delta_u * u_bar) * σ) * P_H -
            u_bar * (P_H * u_bar) * P_H := by
            simp only [mul_add, add_mul, mul_assoc]
      _ = (u_bar * u_bar + delta_u * delta_u) * (P_H * P_H) + 0 -
            u_bar * u_bar * (P_H * P_H) := by
          rw [h_cross_zero, hu_P]
          have h_u2 : P_H * (u_bar * u_bar) = u_bar * u_bar * P_H := by
            calc
              P_H * (u_bar * u_bar) = (P_H * u_bar) * u_bar := by rw [← mul_assoc]
              _ = (u_bar * P_H) * u_bar := by rw [hu_P]
              _ = u_bar * (P_H * u_bar) := by rw [mul_assoc]
              _ = u_bar * (u_bar * P_H) := by rw [hu_P]
              _ = u_bar * u_bar * P_H := by rw [← mul_assoc]
          have h_d2 : P_H * (delta_u * delta_u) = delta_u * delta_u * P_H := by
            calc
              P_H * (delta_u * delta_u) = (P_H * delta_u) * delta_u := by rw [← mul_assoc]
              _ = (delta_u * P_H) * delta_u := by rw [hd_P]
              _ = delta_u * (P_H * delta_u) := by rw [mul_assoc]
              _ = delta_u * (delta_u * P_H) := by rw [hd_P]
              _ = delta_u * delta_u * P_H := by rw [← mul_assoc]
          have h_comm_sum :
              P_H * (u_bar * u_bar + delta_u * delta_u) =
                (u_bar * u_bar + delta_u * delta_u) * P_H := by
            rw [mul_add, h_u2, h_d2, add_mul]
          rw [h_comm_sum]
          simp only [mul_assoc]
      _ = (delta_u * delta_u) * P_H := by
          rw [hPH, add_zero, add_mul]
          abel

/--
**Theorem 8I (`finite_arithmetic_peirce_and_compression_conjunction`):**
This theorem returns a conjunction of the preceding finite residue calculation, conditional Peirce
rotor identities, and conditional compression identities. It introduces no map between the
`ZMod N` character, Peirce ring, and compression operator carriers.
-/
theorem finite_arithmetic_peirce_and_compression_conjunction
    {N : ℕ} [NeZero N] (p k x : ZMod N)
    {B : Type*} [Ring B] (P X Y c s : B) (hP : P * P = P)
    (hc_S : InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * c =
      c * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
    (hs_S : InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * s =
      s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
    (P_H u_bar delta_u σ : B)
    (hPH : P_H * P_H = P_H)
    (hσ2 : σ * σ = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_σ : u_bar * σ = σ * u_bar)
    (hd_σ : delta_u * σ = σ * delta_u) :
    ((Nat.totient 1 + Nat.totient 2 + Nat.totient 3 +
       Nat.totient 4 + Nat.totient 6 + Nat.totient 12 = 12 ∧
      Nat.totient 12 = 4 ∧
      (1 * 1) % 12 = 1 ∧ (5 * 5) % 12 = 1 ∧ (7 * 7) % 12 = 1 ∧ (11 * 11) % 12 = 1 ∧
      (5 * 1) % 12 = 5 ∧ (5 * 5) % 12 = 1 ∧
      (5 * 3) % 12 = 3 ∧ (5 * 6) % 12 = 6) ∧
     ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x))) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
        peirceRotor2D P X Y c s *
        InfoGeometry.OperatorAlgebra.PeirceSpine.invS P =
      peirceRotor2D P X Y c (-s) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
        (peirceRotor2D P X Y c s) =
      s * (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y +
           InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P X Y)) ∧
    (let L := surprisalNormalFormOp u_bar delta_u σ
     (P_H * σ * P_H = σ * P_H → P_H * L * P_H = L * P_H) ∧
     (P_H * σ * P_H = 0 →
       P_H * L * P_H = u_bar * P_H ∧
       P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H)) := by
  have hGalois := z12_residue_arithmetic_and_character_argument p k x
  have hDihedral := peirce_rotor_conjugation_and_commutator P X Y c s hP hc_S hs_S
  have hQuotient :=
    conditional_involution_compression_variance
      P_H u_bar delta_u σ hPH hσ2 hu_P hd_P hu_σ hd_σ
  exact ⟨hGalois, hDihedral, hQuotient⟩

/--
Computable Möbius values on divisors of `12` and `24` (`1` on `1, 6, 10`, `-1` on primes
`2, 3, 5, 7, 11`, and `0` on squareful numbers `4, 8, 9, 12, 24`).
-/
def moebiusDivisor24 : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 0
  | 5 => -1
  | 6 => 1
  | 7 => -1
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => -1
  | _ => 0

/--
Computable integer divisor sum `ramanujanSum12 d x = ∑_{m | gcd(d, x)} m · μ(d / m) ∈ ℤ`
over the divisor list `[1, 2, 3, 4, 6, 12]`.
-/
def ramanujanSum12 (d x : ℕ) : ℤ :=
  (([1, 2, 3, 4, 6, 12] : List ℕ).filter (fun m => decide (m ∣ Nat.gcd d x))).foldl
    (fun acc (m : ℕ) => acc + (m : ℤ) * moebiusDivisor24 (d / m)) 0

/--
Computable integer divisor sum `ramanujanSum24 d x = ∑_{m | gcd(d, x)} m · μ(d / m) ∈ ℤ`
over the divisor list `[1, 2, 3, 4, 6, 8, 12, 24]`.
-/
def ramanujanSum24 (d x : ℕ) : ℤ :=
  (([1, 2, 3, 4, 6, 8, 12, 24] : List ℕ).filter (fun m => decide (m ∣ Nat.gcd d x))).foldl
    (fun acc (m : ℕ) => acc + (m : ℤ) * moebiusDivisor24 (d / m)) 0

/--
**Theorem 8J (`z12_z24_divisor_ramanujan_sum_and_unit_residue_squares`):**
This theorem proves finite natural-number and integer calculations for `N = 12` and `N = 24`:
1. `Nat.totient 1 + Nat.totient 2 + Nat.totient 3 + Nat.totient 4 + Nat.totient 6 + Nat.totient 8 + Nat.totient 12 + Nat.totient 24 = 24` and `Nat.totient 24 = 8`.
2. Each of the eight coprime residues `p ∈ {1, 5, 7, 11, 13, 17, 19, 23}` satisfies `(p * p) % 24 = 1`.
3. For every `x : Fin 12`, summing `ramanujanSum12 d x.val` over `d ∈ {1, 2, 3, 4, 6, 12}` equals `if x.val = 0 then 12 else 0`.
4. For every `x : Fin 24`, summing `ramanujanSum24 d x.val` over `d ∈ {1, 2, 3, 4, 6, 8, 12, 24}` equals `if x.val = 0 then 24 else 0`.
It does not construct a cyclotomic Galois group or complex root-of-unity sum.
-/
theorem z12_z24_divisor_ramanujan_sum_and_unit_residue_squares :
    (Nat.totient 1 + Nat.totient 2 + Nat.totient 3 + Nat.totient 4 +
      Nat.totient 6 + Nat.totient 8 + Nat.totient 12 + Nat.totient 24 = 24 ∧
     Nat.totient 24 = 8 ∧
     (1 * 1) % 24 = 1 ∧ (5 * 5) % 24 = 1 ∧ (7 * 7) % 24 = 1 ∧ (11 * 11) % 24 = 1 ∧
     (13 * 13) % 24 = 1 ∧ (17 * 17) % 24 = 1 ∧ (19 * 19) % 24 = 1 ∧ (23 * 23) % 24 = 1) ∧
    (ramanujanSum12 12 0 = 4 ∧ ramanujanSum12 12 1 = 0 ∧ ramanujanSum12 12 2 = 2 ∧
     ramanujanSum12 12 3 = 0 ∧ ramanujanSum12 12 4 = -2 ∧ ramanujanSum12 12 6 = -4 ∧
     ramanujanSum24 24 0 = 8 ∧ ramanujanSum24 24 4 = 4 ∧
     ramanujanSum24 24 8 = -4 ∧ ramanujanSum24 24 12 = -8) ∧
    (∀ x : Fin 12,
      ramanujanSum12 1 x.val + ramanujanSum12 2 x.val + ramanujanSum12 3 x.val +
      ramanujanSum12 4 x.val + ramanujanSum12 6 x.val + ramanujanSum12 12 x.val =
        if x.val = 0 then 12 else 0) ∧
    (∀ x : Fin 24,
      ramanujanSum24 1 x.val + ramanujanSum24 2 x.val + ramanujanSum24 3 x.val +
      ramanujanSum24 4 x.val + ramanujanSum24 6 x.val + ramanujanSum24 8 x.val +
      ramanujanSum24 12 x.val + ramanujanSum24 24 x.val =
        if x.val = 0 then 24 else 0) := by
  have hTot : Nat.totient 24 = 8 := by decide
  refine ⟨⟨by decide, hTot, by decide⟩, by decide, by decide, by decide⟩

/--
**Theorem 8K (`peirce_reflected_rotor_norm_and_off_diagonal_compression_defect`):**
Under explicit idempotence and commutation hypotheses in `[Ring B]`:
1. Multiplying `peirceRotor2D P X Y c s * invS P` on the right by `invS P` recovers `peirceRotor2D P X Y c s`.
2. Both `peirceRotor2D P X Y c s * peirceRotor2D P X Y c (-s)` and the square of the reflected
   element `(peirceRotor2D P X Y c s * invS P) * (peirceRotor2D P X Y c s * invS P)` equal
   `c * c - s * s * (genJ P X Y * genJ P X Y)`.
3. For any idempotent `P_H * P_H = P_H`, the off-diagonal Peirce generator `genPhi P_H X Y`
   satisfies `P_H * genPhi P_H X Y * P_H = 0`; when `genPhi P_H X Y * genPhi P_H X Y = 1` and
   `u_bar, delta_u` commute as stated, `L = surprisalNormalFormOp u_bar delta_u (genPhi P_H X Y)`
   satisfies `P_H * L * P_H = u_bar * P_H` and
   `P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H`.
-/
theorem peirce_reflected_rotor_norm_and_off_diagonal_compression_defect
    {B : Type*} [Ring B] (P X Y c s : B) (hP : P * P = P)
    (hc_S : InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * c =
      c * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
    (hs_S : InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * s =
      s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
    (hcs : c * s = s * c)
    (hc_J : c * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y * c)
    (hs_J : s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y * s)
    (P_H u_bar delta_u : B)
    (hPH : P_H * P_H = P_H)
    (hPhi2 : InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y *
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_Phi : u_bar * InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y * u_bar)
    (hd_Phi : delta_u * InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y * delta_u) :
    ((peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.invS P =
      peirceRotor2D P X Y c s ∧
     peirceRotor2D P X Y c s * peirceRotor2D P X Y c (-s) =
      c * c - s * s *
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
         InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) ∧
     (peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) *
        (peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) =
      c * c - s * s *
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
         InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y)) ∧
    (let L := surprisalNormalFormOp u_bar delta_u
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y)
     P_H * InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y * P_H = 0 ∧
     P_H * L * P_H = u_bar * P_H ∧
     P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) =
      (delta_u * delta_u) * P_H) := by
  have hS2 :
      InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
        InfoGeometry.OperatorAlgebra.PeirceSpine.invS P = 1 := by
    peirce_nf hP
  have htwo :
      (peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.invS P =
      peirceRotor2D P X Y c s := by
    rw [mul_assoc, hS2, mul_one]
  have hnorm :
      peirceRotor2D P X Y c s * peirceRotor2D P X Y c (-s) =
        c * c - s * s *
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
           InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) := by
    dsimp [peirceRotor2D]
    have hsJ2 :
        s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
          (s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) =
        s * s *
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
           InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) := by
      calc
        s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
            (s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y)
          = s * (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y * s) *
              InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y := by
              simp only [mul_assoc]
        _ = s * s *
              (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
               InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) := by
            rw [← hs_J]
            simp only [mul_assoc]
    have hcross :
        s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y * c -
          c * (s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) = 0 := by
      calc
        s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y * c -
            c * (s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y)
          = s * (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y * c) -
              (c * s) * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y := by
              simp only [mul_assoc]
        _ = (s * c) * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y -
              (s * c) * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y := by
            rw [← hc_J, hcs]
            simp only [mul_assoc]
        _ = 0 := sub_self _
    calc
      (c + s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) *
          (c + (-s) * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y)
        = c * c +
            (s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y * c -
              c * (s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y)) -
            s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
              (s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) := by
            simp only [add_mul, mul_add, neg_mul, mul_neg, mul_assoc]
            abel
      _ = c * c - s * s *
            (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
             InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) := by
          rw [hcross, add_zero, hsJ2]
  have hConj := (peirce_rotor_conjugation_and_commutator P X Y c s hP hc_S hs_S).1
  have hreflSq :
      (peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) *
        (peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) =
      c * c - s * s *
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
         InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) := by
    calc
      (peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) *
          (peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
        = peirceRotor2D P X Y c s *
            (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
              peirceRotor2D P X Y c s *
              InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) := by
            simp only [mul_assoc]
      _ = peirceRotor2D P X Y c s * peirceRotor2D P X Y c (-s) := by rw [hConj]
      _ = c * c - s * s *
            (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
             InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) := hnorm
  have hMicro :
      P_H * InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y * P_H = 0 := by
    peirce_nf hPH
  have hMain :=
    (conditional_involution_compression_variance
      P_H u_bar delta_u (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y)
      hPH hPhi2 hu_P hd_P hu_Phi hd_Phi).2 hMicro
  exact ⟨⟨htwo, hnorm, hreflSq⟩, ⟨hMicro, hMain.1, hMain.2⟩⟩

/--
**Theorem 8L (`cl11_tensor_stage_factorization_and_peirce_compression_synthesis`):**
Combines the finite binary matrix stage tensor factorization from
`InfoGeometry.Clifford.Cl11TensorStageFactorization` (`stageTensorFactorization`,
`stageTensorFactorization_stageEmbed_tmul`, `factorizedStageToLimit_stageEmbed`) with the
finite Ramanujan sum calculations (`z12_z24_divisor_ramanujan_sum_and_unit_residue_squares`) and
conditional Peirce rotor and compression identities
(`peirce_reflected_rotor_norm_and_off_diagonal_compression_defect`). This theorem is a conjunction
of those finite-stage and conditional results and does not establish an infinite-factor
classification or a carrier map between the matrix-tower and ring parameters.
-/
theorem cl11_tensor_stage_factorization_and_peirce_compression_synthesis
    (n m : ℕ)
    (A_st : InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (B_st : InfoGeometry.Clifford.Cl11TensorTower.MatStage m)
    (z_st : TensorProduct ℝ
      (InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
      (InfoGeometry.Clifford.Cl11TensorTower.MatStage m))
    {B : Type*} [Ring B] (P X Y c s : B) (hP : P * P = P)
    (hc_S : InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * c =
      c * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
    (hs_S : InfoGeometry.OperatorAlgebra.PeirceSpine.invS P * s =
      s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
    (hcs : c * s = s * c)
    (hc_J : c * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y * c)
    (hs_J : s * InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y * s)
    (P_H u_bar delta_u : B)
    (hPH : P_H * P_H = P_H)
    (hPhi2 : InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y *
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_Phi : u_bar * InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y * u_bar)
    (hd_Phi : delta_u * InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y * delta_u) :
    (InfoGeometry.Clifford.Cl11TensorStageFactorization.stageTensorFactorization n (m + 1)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (n + m)
          ((InfoGeometry.Clifford.Cl11TensorStageFactorization.stageTensorFactorization n m).symm
            (TensorProduct.tmul ℝ A_st B_st))) =
      TensorProduct.tmul ℝ A_st
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed m B_st) ∧
     InfoGeometry.Clifford.Cl11TensorStageFactorization.factorizedStageToLimit n (m + 1)
        (TensorProduct.map
          (LinearMap.id :
            InfoGeometry.Clifford.Cl11TensorTower.MatStage n →ₗ[ℝ]
              InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
          (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed m).toLinearMap z_st) =
      InfoGeometry.Clifford.Cl11TensorStageFactorization.factorizedStageToLimit n m z_st) ∧
    ((∀ x : Fin 12,
        ramanujanSum12 1 x.val + ramanujanSum12 2 x.val + ramanujanSum12 3 x.val +
        ramanujanSum12 4 x.val + ramanujanSum12 6 x.val + ramanujanSum12 12 x.val =
          if x.val = 0 then 12 else 0) ∧
     (∀ x : Fin 24,
        ramanujanSum24 1 x.val + ramanujanSum24 2 x.val + ramanujanSum24 3 x.val +
        ramanujanSum24 4 x.val + ramanujanSum24 6 x.val + ramanujanSum24 8 x.val +
        ramanujanSum24 12 x.val + ramanujanSum24 24 x.val =
          if x.val = 0 then 24 else 0)) ∧
    (((peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.invS P =
      peirceRotor2D P X Y c s ∧
     peirceRotor2D P X Y c s * peirceRotor2D P X Y c (-s) =
      c * c - s * s *
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
         InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y) ∧
     (peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) *
        (peirceRotor2D P X Y c s * InfoGeometry.OperatorAlgebra.PeirceSpine.invS P) =
      c * c - s * s *
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y *
         InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P X Y)) ∧
    (let L := surprisalNormalFormOp u_bar delta_u
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y)
     P_H * InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P_H X Y * P_H = 0 ∧
     P_H * L * P_H = u_bar * P_H ∧
     P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) =
      (delta_u * delta_u) * P_H)) := by
  have hStage :=
    InfoGeometry.Clifford.Cl11TensorStageFactorization.stageTensorFactorization_stageEmbed_tmul
      n m A_st B_st
  have hLimit :=
    InfoGeometry.Clifford.Cl11TensorStageFactorization.factorizedStageToLimit_stageEmbed
      n m z_st
  have hRam := z12_z24_divisor_ramanujan_sum_and_unit_residue_squares
  have hPeirce :=
    peirce_reflected_rotor_norm_and_off_diagonal_compression_defect
      P X Y c s hP hc_S hs_S hcs hc_J hs_J P_H u_bar delta_u hPH hPhi2 hu_P hd_P hu_Phi hd_Phi
  exact ⟨⟨hStage, hLimit⟩, ⟨hRam.2.2.1, hRam.2.2.2⟩, hPeirce⟩

/--
**Theorem 8M (`wigner_clebsch_gordan_mat3_zorn_cross_and_dressed_peirce_bott_synthesis`):**
Combines the finite arithmetic and Catalan identities
(`CliffordBottKTheoryWignerS4Poset.s4_wedderburn_artin_trees_and_adams_j_mod24_lock`,
`CliffordBottKTheoryWignerS4Poset.adams_j_homomorphism_all_z24_units_divisibility`), the
division-free four-channel decomposition of `3 × 3` matrices and 3D Zorn cross-product identity
(`CliffordBottKTheoryWignerS4Poset.Mat3.wigner_clebsch_gordan_s4_four_channel_decomposition`,
`CliffordBottKTheoryWignerS4Poset.Mat3.kb5_antisym_channel_zorn_cross_product_bridge`), and the
conditional dressed Peirce projector idempotence, diagonal commutator identity, ring homomorphism
preservation, and 4-scale `PeirceIndex` cardinality scaling
(`CliffordBottKTheoryWignerS4Poset.ko_theory_pmi_bruhat_projector_colimit_stability`). This theorem
is a conjunction of those finite-stage and conditional results and does not establish a continuous
homotopy-group construction of `π₃^s` or a carrier map between the matrix and ring parameters.
-/
theorem wigner_clebsch_gordan_mat3_zorn_cross_and_dressed_peirce_bott_synthesis
    {K : Type*} [CommRing K]
    (M_cg : CliffordBottKTheoryWignerS4Poset.Mat3 K) (u_vec v_vec : Fin 3 → K)
    {B B' : Type*} [Ring B] [Ring B']
    (P M_op : B) (hP : P * P = P) (ι : B →+* B') (n : ℕ) :
    ((1 ^ 2 + 1 ^ 2 + 2 ^ 2) + (3 ^ 2 + 3 ^ 2) = 24 ∧
     4 ^ (4 - 2) = 16 ∧
     24 - 4 ^ (4 - 2) = Nat.totient 24 ∧
     CliffordBottKTheoryWignerS4Poset.catalanNum 3 = 5 ∧
     CliffordBottKTheoryWignerS4Poset.catalanNum 4 = 14 ∧
     Nat.gcd (5 ^ 2 - 1) (7 ^ 2 - 1) = 24 ∧
     (∀ k : Fin 24, Nat.Coprime k.val 24 → (k.val * k.val - 1) % 24 = 0)) ∧
    ((CliffordBottKTheoryWignerS4Poset.Mat3.smul 6 M_cg =
        CliffordBottKTheoryWignerS4Poset.Mat3.cgChan1_Triv M_cg +
        CliffordBottKTheoryWignerS4Poset.Mat3.cgChan2_Quadrupole M_cg +
        CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_SymOff M_cg +
        CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_AntisymVort M_cg ∧
      CliffordBottKTheoryWignerS4Poset.Mat3.tr
        (CliffordBottKTheoryWignerS4Poset.Mat3.cgChan2_Quadrupole M_cg) = 0 ∧
      CliffordBottKTheoryWignerS4Poset.Mat3.tr
        (CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_SymOff M_cg) = 0 ∧
      CliffordBottKTheoryWignerS4Poset.Mat3.tr
        (CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_AntisymVort M_cg) = 0 ∧
      CliffordBottKTheoryWignerS4Poset.Mat3.transpose
        (CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_SymOff M_cg) =
        CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_SymOff M_cg ∧
      CliffordBottKTheoryWignerS4Poset.Mat3.transpose
        (CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_AntisymVort M_cg) =
        CliffordBottKTheoryWignerS4Poset.Mat3.smul (-1)
          (CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_AntisymVort M_cg)) ∧
     (CliffordBottKTheoryWignerS4Poset.Mat3.tr (Matrix.vecMulVec u_vec v_vec) =
        u_vec 0 * v_vec 0 + u_vec 1 * v_vec 1 + u_vec 2 * v_vec 2 ∧
      CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_AntisymVort
        (Matrix.vecMulVec u_vec v_vec) 1 2 =
        3 * CliffordBottKTheoryWignerS4Poset.Mat3.zornCross3D u_vec v_vec 0 ∧
      CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_AntisymVort
        (Matrix.vecMulVec u_vec v_vec) 2 0 =
        3 * CliffordBottKTheoryWignerS4Poset.Mat3.zornCross3D u_vec v_vec 1 ∧
      CliffordBottKTheoryWignerS4Poset.Mat3.cgChan3_AntisymVort
        (Matrix.vecMulVec u_vec v_vec) 0 1 =
        3 * CliffordBottKTheoryWignerS4Poset.Mat3.zornCross3D u_vec v_vec 2 ∧
      CliffordBottKTheoryWignerS4Poset.Mat3.zornCross3D u_vec v_vec =
        InfoGeometry.Algebra.ZornVec3.cross u_vec v_vec)) ∧
    (CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op =
        InfoGeometry.OperatorAlgebra.PeirceSpine.dressedPeirceProjector P M_op M_op ∧
     CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op *
        CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op =
        CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op ∧
     CliffordBottKTheoryWignerS4Poset.K_diag P
        (CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op - P) =
        - InfoGeometry.OperatorAlgebra.PeirceSpine.comm
            (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P M_op)
            (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P M_op) ∧
     ι (CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op) *
        ι (CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op) =
        ι (CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op) ∧
     Fintype.card (PeirceIndex (n + 4)) = 16 * Fintype.card (PeirceIndex n)) := by
  have hS4 := CliffordBottKTheoryWignerS4Poset.s4_wedderburn_artin_trees_and_adams_j_mod24_lock
  have hUnits := CliffordBottKTheoryWignerS4Poset.adams_j_homomorphism_all_z24_units_divisibility
  have hCG :=
    CliffordBottKTheoryWignerS4Poset.Mat3.wigner_clebsch_gordan_s4_four_channel_decomposition M_cg
  have hZorn :=
    CliffordBottKTheoryWignerS4Poset.Mat3.kb5_antisym_channel_zorn_cross_product_bridge u_vec v_vec
  have hZornVec :=
    CliffordBottKTheoryWignerS4Poset.Mat3.kb5_zorn_vector_matrix_cross_and_dot_bridge u_vec v_vec
  have hKO :=
    CliffordBottKTheoryWignerS4Poset.ko_theory_pmi_bruhat_projector_colimit_stability P M_op hP ι n
  exact ⟨⟨hS4.1, hS4.2.2.2.1, hS4.2.2.2.2.1, hS4.2.2.2.2.2.1,
          hS4.2.2.2.2.2.2.1, hS4.2.2.2.2.2.2.2.1, hUnits.2⟩,
         ⟨hCG, ⟨hZorn.1, hZorn.2.1, hZorn.2.2.1, hZorn.2.2.2, hZornVec.2.1⟩⟩,
         hKO⟩

/--
**Theorem 8N (`wigner_hurwitz_adams_frobenius_pythagorean_and_d23_filter_synthesis`):**
Combines the scaled idempotency, mutual annihilation, and Frobenius Pythagorean decomposition of
the four Wigner–Clebsch–Gordan channels on `Matrix (Fin 3) (Fin 3) K`
(`WignerHurwitzAdamsKTheoryPoset.Mat3.clebsch_gordan_s4_idempotency_and_mutual_orthogonality`,
`WignerHurwitzAdamsKTheoryPoset.Mat3.clebsch_gordan_frobenius_pythagorean_theorem`), the Hurwitz
quaternion norm multiplicativity, spinor-corner `ℤ₃` triality conjugation identities, and
`Quaternion K` / `DiscreteHurwitzCliffordWavelet` paraunitary readouts
(`WignerHurwitzAdamsKTheoryPoset.Quat.hurwitz_corner_triality_attention_filter`,
`WignerHurwitzAdamsKTheoryPoset.Quat.hurwitz_quaternion_and_paraunitary_filter_bank_bridge`),
and the cyclotomic polynomial factorization identities
(`WignerHurwitzAdamsKTheoryPoset.adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge`).
This statement is a conjunction of those finite-stage algebraic results and does not establish a
continuous homotopy-group construction of `π₃(SO) ↠ π₃^s`.
-/
theorem wigner_hurwitz_adams_frobenius_pythagorean_and_d23_filter_synthesis
    {K : Type*} [CommRing K]
    (M_cg N_cg : WignerHurwitzAdamsKTheoryPoset.Mat3 K)
    (Q_quat X_quat : WignerHurwitzAdamsKTheoryPoset.Quat K)
    (x_cyc : K) :
    (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi1 M_cg +
        WignerHurwitzAdamsKTheoryPoset.Mat3.Pi2 M_cg +
        WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_pos M_cg +
        WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_neg M_cg =
        WignerHurwitzAdamsKTheoryPoset.Mat3.smul 6 M_cg ∧
     WignerHurwitzAdamsKTheoryPoset.Mat3.Pi1
        (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi1 M_cg) =
        WignerHurwitzAdamsKTheoryPoset.Mat3.smul 6
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi1 M_cg) ∧
     WignerHurwitzAdamsKTheoryPoset.Mat3.Pi2
        (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi2 M_cg) =
        WignerHurwitzAdamsKTheoryPoset.Mat3.smul 6
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi2 M_cg) ∧
     WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_pos
        (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_pos M_cg) =
        WignerHurwitzAdamsKTheoryPoset.Mat3.smul 6
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_pos M_cg) ∧
     WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_neg
        (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_neg M_cg) =
        WignerHurwitzAdamsKTheoryPoset.Mat3.smul 6
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_neg M_cg) ∧
     WignerHurwitzAdamsKTheoryPoset.Mat3.Pi1
        (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi2 M_cg) = 0 ∧
     WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_pos
        (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_neg M_cg) = 0 ∧
     WignerHurwitzAdamsKTheoryPoset.Mat3.frobInner
        (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi1 M_cg)
        (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi2 N_cg) = 0 ∧
     WignerHurwitzAdamsKTheoryPoset.Mat3.frobInner
        (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_pos M_cg)
        (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_neg N_cg) = 0 ∧
     36 * WignerHurwitzAdamsKTheoryPoset.Mat3.frobInner M_cg N_cg =
        WignerHurwitzAdamsKTheoryPoset.Mat3.frobInner
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi1 M_cg)
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi1 N_cg) +
        WignerHurwitzAdamsKTheoryPoset.Mat3.frobInner
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi2 M_cg)
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi2 N_cg) +
        WignerHurwitzAdamsKTheoryPoset.Mat3.frobInner
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_pos M_cg)
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_pos N_cg) +
        WignerHurwitzAdamsKTheoryPoset.Mat3.frobInner
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_neg M_cg)
          (WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_neg N_cg)) ∧
    (8 + 2 ^ 4 = 24 ∧
     24 + Nat.choose 4 2 * 2 ^ 2 = 48 ∧
     WignerHurwitzAdamsKTheoryPoset.Quat.qNorm (Q_quat * X_quat) =
        WignerHurwitzAdamsKTheoryPoset.Quat.qNorm Q_quat *
          WignerHurwitzAdamsKTheoryPoset.Quat.qNorm X_quat ∧
     (WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW :
        WignerHurwitzAdamsKTheoryPoset.Quat K) *
        WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW -
        WignerHurwitzAdamsKTheoryPoset.Quat.smul 2
          WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW +
        WignerHurwitzAdamsKTheoryPoset.Quat.smul 4
          WignerHurwitzAdamsKTheoryPoset.Quat.qOne = 0 ∧
     (WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW :
        WignerHurwitzAdamsKTheoryPoset.Quat K) *
        WignerHurwitzAdamsKTheoryPoset.Quat.qi *
        WignerHurwitzAdamsKTheoryPoset.Quat.conj
          WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW =
        WignerHurwitzAdamsKTheoryPoset.Quat.smul 4
          WignerHurwitzAdamsKTheoryPoset.Quat.qj ∧
     (WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW :
        WignerHurwitzAdamsKTheoryPoset.Quat K) *
        WignerHurwitzAdamsKTheoryPoset.Quat.qj *
        WignerHurwitzAdamsKTheoryPoset.Quat.conj
          WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW =
        WignerHurwitzAdamsKTheoryPoset.Quat.smul 4
          WignerHurwitzAdamsKTheoryPoset.Quat.qk ∧
     (WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW :
        WignerHurwitzAdamsKTheoryPoset.Quat K) *
        WignerHurwitzAdamsKTheoryPoset.Quat.qk *
        WignerHurwitzAdamsKTheoryPoset.Quat.conj
          WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW =
        WignerHurwitzAdamsKTheoryPoset.Quat.smul 4
          WignerHurwitzAdamsKTheoryPoset.Quat.qi ∧
     WignerHurwitzAdamsKTheoryPoset.Quat.toQuaternion (Q_quat * X_quat) =
        WignerHurwitzAdamsKTheoryPoset.Quat.toQuaternion Q_quat *
          WignerHurwitzAdamsKTheoryPoset.Quat.toQuaternion X_quat ∧
     WignerHurwitzAdamsKTheoryPoset.Quat.qNorm Q_quat =
        Quaternion.normSq (WignerHurwitzAdamsKTheoryPoset.Quat.toQuaternion Q_quat) ∧
     (∀ F : InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet.ParaunitaryCliffordFilterBank,
        InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet.paraunitary F →
          F.sum_normSq_eq_one)) ∧
    (WignerHurwitzAdamsKTheoryPoset.Phi6 (x_cyc ^ 4) =
        WignerHurwitzAdamsKTheoryPoset.Phi24 x_cyc ∧
     (x_cyc ^ 4 + 1) * WignerHurwitzAdamsKTheoryPoset.Phi24 x_cyc = x_cyc ^ 12 + 1 ∧
     (x_cyc ^ 12 - 1) * (x_cyc ^ 4 + 1) *
        WignerHurwitzAdamsKTheoryPoset.Phi24 x_cyc = x_cyc ^ 24 - 1 ∧
     WignerHurwitzAdamsKTheoryPoset.Mat3.Pi2 M_cg +
        WignerHurwitzAdamsKTheoryPoset.Mat3.Pi3_pos M_cg =
        WignerHurwitzAdamsKTheoryPoset.Mat3.Pi5_so3 M_cg ∧
     (WignerHurwitzAdamsKTheoryPoset.Quat.oddCosetU :
        WignerHurwitzAdamsKTheoryPoset.Quat K) *
        WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW *
        WignerHurwitzAdamsKTheoryPoset.Quat.conj
          WignerHurwitzAdamsKTheoryPoset.Quat.oddCosetU =
        WignerHurwitzAdamsKTheoryPoset.Quat.smul 2
          WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW' ∧
     WignerHurwitzAdamsKTheoryPoset.Phi1 x_cyc *
        WignerHurwitzAdamsKTheoryPoset.Phi2 x_cyc *
        WignerHurwitzAdamsKTheoryPoset.Phi3 x_cyc *
        WignerHurwitzAdamsKTheoryPoset.Phi4 x_cyc *
        WignerHurwitzAdamsKTheoryPoset.Phi6 x_cyc *
        WignerHurwitzAdamsKTheoryPoset.Phi8 x_cyc *
        WignerHurwitzAdamsKTheoryPoset.Phi12 x_cyc *
        WignerHurwitzAdamsKTheoryPoset.Phi24 x_cyc = x_cyc ^ 24 - 1) := by
  have hIdem :=
    WignerHurwitzAdamsKTheoryPoset.Mat3.clebsch_gordan_s4_idempotency_and_mutual_orthogonality M_cg
  have hFrob :=
    WignerHurwitzAdamsKTheoryPoset.Mat3.clebsch_gordan_frobenius_pythagorean_theorem M_cg N_cg
  have hHurw :=
    WignerHurwitzAdamsKTheoryPoset.Quat.hurwitz_corner_triality_attention_filter Q_quat X_quat
  have hD23 :=
    WignerHurwitzAdamsKTheoryPoset.Quat.hurwitz_quaternion_and_paraunitary_filter_bank_bridge
      Q_quat X_quat
  have hCyc :=
    WignerHurwitzAdamsKTheoryPoset.adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge x_cyc
  have hExt :=
    WignerHurwitzAdamsKTheoryPoset.wh11_extended_wigner_hurwitz_adams_master_synthesis
      M_cg N_cg x_cyc
  rcases hIdem with ⟨hResolution, hPi1, hPi2, hPi3Pos, hPi3Neg,
    hPi1Pi2, _, _, _, _, _, _, _, _, _, hPi3PosPi3Neg, _⟩
  exact ⟨⟨hResolution, hPi1, hPi2, hPi3Pos, hPi3Neg,
          hPi1Pi2, hPi3PosPi3Neg,
          hFrob.1, hFrob.2.2.2.1, hFrob.2.2.2.2⟩,
         ⟨hHurw.1, by decide, hHurw.2.2.1, hHurw.2.2.2.2.1,
          hHurw.2.2.2.2.2.2.1, hHurw.2.2.2.2.2.2.2.1, hHurw.2.2.2.2.2.2.2.2,
          hD23.2.2.1, hD23.2.2.2.2.1, hD23.2.2.2.2.2.1⟩,
         ⟨hCyc.1, hCyc.2.1, hCyc.2.2,
          hExt.1.1, hExt.2.1.2.2.1,
          (WignerHurwitzAdamsKTheoryPoset.complete_cyclotomic_24_factorization_and_spectral_dimensions x_cyc).2.2.2.2.2.2⟩⟩

/--
**Theorem 8O (`pin_minus_88_octahedral_reflection_cl11_parity_time_and_abk_triality_synthesis`):**
Combines the finite `Pin_-` short-root reflection identities, Hurwitz triality generation
`reflIJ * reflJK = hurwitzW`, `S₃` braid identity, and real orthogonal reflection on `Quat K` / `ℝ³`
(`PinMinus88TrialityPoset.Quat.pin_minus_reflection_lift_in_binary_octahedral_coset`,
`PinMinus88TrialityPoset.Quat.pin_minus_short_root_product_eq_hurwitz_triality_and_braid_relation`,
`PinMinus88TrialityPoset.pinMinusJKUnitRoot_norm_and_square`,
`PinMinus88TrialityPoset.pinMinusJKReflection3_is_orthogonal_improper`), the $2 \times 2$ and $4 \times 4$
split Clifford parity-time generator relations and `TowerMatrix.Idx 8` cardinality
(`PinMinus88TrialityPoset.Mat2.cl_minus_1_1_split_generators_and_parity_time_d4_relations`,
`PinMinus88TrialityPoset.Mat2.cl_minus_3_0_into_split_cl_2_2_kronecker_embedding`,
`PinMinus88TrialityPoset.Mat2.cl11_tensor_tower_parity_time_and_idx8_bridge`), and the cyclotomic
factorization `Phi8 (x_cyc ^ 3) = Phi8 x_cyc * Phi24 x_cyc = Phi8 x_cyc * Phi6 (x_cyc ^ 4)` and
Chinese Remainder idempotent split `(9 : ZMod 24)` / `(16 : ZMod 24)`
(`PinMinus88TrialityPoset.pin_minus_abk_triality_cyclotomic_bridge`,
`PinMinus88TrialityPoset.zmod24_chinese_remainder_abk_triality_split`).
This statement is a conjunction of those finite-stage algebraic results and does not establish a
Lie-group construction of `Pin_-(8,8)` or a cobordism calculation of `Ω₂^{Pin_-}`.
-/
theorem pin_minus_88_octahedral_reflection_cl11_parity_time_and_abk_triality_synthesis
    {K : Type*} [CommRing K]
    (x_vec y_vec z_vec x_cyc : K) :
    (PinMinus88TrialityPoset.Quat.qNorm
        (PinMinus88TrialityPoset.Quat.reflJK : PinMinus88TrialityPoset.Quat K) = 2 ∧
     (PinMinus88TrialityPoset.Quat.reflJK : PinMinus88TrialityPoset.Quat K) *
        PinMinus88TrialityPoset.Quat.reflJK =
        PinMinus88TrialityPoset.Quat.smul (-2) PinMinus88TrialityPoset.Quat.qOne ∧
     PinMinus88TrialityPoset.Quat.pinRefl
        PinMinus88TrialityPoset.Quat.reflJK
        (PinMinus88TrialityPoset.Quat.vec3 x_vec y_vec z_vec) =
        PinMinus88TrialityPoset.Quat.smul 2
          (PinMinus88TrialityPoset.Quat.vec3 x_vec z_vec y_vec) ∧
     PinMinus88TrialityPoset.Quat.pinRefl
        PinMinus88TrialityPoset.Quat.reflJK
        (PinMinus88TrialityPoset.Quat.pinRefl
          PinMinus88TrialityPoset.Quat.reflJK
          (PinMinus88TrialityPoset.Quat.vec3 x_vec y_vec z_vec)) =
        PinMinus88TrialityPoset.Quat.smul 4
          (PinMinus88TrialityPoset.Quat.vec3 x_vec y_vec z_vec) ∧
     (PinMinus88TrialityPoset.Quat.reflJK : PinMinus88TrialityPoset.Quat K) *
        PinMinus88TrialityPoset.Quat.hurwitzW *
        PinMinus88TrialityPoset.Quat.conj PinMinus88TrialityPoset.Quat.reflJK =
        PinMinus88TrialityPoset.Quat.smul 2
          PinMinus88TrialityPoset.Quat.hurwitzW_refl ∧
     (PinMinus88TrialityPoset.Quat.reflIJ : PinMinus88TrialityPoset.Quat K) *
        PinMinus88TrialityPoset.Quat.reflJK =
        PinMinus88TrialityPoset.Quat.hurwitzW ∧
     (PinMinus88TrialityPoset.Quat.reflIJ : PinMinus88TrialityPoset.Quat K) *
        PinMinus88TrialityPoset.Quat.reflJK *
        PinMinus88TrialityPoset.Quat.reflIJ =
        PinMinus88TrialityPoset.Quat.smul (-2) PinMinus88TrialityPoset.Quat.reflKI ∧
     PinMinus88TrialityPoset.Quat.binaryOctahedral48Finset.card = 48 ∧
     Quaternion.normSq PinMinus88TrialityPoset.pinMinusJKUnitRoot = 1 ∧
     PinMinus88TrialityPoset.pinMinusJKUnitRoot *
        PinMinus88TrialityPoset.pinMinusJKUnitRoot = (-1 : Quaternion ℝ) ∧
     Matrix.det PinMinus88TrialityPoset.pinMinusJKReflection3 = -1 ∧
     -PinMinus88TrialityPoset.quatAdjointMatrix3 PinMinus88TrialityPoset.pinMinusJKUnitRoot =
        PinMinus88TrialityPoset.pinMinusJKReflection3) ∧
    ((PinMinus88TrialityPoset.Mat2.parityP : PinMinus88TrialityPoset.Mat2 K) *
        PinMinus88TrialityPoset.Mat2.parityP = -PinMinus88TrialityPoset.Mat2.I2 ∧
     (PinMinus88TrialityPoset.Mat2.timeT : PinMinus88TrialityPoset.Mat2 K) *
        PinMinus88TrialityPoset.Mat2.timeT = PinMinus88TrialityPoset.Mat2.I2 ∧
     (PinMinus88TrialityPoset.Mat2.parityP : PinMinus88TrialityPoset.Mat2 K) *
        PinMinus88TrialityPoset.Mat2.timeT +
        PinMinus88TrialityPoset.Mat2.timeT *
          PinMinus88TrialityPoset.Mat2.parityP = 0 ∧
     (PinMinus88TrialityPoset.Mat2.chiralPT : PinMinus88TrialityPoset.Mat2 K) *
        PinMinus88TrialityPoset.Mat2.chiralPT = PinMinus88TrialityPoset.Mat2.I2 ∧
     (PinMinus88TrialityPoset.Mat2.clMinus3Refl23 : PinMinus88TrialityPoset.Mat2.Mat4Split K) *
        PinMinus88TrialityPoset.Mat2.clMinus3Refl23 =
        (-2 : K) • (1 : PinMinus88TrialityPoset.Mat2.Mat4Split K) ∧
     Function.Injective PinMinus88TrialityPoset.Mat2.mat4SplitToMatStage8AlgHom ∧
     PinMinus88TrialityPoset.Mat2.toMatrix
        (PinMinus88TrialityPoset.Mat2.parityP : PinMinus88TrialityPoset.Mat2 ℝ) =
        InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase ∧
     Fintype.card (InfoGeometry.Clifford.TowerMatrix.Idx 8) = 256) ∧
    (8 * 3 = 24 ∧ 3 * 3 - 1 * 8 = 1 ∧
     PinMinus88TrialityPoset.Phi8 (x_cyc ^ 3) =
        PinMinus88TrialityPoset.Phi8 x_cyc * PinMinus88TrialityPoset.Phi24 x_cyc ∧
     PinMinus88TrialityPoset.Phi8 (x_cyc ^ 3) =
        PinMinus88TrialityPoset.Phi8 x_cyc * PinMinus88TrialityPoset.Phi6 (x_cyc ^ 4) ∧
     (x_cyc ^ 12 - 1) * PinMinus88TrialityPoset.Phi8 (x_cyc ^ 3) = x_cyc ^ 24 - 1 ∧
     (9 : ZMod 24) * 16 = 0 ∧ (9 : ZMod 24) + 16 = 1) := by
  have hRefl :=
    PinMinus88TrialityPoset.Quat.pin_minus_reflection_lift_in_binary_octahedral_coset
      x_vec y_vec z_vec
  have hBraid :=
    PinMinus88TrialityPoset.Quat.pin_minus_short_root_product_eq_hurwitz_triality_and_braid_relation
      x_vec y_vec z_vec
  have h48 :=
    PinMinus88TrialityPoset.Quat.binary_octahedral_48_coset_decomposition_and_octahedral_pole_action
  have hUnit := PinMinus88TrialityPoset.pinMinusJKUnitRoot_norm_and_square
  have hOrth := PinMinus88TrialityPoset.pinMinusJKReflection3_is_orthogonal_improper
  have hAdj :=
    PinMinus88TrialityPoset.quatAdjointMatrix3_homomorphism_orthogonality_and_graded_2O_action
      (PinMinus88TrialityPoset.Quat.qOne : PinMinus88TrialityPoset.Quat ℝ)
      (PinMinus88TrialityPoset.Quat.qOne : PinMinus88TrialityPoset.Quat ℝ)
      (fun _ => (0 : ℝ))
  have hPT :=
    PinMinus88TrialityPoset.Mat2.cl_minus_1_1_split_generators_and_parity_time_d4_relations
      (K := K)
  have hCl3 :=
    PinMinus88TrialityPoset.Mat2.cl_minus_3_0_into_split_cl_2_2_kronecker_embedding (K := K)
  have hSt8 :=
    PinMinus88TrialityPoset.Mat2.clMinus30_into_matStage8_algHom_and_reflection_transport
  have hIdx8 :=
    PinMinus88TrialityPoset.Mat2.cl11_tensor_tower_parity_time_and_idx8_bridge
  have hCyc :=
    PinMinus88TrialityPoset.pin_minus_abk_triality_cyclotomic_bridge x_cyc
  have hCRT :=
    PinMinus88TrialityPoset.zmod24_chinese_remainder_abk_triality_split
  exact ⟨⟨hRefl.1, hRefl.2.1, hRefl.2.2.2.2.2.1, hRefl.2.2.2.2.2.2.1, hRefl.2.2.2.2.2.2.2,
          hBraid.2.2.2.2.1, hBraid.2.2.2.2.2.1, h48.2.2.2.2.1,
          hUnit.1, hUnit.2.1, hOrth.2, hAdj.2.2.2.2.2⟩,
         ⟨hPT.2.2.2.2.1, hPT.2.2.2.2.2.1, hPT.2.2.2.2.2.2.1, hPT.2.2.2.2.2.2.2.2,
          hCl3.2.2.1, hSt8.1, hIdx8.1, hIdx8.2.2.2⟩,
         ⟨hCyc.1, hCyc.2.1, hCyc.2.2.1, hCyc.2.2.2.1, hCyc.2.2.2.2,
          hCRT.2.2.2.2.2.2.1, hCRT.2.2.2.2.2.2.2⟩⟩

/--
**Theorem 8P (`kitaev_local_bulk_gap_collar_healing_and_universal_invertibility_rotor_synthesis`):**
Combines the conditional affine ground-state fiber invariance and spectral-annulus midpoint
centering (`KitaevLocalGapOmegaSpectrumPoset.convex_hamiltonian_fiber_ground_state_invariance`,
`KitaevLocalGapOmegaSpectrumPoset.energy_gap_annulus_midpoint_centering`), the square-first vs.
truncate-first Peirce collar excursion identity and its bridge to `PeirceSpine.conePlus`
and `coneMinus` (`KitaevLocalGapOmegaSpectrumPoset.square_first_local_bulk_gap_collar_healing`,
`KitaevLocalGapOmegaSpectrumPoset.n_plus_minus_eq_centralizer_cones`), the universal $2 \times 2$
block anticommutators (both Hadamard-rotated and direct unrotated), division-free Hadamard
similarity, rotor squares, unit-gap homotopy preservation, pole domain-wall cancellation, and dimer
re-association cancellation (`KitaevLocalGapOmegaSpectrumPoset.Block2.universal_invertibility_anticommuting_homotopy`,
`KitaevLocalGapOmegaSpectrumPoset.Block2.universal_unrotated_and_hadamard_invertibility_rotor`,
`KitaevLocalGapOmegaSpectrumPoset.Block2.unit_gap_rotor_preservation_and_pole_endpoints`), and the
concrete $4$-Majorana open Kitaev chain collar healing and $2 \times 2$ Brown–Gauss 8-fold matrix
powers (`KitaevLocalGapOmegaSpectrumPoset.Mat4.open_kitaev_majorana_chain_square_first_healing`,
`KitaevLocalGapOmegaSpectrumPoset.Block2.brown_gauss_matrix_power_identities`).
This statement is a conjunction of those finite-stage ring identities under explicit hypotheses and
does not establish a continuous homotopy equivalence $A_d \simeq \Omega A_{d+1} \simeq KO_{d-2}$.
-/
theorem kitaev_local_bulk_gap_collar_healing_and_universal_invertibility_rotor_synthesis
    {B : Type*} [Ring B] {K : Type*} [CommRing K]
    (H0 H1 P0 t P A A0 μ0 c s : B)
    (h0 : H0 * P0 = 0) (h1 : H1 * P0 = 0) (hP : P * P = P)
    (hc : c * A = A * c) (hs : s * A = A * s) (hcs : c * s = s * c)
    (Q a_sq b_sq : K) :
    (((1 - t) * H0 + t * H1) * P0 = 0 ∧
     (b_sq - a_sq) ^ 2 - (2 * Q - (a_sq + b_sq)) ^ 2 = 4 * (Q - a_sq) * (b_sq - Q)) ∧
    (KitaevLocalGapOmegaSpectrumPoset.SquareFirstBulkOp P A μ0 -
       KitaevLocalGapOmegaSpectrumPoset.TruncateFirstBulkOp P A μ0 =
       - (KitaevLocalGapOmegaSpectrumPoset.N_plus P A *
            KitaevLocalGapOmegaSpectrumPoset.N_minus P A) ∧
     (P * (A * A) * P = -P →
       KitaevLocalGapOmegaSpectrumPoset.SquareFirstBulkOp P A 1 = 0 ∧
       KitaevLocalGapOmegaSpectrumPoset.TruncateFirstBulkOp P A 1 =
         KitaevLocalGapOmegaSpectrumPoset.N_plus P A *
           KitaevLocalGapOmegaSpectrumPoset.N_minus P A) ∧
     KitaevLocalGapOmegaSpectrumPoset.N_plus P A =
       InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A ∧
     KitaevLocalGapOmegaSpectrumPoset.N_minus P A =
       InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P A) ∧
    (KitaevLocalGapOmegaSpectrumPoset.Block2.doubledSys A *
       KitaevLocalGapOmegaSpectrumPoset.Block2.baseDecoupler +
       KitaevLocalGapOmegaSpectrumPoset.Block2.baseDecoupler *
         KitaevLocalGapOmegaSpectrumPoset.Block2.doubledSys A = 0 ∧
     KitaevLocalGapOmegaSpectrumPoset.Block2.diagSys A *
       KitaevLocalGapOmegaSpectrumPoset.Block2.baseDecoupler +
       KitaevLocalGapOmegaSpectrumPoset.Block2.baseDecoupler *
         KitaevLocalGapOmegaSpectrumPoset.Block2.diagSys A = 0 ∧
     KitaevLocalGapOmegaSpectrumPoset.Block2.hadamard2 *
       KitaevLocalGapOmegaSpectrumPoset.Block2.diagSys A *
       KitaevLocalGapOmegaSpectrumPoset.Block2.hadamard2 =
       KitaevLocalGapOmegaSpectrumPoset.Block2.doubledSys (A + A) ∧
     KitaevLocalGapOmegaSpectrumPoset.Block2.RotorXY A c s *
       KitaevLocalGapOmegaSpectrumPoset.Block2.RotorXY A c s =
       KitaevLocalGapOmegaSpectrumPoset.Block2.mk2
         (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s) ∧
     KitaevLocalGapOmegaSpectrumPoset.Block2.DirectRotor A c s *
       KitaevLocalGapOmegaSpectrumPoset.Block2.DirectRotor A c s =
       KitaevLocalGapOmegaSpectrumPoset.Block2.mk2
         (c * c * (A * A) - s * s) 0 0 (c * c * (A * A) - s * s) ∧
     (A * A = -1 → c * c + s * s = 1 →
       KitaevLocalGapOmegaSpectrumPoset.Block2.RotorXY A c s *
         KitaevLocalGapOmegaSpectrumPoset.Block2.RotorXY A c s =
         KitaevLocalGapOmegaSpectrumPoset.Block2.mk2 (-1) 0 0 (-1)) ∧
     KitaevLocalGapOmegaSpectrumPoset.Block2.RotorXY A 0 1 +
       KitaevLocalGapOmegaSpectrumPoset.Block2.RotorXY A 0 (-1) = 0 ∧
     (A - A0) + (A0 - A0) + (A0 - A0) = A - A0) ∧
    (- ((KitaevLocalGapOmegaSpectrumPoset.Mat4.kitaevChainA :
          KitaevLocalGapOmegaSpectrumPoset.Mat4 K) *
         KitaevLocalGapOmegaSpectrumPoset.Mat4.kitaevChainA) -
       KitaevLocalGapOmegaSpectrumPoset.Mat4.I4 =
       KitaevLocalGapOmegaSpectrumPoset.Mat4.edgeZeroModeDefect ∧
     KitaevLocalGapOmegaSpectrumPoset.TruncateFirstBulkOp
       (KitaevLocalGapOmegaSpectrumPoset.Mat4.projCut2 :
         KitaevLocalGapOmegaSpectrumPoset.Mat4 K)
       KitaevLocalGapOmegaSpectrumPoset.Mat4.kitaevChainA 1 =
       -KitaevLocalGapOmegaSpectrumPoset.Mat4.projCut2 ∧
     KitaevLocalGapOmegaSpectrumPoset.N_plus
       (KitaevLocalGapOmegaSpectrumPoset.Mat4.projCut2 :
         KitaevLocalGapOmegaSpectrumPoset.Mat4 K)
       KitaevLocalGapOmegaSpectrumPoset.Mat4.kitaevChainA *
       KitaevLocalGapOmegaSpectrumPoset.N_minus
         KitaevLocalGapOmegaSpectrumPoset.Mat4.projCut2
         KitaevLocalGapOmegaSpectrumPoset.Mat4.kitaevChainA =
       -KitaevLocalGapOmegaSpectrumPoset.Mat4.projCut2 ∧
     KitaevLocalGapOmegaSpectrumPoset.SquareFirstBulkOp
       (KitaevLocalGapOmegaSpectrumPoset.Mat4.projCut2 :
         KitaevLocalGapOmegaSpectrumPoset.Mat4 K)
       KitaevLocalGapOmegaSpectrumPoset.Mat4.kitaevChainA 1 = 0 ∧
     (((KitaevLocalGapOmegaSpectrumPoset.Block2.brownGaussU :
          KitaevLocalGapOmegaSpectrumPoset.Block2 K) *
         KitaevLocalGapOmegaSpectrumPoset.Block2.brownGaussU) *
        (KitaevLocalGapOmegaSpectrumPoset.Block2.brownGaussU *
         KitaevLocalGapOmegaSpectrumPoset.Block2.brownGaussU)) *
       (((KitaevLocalGapOmegaSpectrumPoset.Block2.brownGaussU :
            KitaevLocalGapOmegaSpectrumPoset.Block2 K) *
           KitaevLocalGapOmegaSpectrumPoset.Block2.brownGaussU) *
          (KitaevLocalGapOmegaSpectrumPoset.Block2.brownGaussU *
           KitaevLocalGapOmegaSpectrumPoset.Block2.brownGaussU)) =
       (16 : K) • (1 : KitaevLocalGapOmegaSpectrumPoset.Block2 K)) := by
  have hFib :=
    KitaevLocalGapOmegaSpectrumPoset.convex_hamiltonian_fiber_ground_state_invariance
      H0 H1 P0 t h0 h1
  have hAnn :=
    KitaevLocalGapOmegaSpectrumPoset.energy_gap_annulus_midpoint_centering Q a_sq b_sq
  have hGap :=
    KitaevLocalGapOmegaSpectrumPoset.square_first_local_bulk_gap_collar_healing P A μ0 hP
  have hCones :=
    KitaevLocalGapOmegaSpectrumPoset.n_plus_minus_eq_centralizer_cones P A
  have hInv :=
    KitaevLocalGapOmegaSpectrumPoset.Block2.universal_invertibility_anticommuting_homotopy
      A A0 c s hc hs hcs
  have hUnrot :=
    KitaevLocalGapOmegaSpectrumPoset.Block2.universal_unrotated_and_hadamard_invertibility_rotor
      A c s hc hs hcs
  have hUnit :=
    KitaevLocalGapOmegaSpectrumPoset.Block2.unit_gap_rotor_preservation_and_pole_endpoints
      A c s hc hs hcs
  have hMaj :=
    KitaevLocalGapOmegaSpectrumPoset.Mat4.open_kitaev_majorana_chain_square_first_healing (K := K)
  have hBrown :=
    KitaevLocalGapOmegaSpectrumPoset.Block2.brown_gauss_matrix_power_identities
      (B := K)
  exact ⟨⟨hFib, hAnn⟩,
         ⟨hGap.1, hGap.2, hCones.1, hCones.2.1⟩,
         ⟨hInv.1, hUnrot.2.1, hUnrot.2.2.1.1, hInv.2.1, hUnrot.2.2.2.2,
          hUnit.1, hUnit.2.2.2.2.2.1, hInv.2.2⟩,
         ⟨hMaj.2.1, hMaj.2.2.2.1.2.2, hMaj.2.2.2.2.1, hMaj.2.2.2.2.2.2, hBrown.2.2.2⟩⟩

end InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset
