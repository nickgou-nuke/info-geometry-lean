/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.ZModFourierBridge
import InfoGeometry.LLM.CyclicGramGeometry
import InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset
import InfoGeometry.Canonical.LanguageStatisticsTranslationSymmetry
import InfoGeometry.Canonical.PlabicGramEigenvectorTransport
import InfoGeometry.OperatorAlgebra.PeirceCoupling.GramGeometry
import InfoGeometry.Canonical.SmithBlockCirculantMoorePenrose
import InfoGeometry.Parafermion.ParafermionCondensationGaloisCharacterPoset
import InfoGeometry.Canonical.V4GroupFourierTransform
import InfoGeometry.Core.TensorPeirceDecomposition
import InfoGeometry.Algebra.MonarchFactorization
import InfoGeometry.Routing.BirkhoffVonNeumann
import InfoGeometry.Canonical.GibsonBasicDoublyStochastic
import InfoGeometry.QuantumContext.MarkovDrazinSemisimplicity
import InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge
import InfoGeometry.Clifford.Cl55PeirceMoERouting
import InfoGeometry.Krein.FiniteGramFactorization
import InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential
import InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
import InfoGeometry.Quantum.DoubledSylvesterCommutantBridge
import InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus
import InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset
import InfoGeometry.GaloisQuotient.GaloisQuotientNonAbelianFourierPoset
import InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset
import InfoGeometry.WignerHurwitzAdamsKTheory.WignerHurwitzAdamsKTheoryPoset
import InfoGeometry.PinMinus88Triality.PinMinus88TrialityPoset
import InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevLocalGapOmegaSpectrumPoset
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Data.Nat.Totient
import Omega.Core.Word
import Omega.Core.WalshFourier

open scoped Matrix Kronecker

/-!
# Language Symmetry and Related Finite Algebra Catalog

## i. Overview

This canonical module collects selected finite algebraic claims motivated by
Dhruva Karkada, Daniel J. Korchinski, Andres Nava, Matthieu Wyart, and Yasaman Bahri,
 *"Symmetry in language statistics shapes the geometry of model representations"* (`arXiv:2602.15029`),
alongside related results from repository owners for
circulant/Toeplitz operators, Fourier characters, Gramian factorizations, Birkhoff bistochastic
permutation polytopes, stochastic grammar Drazin semisimplicity, Clifford Mixture-of-Experts (MoE)
routing, Yangian RTT monodromy, and recursive Tensor-Peirce decomposition with centralizer
homogenization:

* **Node `𝔏𝔖₁` (`ls1_shift_commutant_subalgebra_and_indirect_cooccurrence_closure`):**
  Proves in any associative ring `[Ring B]` that the centralizer (commutant) of a shift operator
  `S : B` is closed under addition, subtraction, multiplication, and higher powers:
  `comm S K₁ = 0 → comm S K₂ = 0 → comm S (K₁ + K₂) = 0 ∧ comm S (K₁ * K₂) = 0 ∧ comm S (K₁ * K₁) = 0`.
  Proves `peirce_two_hop_excursion_metric_and_shift_commutation`: for any month-subspace projector
  `P * P = P` and vocabulary co-occurrence operator `M`, `P * (M * M) * P = (P * M * P)² + conePlus P M * coneMinus P M`;
  when direct month-to-month co-occurrences are deleted (`P * M * P = 0`), the two-hop block reduces
  to the algebraic excursion term `conePlus P M * coneMinus P M`. This conditional identity does not
  identify the term with a measured month kernel from the paper's empirical helper-word experiment.
  The excursion term commutes with the cyclic shift `S` whenever `comm S P = 0` and `comm S M = 0`.
  Bridges directly to `ZModFourierBridge.matrix_translation_invariant_iff_eq_circulant`,
  `blockCirculant3_commutes_cyclicShift`, and proves that every `3 × 3` circulant matrix
  `blockCirculant3 c0 c1 c2` whose row sums to `1` (`c0 + c1 + c2 = 1`) is automatically
  algebraically doubly stochastic (`IsAlgebraicDoublyStochastic`).
* **Node `𝔏𝔖₂` (`ls2_circulant_fourier_character_diagonalization_and_circle_degeneracy`):**
  Unifies `ZModFourierBridge` (`circulant_hasEigenvector_stdAddChar`, `dft_circulant_mulVec`) and
  `CyclicGramGeometry` (`cyclicCentering_circulant`, `centered_circulant_hasEigenvector_stdAddChar`,
  `centered_circulant_mulVec_eq_invDFT`). Proves in any `[CommRing K]` that any 4-tap circulant
  polynomial `C = c0 + c1 * S + c2 * S² + c3 * S³` acts on a shift eigenmode (`S * v = ζ * v`) with
  eigenvalue `c0 + c1 * ζ + c2 * ζ² + c3 * ζ³`, and for a symmetric periodic kernel (`c3 = c1`)
  creates the 2D cosine/sine circular eigenspace degeneracy `μ_k = μ_{N-k}`. Proves
  `binary_involution_spectral_linearization`: proves polynomial identities for an involution and
  the corresponding two-eigenspace linearization. It does not prove a real-log identity, define
  PMI, or derive the probability factorization in Eq. (44).
* **Node `𝔏𝔖₃` (`ls3_gramian_torus_ripple_embedding_and_metriplectic_coincidence`):**
  Unifies `CyclicGramGeometry` (`cyclicAutocorrelation_gram`, `cyclicAutocorrelation_posSemidef`,
  `dft_cyclicAutocorrelation_eq_normSq`, `cyclicRealFourierPair_gram_eq_circulant`) with the
  two-harmonic Clifford torus / helical ripple embedding `w(j) = (r₁ cos₁(j), r₁ sin₁(j), r₂ cos₂(j), r₂ sin₂(j))`
  (`arXiv:2602.15029` §§2–3): shift-invariant Gramian `r₁² cos₁(i - j) + r₂² cos₂(i - j)`, constant
  squared radius `r₁² + r₂²`, squared chordal step velocity `2 r₁² (1 - c₁) + 2 r₂² (1 - c_m)`, and
  squared 2nd discrete difference (extrinsic ripple curvature) `4 r₁² (1 - c₁)² + 4 r₂² (1 - c_m)²`,
  together with `FiniteGramFactorization`, `PlabicGramEigenvectorTransport`, and the metriplectic
  Out/In Gramian coincidence `(S + K)(S - K) - (S - K)(S + K) = -2 [S, K]`.
* **Node `𝔏𝔖₄` (`ls4_toeplitz_open_boundary_commutator_defect_and_peirce_corner_leakage`):**
  Separates periodic circulant domains (`ℤ_N`) from bounded open intervals (`{1, …, N}`):
  for the symmetric `3 × 3` Toeplitz matrix `symToeplitz3 t0 t1 t2 = !![t0, t1, t2; t1, t0, t1; t2, t1, t0]`,
  its commutator with `cyclicShift3` is `(t2 - t1) • !![1, 0, 0; -1, 0, 0; 0, 1, -1]`, which
  vanishes if and only if the periodic wrap-around condition `t2 = t1` holds. Proves
  `kmsToeplitz3_mul_tridiagLaplacian3`: for the Kac–Murdock–Szegő exponential decay Toeplitz matrix
  `kmsToeplitz3 ρ = symToeplitz3 1 ρ (ρ²)` (modeling open 1D historical year chains, `arXiv:2602.15029`
  §3.2), its product with the tridiagonal discrete Laplacian `kmsTridiagLaplacian3 ρ` is `(1 - ρ²) • I₃`
  with exact wrap-around corner annihilation `(0, 2) = (2, 0) = 0`. Bridges to
  `causalToeplitz3_commute_and_shift_boundary_defect` and `coherenceDefect P F = conePlus P F * coneMinus P F`.
* **Node `𝔏𝔖₅` (`ls5_birkhoff_bistochastic_permutation_polytope_and_stochastic_grammar_moe`):**
  Unifies `BirkhoffRouting.birkhoff_von_neumann_decomposition` (convex permutation decomposition
  of doubly stochastic matrices), `MarkovDrazin.no_length_two_generalized_fixed_vector` (Drazin
  index-1 semisimplicity wall for row-stochastic transition matrices),
  `StochasticGrammarCuntzKriegerBridge.StochasticTransitionMatrix.amplitude_row_l2_normalization`,
  and `Cl55PeirceMoERouting.hypercube_expert_sum_one` (2-bit Clifford Peirce MoE partition of unity).
* **Node `𝔏𝔖₆` (`ls6_recursive_tensor_peirce_centralizer_homogenization_and_monarch_tower`):**
  Unifies the recursive `2^n × 2^n` Tensor-Peirce decomposition (`toTensorTower_ofTensorTower`,
  `ofTensorTower_toTensorTower`), universal algebraic reconstruction
  (`tensor_peirce_exact_reconstruction`), centralizer homogenization (`fromBlocks_pi_homogenization`:
  `pi_{ab}(M) = I₂ ⊗ M_{ab}`), doubled Sylvester sheet commutant duality
  (`DoubledSylvester.commutant_commutes`), Monarch rank-1 crossed-slice factorization
  (`MonarchFactorization.routingSlice_monarch`), and the square-zero centralizer differential
  (`centralizerDifferentialHom_comp_self`).
* **Node `𝔏𝔖₇` (`ls7_language_symmetry_yangian_peirce_birkhoff_master_coagulation`):**
  Grand 7-node synthesis uniting `𝔏𝔖₁`–`𝔏𝔖₆` with the Yangian RTT quantum determinant
  `laxBlockA u θ η * laxBlockD (u - η) θ η - laxBlockB η * laxBlockC η = ((u - θ)² - η²) • 1`
  and the Peirce–Bruhat counterterm idempotency `P_hat_+ * P_hat_+ = P_hat_+`.

## ii. Key results

- `LanguageSymmetryPeirceStage` & `LanguageSymmetryPeirceStage.causalEdge_acyclic`
- `ls1_shift_commutant_subalgebra_and_indirect_cooccurrence_closure`
- `ls2_circulant_fourier_character_diagonalization_and_circle_degeneracy`
- `ls3_gramian_torus_ripple_embedding_and_metriplectic_coincidence`
- `ls4_toeplitz_open_boundary_commutator_defect_and_peirce_corner_leakage`
- `ls5_birkhoff_bistochastic_permutation_polytope_and_stochastic_grammar_moe`
- `ls6_recursive_tensor_peirce_centralizer_homogenization_and_monarch_tower`
- `ls7_language_symmetry_yangian_peirce_birkhoff_master_coagulation`
- `helper_word_ablation_resilience_and_shift_equivariance`
- `binary_involution_spectral_linearization`
- `kronecker_product_eigenmode_of_factorization`
- `binary_attribute_kernel_walsh_eigenmode2`
- `cyclic_fourier_binary_walsh_product_eigenmode`
- `language_walsh_xor_convolution_eigenmode`
- `languageWalshConvolutionMatrix_mulVec`
- `languageWalshConvolutionMatrix_walsh_eigenmode`
- `cyclic_fourier_arbitrary_walsh_product_eigenmode`
- `cyclicV4ProductFourierInv_transform`
- `cyclicV4ProductFourier_convolution`
- `cyclicV4ProductConvolution_eq_inv_mul`
- `cyclicWalshProductFourier_convolution`
- `partitioned_vocabulary_peirce_excursion_eq_convolution_kernel`
- `cyclic_fourier_gram_factorization_and_eigenvalue_difference`
- `open_boundary_exponential_kernel_tridiagonal_inverse`
- `ls7_peirce_helper_excursion_bkm_attribute_surprisal_and_kms_toeplitz_laplacian`
- `ls7_galois_quotient_dihedral_peter_weyl_and_surprisal_survival`
- `ls7_cl11_tensor_stage_factorization_ramanujan24_and_peirce_compression_synthesis`
- `ls7_wigner_clebsch_gordan_s4_zorn_cross_and_dressed_peirce_bott_synthesis`
- `ls7_wigner_hurwitz_adams_frobenius_pythagorean_and_d23_filter_synthesis`

## iii. Table of contents

1. Section 0: The 7-Stage Causal Poset (`𝔏𝔖₁ ≺ ⋯ ≺ 𝔏𝔖₇`) and Strict Acyclicity
2. Node `𝔏𝔖₁`: Translation-Symmetric Shift Commutant Subalgebra, Indirect Co-Occurrence Closure, & Bistochastic Circulants
3. Node `𝔏𝔖₂`: Circulant Polynomial Eigenvalue Evaluation, `μ_k = μ_{N-k}` Circular Degeneracy, & `V₄` / Cyclotomic Character Identities
4. Node `𝔏𝔖₃`: Two-Harmonic Clifford Torus Ripple Gramian, `FiniteGramFactorization`, & Metriplectic Out/In Gramian Coincidence
5. Node `𝔏𝔖₄`: Open-Boundary Toeplitz vs. Periodic Circulant Commutator Defect (`t₂ - t₁`) & Peirce Corner Leakage
6. Node `𝔏𝔖₅`: Birkhoff Bistochastic Permutation Polytope, Stochastic Grammar Drazin Wall, & Clifford MoE Hypercube Routing
7. Node `𝔏𝔖₆`: Recursive Tensor-Peirce Decomposition, Centralizer Homogenization, Sylvester Commutant, & Monarch Slices
8. Node `𝔏𝔖₇`: Master Coagulation with Yangian RTT Quantum Determinant & Peirce–Bruhat Counterterm Idempotency

## iv. References

- D. Karkada, D. J. Korchinski, A. Nava, M. Wyart, and Y. Bahri, *"Symmetry in language statistics shapes the geometry of model representations"*, `arXiv:2602.15029` (2026).
- G. Birkhoff, *"Three observations on linear algebra"*, Univ. Nac. Tucumán Rev. Ser. A 5 (1946).
- S.-I. Amari, *Information Geometry and Its Applications* (2016).

### Three-Bucket Audit Map (`audit-proof` Policy)

#### BUCKET 1 — Proved Kernel Content
- `LanguageSymmetryPeirceStage.causalEdge_acyclic`,
  `ls1_shift_commutant_subalgebra_and_indirect_cooccurrence_closure`.
- `ls2_circulant_fourier_character_diagonalization_and_circle_degeneracy`,
  `ls3_gramian_torus_ripple_embedding_and_metriplectic_coincidence`.
- `symToeplitz3_comm_cyclicShift3`,
  `ls4_toeplitz_open_boundary_commutator_defect_and_peirce_corner_leakage`.
- `ls5_birkhoff_bistochastic_permutation_polytope_and_stochastic_grammar_moe`,
  `ls6_recursive_tensor_peirce_centralizer_homogenization_and_monarch_tower`,
  `ls7_language_symmetry_yangian_peirce_birkhoff_master_coagulation`,
  `helper_word_ablation_resilience_and_shift_equivariance`,
  `binary_involution_spectral_linearization`,
  `binary_attribute_kernel_walsh_eigenmode2`,
  `cyclic_fourier_binary_walsh_product_eigenmode`,
  `language_walsh_xor_convolution_eigenmode`,
  `languageWalshConvolutionMatrix_walsh_eigenmode`,
  `cyclic_fourier_arbitrary_walsh_product_eigenmode`,
  `cyclicV4ProductFourierInv_transform`,
  `open_boundary_exponential_kernel_tridiagonal_inverse`,
  `ls7_peirce_helper_excursion_bkm_attribute_surprisal_and_kms_toeplitz_laplacian`,
  `ls7_galois_quotient_dihedral_peter_weyl_and_surprisal_survival`,
  `ls7_cl11_tensor_stage_factorization_ramanujan24_and_peirce_compression_synthesis`,
  `ls7_wigner_clebsch_gordan_s4_zorn_cross_and_dressed_peirce_bott_synthesis`,
  `ls7_wigner_hurwitz_adams_frobenius_pythagorean_and_d23_filter_synthesis`,
  `ls7_pin_minus_88_octahedral_reflection_cl11_parity_time_and_abk_triality_synthesis`,
  `ls7_kitaev_local_bulk_gap_collar_healing_and_universal_invertibility_rotor_synthesis`.

#### BUCKET 2 — Conditional / Interface Boundaries
- Commutant closure and Peirce identities hold over any `[Ring B]` under explicit commutation
  (`comm S K = 0`) or idempotency (`P * P = P`) hypotheses; trigonometric torus Gramian identities
  hold over any `[CommRing K]` under explicit cosine/sine addition and Pythagorean relations.
- `kronecker_product_eigenmode_of_factorization` composes two supplied matrix factorization
  eigenrelations. `cyclic_fourier_arbitrary_walsh_product_eigenmode` instantiates it with the
  cyclic DFT character and the arbitrary finite Boolean-cube Walsh character. This is a finite
  matrix theorem; it does not establish an empirical corpus or learned-representation claim.

#### BUCKET 3 — Open / Unformalized
- Empirical corpus estimation of PMI matrices on natural-language token streams and asymptotic
  random-matrix Marchenko–Pastur bulk edge distributions are outside the scope of this algebraic
  and finite-matrix owner.
-/

namespace InfoGeometry.Canonical.LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open InfoGeometry.LLM
open InfoGeometry.Information.TranslationSymmetryEmbeddings
open InfoGeometry.Canonical.LanguageStatisticsTranslationSymmetry
open InfoGeometry.Canonical.PlabicGramEigenvectorTransport
open InfoGeometry.OperatorAlgebra.PeirceCoupling
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus
open InfoGeometry.Canonical.SmithBlockCirculantMoorePenrose
open InfoGeometry.Canonical.GibsonBasicDoublyStochastic
open InfoGeometry.Core.TensorPeirceDecomposition
open InfoGeometry.Algebra.MonarchFactorization
open ParafermionCondensationGaloisCharacterPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset

-- ============================================================================
-- SECTION 0: THE 7-STAGE CAUSAL POSET (𝔏𝔖₁ ≺ ⋯ ≺ 𝔏𝔖₇)
-- ============================================================================

/--
The 7-stage index orders a catalog of finite results motivated by `arXiv:2602.15029` and related
repository owners. The rank is declared explicitly; this index does not assert that every result
is derived from the paper or that cross-domain causal maps have been proved.
-/
inductive LanguageSymmetryPeirceStage : Type
  | LS1_ShiftCommutantAndIndirectCooccurrenceClosure
  | LS2_CirculantFourierCharacterAndCircleDegeneracy
  | LS3_GramianTorusRippleAndMetriplecticCoincidence
  | LS4_ToeplitzOpenBoundaryCommutatorAndPeirceDefect
  | LS5_BirkhoffBistochasticStochasticGrammarAndCliffordMoE
  | LS6_RecursiveTensorPeirceCentralizerAndMonarchTower
  | LS7_LanguageSymmetryYangianPeirceBirkhoffMasterCoagulation
  deriving DecidableEq, Repr

namespace LanguageSymmetryPeirceStage

/-- Declared catalog rank `0..6` of each stage in `LanguageSymmetryPeirceStage`. -/
def rank : LanguageSymmetryPeirceStage → ℕ
  | .LS1_ShiftCommutantAndIndirectCooccurrenceClosure => 0
  | .LS2_CirculantFourierCharacterAndCircleDegeneracy => 1
  | .LS3_GramianTorusRippleAndMetriplecticCoincidence => 2
  | .LS4_ToeplitzOpenBoundaryCommutatorAndPeirceDefect => 3
  | .LS5_BirkhoffBistochasticStochasticGrammarAndCliffordMoE => 4
  | .LS6_RecursiveTensorPeirceCentralizerAndMonarchTower => 5
  | .LS7_LanguageSymmetryYangianPeirceBirkhoffMasterCoagulation => 6

/-- `rank` is strictly injective across all 7 stages. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

/-- `LinearOrder` on `LanguageSymmetryPeirceStage` lifted along `rank`. -/
instance instLinearOrder : LinearOrder LanguageSymmetryPeirceStage :=
  LinearOrder.lift' rank rank_injective

/-- Rank-order relation on catalog entries, defined by `rank u < rank v`. -/
def causalEdge (u v : LanguageSymmetryPeirceStage) : Bool :=
  decide (rank u < rank v)

/-- Irreflexivity and transitivity of the declared catalog rank order. -/
theorem causalEdge_acyclic :
    (∀ u : LanguageSymmetryPeirceStage, causalEdge u u = false) ∧
    (∀ u v w : LanguageSymmetryPeirceStage,
      causalEdge u v = true → causalEdge v w = true → causalEdge u w = true) := by
  refine ⟨?_, ?_⟩
  · intro u
    simp [causalEdge]
  · intro u v w huv hvw
    simp only [causalEdge, decide_eq_true_eq] at huv hvw ⊢
    exact Nat.lt_trans huv hvw

end LanguageSymmetryPeirceStage

-- ============================================================================
-- NODE 𝔏𝔖₁: Shift-Commutant Subalgebra Closure, Indirect Co-Occurrence, & Bistochastic Circulants
-- ============================================================================

section ShiftCommutantAndCirculantBistochastic

/--
**Theorem 1 (`𝔏𝔖₁` — `ls1_shift_commutant_subalgebra_and_indirect_cooccurrence_closure`):**
1. **Universal Commutant Subalgebra & Indirect Co-Occurrence Closure:**
   In any associative ring `[Ring B]`, if `K₁` and `K₂` commute with a shift generator `S`
   (`comm S K₁ = 0` and `comm S K₂ = 0`), then `K₁ + K₂`, `K₁ - K₂`, `K₁ * K₂`, the
   2-step indirect co-occurrence square `K₁ * K₁`, and the 3-step cube `K₁ * K₁ * K₁`
   all commute with `S`.
2. **Native Circulant Reconstruction & Translation-Invariant Composition (`ZModFourierBridge`, `TranslationSymmetryEmbeddings`, `LanguageStatisticsTranslationSymmetry`):**
   - Over any `[AddCommGroup G]`, simultaneous translation invariance reconstructs any matrix `M`
     as the native circulant of its zero column:
     `(∀ i j a, M (i + a) (j + a) = M i j) ↔ M = Matrix.circulant (fun i => M i 0)`
     (`matrix_translation_invariant_iff_eq_circulant`).
   - Pair-kernel translation invariance is equivalent to a difference kernel (`translationInvariant_iff_differenceKernel`),
     and difference-kernel matrices preserve simultaneous translation invariance under multiplication
     (`relativeKernelMatrix_mul_translation_invariant`).
3. **Concrete `3 × 3` Circulant Shift Commutation (`blockCirculant3_commutes_cyclicShift`):**
   Over any `[Ring R]`, `blockCirculant3 c0 c1 c2 * cyclicShift3 = cyclicShift3 * blockCirculant3 c0 c1 c2`.
4. **Normalized Circulant Matrices are Algebraically Bistochastic:**
   Over any `[CommRing R]`, `blockCirculant3 c0 c1 c2` is algebraically doubly stochastic
   (`IsAlgebraicDoublyStochastic (blockCirculant3 c0 c1 c2)`) if and only if its generator
   row sums to `1` (`c0 + c1 + c2 = 1`).
-/
theorem ls1_shift_commutant_subalgebra_and_indirect_cooccurrence_closure
    {B : Type*} [Ring B] (S K₁ K₂ : B)
    (h₁ : comm S K₁ = 0) (h₂ : comm S K₂ = 0)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (M_trans : Matrix G G ℂ) (K_pair : G → G → ℂ) (f_rel g_rel : G → ℂ) (a_shift i_pos j_pos : G)
    {R : Type*} [CommRing R] (c0 c1 c2 : R) :
    (comm S (K₁ + K₂) = 0 ∧
     comm S (K₁ - K₂) = 0 ∧
     comm S (K₁ * K₂) = 0 ∧
     comm S (K₁ * K₁) = 0 ∧
     comm S (K₁ * K₁ * K₁) = 0) ∧
    (((∀ i j a, M_trans (i + a) (j + a) = M_trans i j) ↔
        M_trans = Matrix.circulant (fun i => M_trans i 0)) ∧
     ((∀ a x y : G, K_pair (x + a) (y + a) = K_pair x y) ↔
        ∃ c : G → ℂ, ∀ x y, K_pair x y = DifferenceKernel c x y) ∧
     (relativeKernelMatrix f_rel * relativeKernelMatrix g_rel) (i_pos + a_shift) (j_pos + a_shift) =
       (relativeKernelMatrix f_rel * relativeKernelMatrix g_rel) i_pos j_pos) ∧
    blockCirculant3 c0 c1 c2 * cyclicShift3 = cyclicShift3 * blockCirculant3 c0 c1 c2 ∧
    (IsAlgebraicDoublyStochastic (blockCirculant3 c0 c1 c2) ↔ c0 + c1 + c2 = 1) := by
  have hSK1 : S * K₁ = K₁ * S := sub_eq_zero.mp h₁
  have hSK2 : S * K₂ = K₂ * S := sub_eq_zero.mp h₂
  have hAdd : comm S (K₁ + K₂) = 0 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [mul_add, add_mul, hSK1, hSK2, sub_self]
  have hSub : comm S (K₁ - K₂) = 0 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [mul_sub, sub_mul, hSK1, hSK2, sub_self]
  have hMul : comm S (K₁ * K₂) = 0 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    calc
      S * (K₁ * K₂) - K₁ * K₂ * S = (S * K₁) * K₂ - K₁ * (K₂ * S) := by
        rw [← mul_assoc, ← mul_assoc]
      _ = (K₁ * S) * K₂ - K₁ * (S * K₂) := by rw [hSK1, hSK2]
      _ = 0 := by rw [mul_assoc, sub_self]
  have hSq : comm S (K₁ * K₁) = 0 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    calc
      S * (K₁ * K₁) - K₁ * K₁ * S = (S * K₁) * K₁ - K₁ * (K₁ * S) := by
        rw [← mul_assoc, ← mul_assoc]
      _ = (K₁ * S) * K₁ - K₁ * (S * K₁) := by rw [hSK1]
      _ = 0 := by rw [mul_assoc, sub_self]
  have hSK1Sq : S * (K₁ * K₁) = (K₁ * K₁) * S := sub_eq_zero.mp hSq
  have hCube : comm S (K₁ * K₁ * K₁) = 0 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    calc
      S * (K₁ * K₁ * K₁) - K₁ * K₁ * K₁ * S =
          (S * (K₁ * K₁)) * K₁ - (K₁ * K₁) * (K₁ * S) := by noncomm_ring
      _ = ((K₁ * K₁) * S) * K₁ - (K₁ * K₁) * (S * K₁) := by rw [hSK1Sq, hSK1]
      _ = 0 := by noncomm_ring
  have hBistoch : IsAlgebraicDoublyStochastic (blockCirculant3 c0 c1 c2) ↔ c0 + c1 + c2 = 1 := by
    constructor
    · intro hD
      have hRow0 := hD.1 0
      rw [Fin.sum_univ_three] at hRow0
      simpa [blockCirculant3] using hRow0
    · intro hSum
      refine ⟨?_, ?_⟩
      · intro i
        rw [Fin.sum_univ_three]
        fin_cases i <;>
        · simp [blockCirculant3]
          linear_combination hSum
      · intro j
        rw [Fin.sum_univ_three]
        fin_cases j <;>
        · simp [blockCirculant3]
          linear_combination hSum
  exact ⟨⟨hAdd, hSub, hMul, hSq, hCube⟩,
    ⟨matrix_translation_invariant_iff_eq_circulant M_trans,
     translationInvariant_iff_differenceKernel K_pair,
     relativeKernelMatrix_mul_translation_invariant f_rel g_rel a_shift i_pos j_pos⟩,
    blockCirculant3_commutes_cyclicShift c0 c1 c2,
    hBistoch⟩

end ShiftCommutantAndCirculantBistochastic

-- ============================================================================
-- NODE 𝔏𝔖₂: Circulant Fourier Character Diagonalization & Cosine/Sine Circle Degeneracy
-- ============================================================================

section CirculantFourierAndCircleDegeneracy

/-- Four-tap circulant polynomial `c₀ + c₁ S + c₂ S² + c₃ S³` in any ring `[Ring B]`. -/
def circulantPoly4 {B : Type*} [Ring B] (c0 c1 c2 c3 S : B) : B :=
  c0 + c1 * S + c2 * (S * S) + c3 * (S * (S * S))

/--
**Theorem 2 (`𝔏𝔖₂` — `ls2_circulant_fourier_character_diagonalization_and_circle_degeneracy`):**
1. **Native Cyclic Fourier Eigenvectors, DFT Diagonalization, & Centered Inverse-DFT Reconstruction (`ZModFourierBridge`, `CyclicGramGeometry`):**
   - For any `[NeZero N_cyc]`, `κ v_cyc : ZMod N_cyc → ℂ`, and `k_freq : ZMod N_cyc`, the standard
     character `fun i => ZMod.stdAddChar (k_freq * i)` is a nonzero eigenvector of `Matrix.circulant κ`
     with eigenvalue `ZMod.dft κ k_freq` (`circulant_hasEigenvector_stdAddChar`), and the native DFT
     diagonalizes the full circulant action (`dft_circulant_mulVec κ v_cyc`).
   - Two-sided centering `cyclicCentering N_cyc * Matrix.circulant κ * cyclicCentering N_cyc`
     equals `Matrix.circulant (fun a => κ a - (N_cyc : ℂ)⁻¹ * ∑ b, κ b)` (`cyclicCentering_circulant`),
     kills the constant mode (`k_freq = 0`) while preserving every nonzero frequency `ZMod.dft κ k_freq`
     (`centered_circulant_hasEigenvector_stdAddChar`), and reconstructs the centered operator action
     via `ZMod.dft.symm` (`centered_circulant_mulVec_eq_invDFT`).
2. **Universal Circulant Eigenmode Identity:**
   In any commutative ring `[CommRing K]`, if `S` scales a Fourier mode `v` by `ζ` (`S * v = ζ * v`),
   then `circulantPoly4 c0 c1 c2 c3 S * v = (c0 + c1 * ζ + c2 * ζ² + c3 * ζ³) * v`.
3. **Symmetric Kernel Eigenvalue Degeneracy (`μ_k = μ_{N-k}`, `arXiv:2602.15029` §2):**
   When the periodic co-occurrence kernel is symmetric (`c3 = c1`) and the conjugate harmonic
   `ζ_inv` satisfies `ζ * ζ_inv = 1` and `ζ_inv² = ζ²` (as in `ℤ₄` where `(±i)² = -1`),
   the forward eigenvalue `μ_+ = c0 + c1 * ζ + c2 * ζ² + c1 * ζ³` and backward eigenvalue
   `μ_- = c0 + c1 * ζ_inv + c2 * ζ_inv² + c1 * ζ_inv³` are **identically equal**:
   `c0 + c1 * ζ + c2 * ζ ^ 2 + c1 * (ζ * ζ_inv ^ 2) = c0 + c1 * ζ_inv + c2 * ζ_inv ^ 2 + c1 * (ζ_inv * ζ ^ 2)`
   and their difference factors as `c1 * (ζ - ζ_inv) * (1 + ζ ^ 2)`.
4. **Klein Four-Group `V₄` Character Orthogonality & `ℤ₃`/`ℤ₄` Character Annihilation:**
   Bridges directly to `V4GroupFourierTransform.v4Character_pairwise_orthogonality` and
   `ParafermionCondensationGaloisCharacterPoset.cyclic_character_sum_ring_identities`.
-/
theorem ls2_circulant_fourier_character_diagonalization_and_circle_degeneracy
    {N_cyc : ℕ} [NeZero N_cyc] (κ v_cyc : ZMod N_cyc → ℂ) (k_freq : ZMod N_cyc)
    {K : Type*} [CommRing K] (c0 c1 c2 c3 S ζ ζ_inv v : K)
    (hEv : S * v = ζ * v)
    (hInv : ζ * ζ_inv = 1) (hSq : ζ_inv ^ 2 = ζ ^ 2)
    {B : Type*} [Ring B] (Ω U : B)
    (hΩ : Ω * (Ω * Ω) = 1) (hU : U * (U * (U * U)) = 1)
    (i j : Fin 4) :
    (Module.End.HasEigenvector (Matrix.circulant κ).mulVecLin
       (ZMod.dft κ k_freq) (fun idx => ZMod.stdAddChar (k_freq * idx)) ∧
     ZMod.dft (Matrix.circulant κ *ᵥ v_cyc) = ZMod.dft κ * ZMod.dft v_cyc ∧
     cyclicCentering N_cyc * Matrix.circulant κ * cyclicCentering N_cyc =
       Matrix.circulant (fun a => κ a - (N_cyc : ℂ)⁻¹ * ∑ b, κ b) ∧
     Module.End.HasEigenvector
       (cyclicCentering N_cyc * Matrix.circulant κ * cyclicCentering N_cyc).mulVecLin
       (if k_freq = 0 then 0 else ZMod.dft κ k_freq)
       (fun idx => ZMod.stdAddChar (k_freq * idx)) ∧
     (cyclicCentering N_cyc * Matrix.circulant κ * cyclicCentering N_cyc) *ᵥ v_cyc =
       ZMod.dft.symm
         (fun k => (if k = 0 then 0 else ZMod.dft κ k) * ZMod.dft v_cyc k)) ∧
    circulantPoly4 c0 c1 c2 c3 S * v = (c0 + c1 * ζ + c2 * ζ ^ 2 + c3 * ζ ^ 3) * v ∧
    (c0 + c1 * ζ + c2 * ζ ^ 2 + c1 * (ζ * ζ_inv ^ 2) =
       c0 + c1 * ζ_inv + c2 * ζ_inv ^ 2 + c1 * (ζ_inv * ζ ^ 2)) ∧
    (c0 + c1 * ζ + c2 * ζ ^ 2 + c1 * ζ ^ 3 -
       (c0 + c1 * ζ_inv + c2 * ζ_inv ^ 2 + c1 * ζ_inv ^ 3) =
       c1 * (ζ - ζ_inv) * (1 + ζ ^ 2)) ∧
    (∑ g : InfoGeometry.Topology.V4RootSystem.V4Group,
       InfoGeometry.Canonical.V4GroupFourierTransform.v4Character i g *
       InfoGeometry.Canonical.V4GroupFourierTransform.v4Character j g =
       if i = j then 4 else 0) ∧
    ((1 - Ω) * cyclicCharacterSum3 Ω = 0 ∧
     (U * U) * cyclicCharacterSum4 U = cyclicCharacterSum4 U) := by
  have hEv2 : S * (S * v) = ζ ^ 2 * v := by
    calc
      S * (S * v) = S * (ζ * v) := by rw [hEv]
      _ = ζ * (S * v) := by ring
      _ = ζ * (ζ * v) := by rw [hEv]
      _ = ζ ^ 2 * v := by ring
  have hEv3 : S * (S * (S * v)) = ζ ^ 3 * v := by
    calc
      S * (S * (S * v)) = S * (ζ ^ 2 * v) := by rw [hEv2]
      _ = ζ ^ 2 * (S * v) := by ring
      _ = ζ ^ 2 * (ζ * v) := by rw [hEv]
      _ = ζ ^ 3 * v := by ring
  have hPoly :
      circulantPoly4 c0 c1 c2 c3 S * v = (c0 + c1 * ζ + c2 * ζ ^ 2 + c3 * ζ ^ 3) * v := by
    dsimp [circulantPoly4]
    calc
      (c0 + c1 * S + c2 * (S * S) + c3 * (S * (S * S))) * v =
          c0 * v + c1 * (S * v) + c2 * (S * (S * v)) + c3 * (S * (S * (S * v))) := by noncomm_ring
      _ = c0 * v + c1 * (ζ * v) + c2 * (ζ ^ 2 * v) + c3 * (ζ ^ 3 * v) := by
          rw [hEv3, hEv2, hEv]
      _ = (c0 + c1 * ζ + c2 * ζ ^ 2 + c3 * ζ ^ 3) * v := by noncomm_ring
  have hDeg1 :
      c0 + c1 * ζ + c2 * ζ ^ 2 + c1 * (ζ * ζ_inv ^ 2) =
        c0 + c1 * ζ_inv + c2 * ζ_inv ^ 2 + c1 * (ζ_inv * ζ ^ 2) := by
    linear_combination -c2 * hSq + c1 * (ζ_inv - ζ) * hInv
  have hDeg2 :
      c0 + c1 * ζ + c2 * ζ ^ 2 + c1 * ζ ^ 3 -
        (c0 + c1 * ζ_inv + c2 * ζ_inv ^ 2 + c1 * ζ_inv ^ 3) =
        c1 * (ζ - ζ_inv) * (1 + ζ ^ 2) := by
    linear_combination -(c2 + c1 * ζ_inv) * hSq
  have hChar := cyclic_character_sum_ring_identities Ω U hΩ hU
  exact ⟨⟨circulant_hasEigenvector_stdAddChar κ k_freq,
          dft_circulant_mulVec κ v_cyc,
          cyclicCentering_circulant κ,
          centered_circulant_hasEigenvector_stdAddChar κ k_freq,
          centered_circulant_mulVec_eq_invDFT κ v_cyc⟩,
    hPoly, hDeg1, hDeg2,
    InfoGeometry.Canonical.V4GroupFourierTransform.v4Character_pairwise_orthogonality i j,
    ⟨hChar.1, hChar.2.2.2.1⟩⟩

end CirculantFourierAndCircleDegeneracy

-- ============================================================================
-- NODE 𝔏𝔖₃: Gramian Torus Ripple Embedding, FiniteGramFactorization, & Metriplectic Coincidence
-- ============================================================================

section GramianTorusAndMetriplecticCoincidence

/--
**Theorem 3 (`𝔏𝔖₃` — `ls3_gramian_torus_ripple_embedding_and_metriplectic_coincidence`):**
1. **Cyclic Autocorrelation PSD Gram Matrix, Wiener–Khinchin Spectrum, & Real 2D Fourier Coordinates (`CyclicGramGeometry`):**
   - For any `[NeZero N_cyc]` and complex feature vector `g_feat : ZMod N_cyc → ℂ`,
     `Matrix.circulant (cyclicAutocorrelation g_feat) = Matrix.circulant g_feat * (Matrix.circulant g_feat)ᴴ`
     (`cyclicAutocorrelation_gram`), which is positive semidefinite (`cyclicAutocorrelation_posSemidef`),
     with Wiener–Khinchin power spectrum `ZMod.dft (cyclicAutocorrelation g_feat) k_freq = (Complex.normSq (ZMod.dft g_feat k_freq) : ℂ)`
     (`dft_cyclicAutocorrelation_eq_normSq`) and centered Gram factorization
     `cyclicCentering N_cyc * Matrix.circulant (cyclicAutocorrelation g_feat) * cyclicCentering N_cyc = (cyclicCentering N_cyc * Matrix.circulant g_feat) * (cyclicCentering N_cyc * Matrix.circulant g_feat)ᴴ`.
   - For the explicit real 2D Fourier coordinate matrix `cyclicRealFourierPair a_scale k_freq : Matrix (ZMod N_cyc) (Fin 2) ℝ`,
     its Gram matrix is the circulant `Matrix.circulant (fun i => a_scale ^ 2 * (ZMod.stdAddChar (k_freq * i)).re)`
     (`cyclicRealFourierPair_gram_eq_circulant`) with constant diagonal `a_scale ^ 2` (`cyclicRealFourierPair_gram_diag`).
2. **Two-Harmonic Clifford Torus / Helical Ripple Gramian (`arXiv:2602.15029` §§2–3):**
   Over any `[CommRing K]`, when token `i` is embedded into `K⁴` by two Fourier circle pairs
   `w(i) = (r₁ c₁ᵢ, r₁ s₁ᵢ, r₂ c₂ᵢ, r₂ s₂ᵢ)` satisfying `c₁ᵢ² + s₁ᵢ² = 1`, `c₂ᵢ² + s₂ᵢ² = 1`,
   and the cosine addition laws `c₁ᵢ c₁ⱼ + s₁ᵢ s₁ⱼ = c₁_diff`, `c₂ᵢ c₂ⱼ + s₂ᵢ s₂ⱼ = c₂_diff`:
   - The Gramian inner product `⟨w(i), w(j)⟩` is purely translation-invariant:
     `(r₁ * c₁ᵢ) * (r₁ * c₁ⱼ) + (r₁ * s₁ᵢ) * (r₁ * s₁ⱼ) + (r₂ * c₂ᵢ) * (r₂ * c₂ⱼ) + (r₂ * s₂ᵢ) * (r₂ * s₂ⱼ) = r₁ ^ 2 * c₁_diff + r₂ ^ 2 * c₂_diff`,
   - The self-Gramian squared radius `⟨w(i), w(i)⟩` is constant across all tokens on the Clifford torus:
     `(r₁ * c₁ᵢ) ^ 2 + (r₁ * s₁ᵢ) ^ 2 + (r₂ * c₂ᵢ) ^ 2 + (r₂ * s₂ᵢ) ^ 2 = r₁ ^ 2 + r₂ ^ 2`.
3. **Real & Complex Matrix Gramian Identities (`FiniteGramFactorization`, `PlabicGramEigenvectorTransport`, `PeirceCoupling`):**
   - `(∑ i, ∑ j, v i * gramMatrix B_mat i j * v j) = ∑ k : m, (∑ i, v i * B_mat i k) ^ 2 ≥ 0`,
   - `Matrix.charpoly (A_sqᴴ * A_sq) = Matrix.charpoly (A_sq * A_sqᴴ)` (`gram_charpoly_eq_of_square`),
   - `(A_sq * A_sqᴴ + A_sqᴴ * A_sq).PosSemidef` (`gramSum_posSemidef`).
4. **Non-Commutative Metriplectic Out/In Gramian Coincidence (`gramianOut_expand`, `gramianIn_expand`):**
   In any `[Ring B]`, decomposing an asymmetric co-occurrence operator into symmetric `S` and
   skew `K` parts (`C_+ = S + K`, `C_- = S - K`) yields
   `gramianOut S K - gramianIn S K = -(comm S K + comm S K)`.
-/
theorem ls3_gramian_torus_ripple_embedding_and_metriplectic_coincidence
    {N_cyc : ℕ} [NeZero N_cyc] (g_feat : ZMod N_cyc → ℂ) (a_scale : ℝ) (k_freq idx_cyc : ZMod N_cyc)
    {K : Type*} [CommRing K]
    (r1 r2 c1i s1i c1j s1j c1_diff c2i s2i c2j s2j c2_diff : K)
    (hCircle1 : c1i ^ 2 + s1i ^ 2 = 1)
    (hCircle2 : c2i ^ 2 + s2i ^ 2 = 1)
    (hCos1 : c1i * c1j + s1i * s1j = c1_diff)
    (hCos2 : c2i * c2j + s2i * s2j = c2_diff)
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (B_mat : Matrix n m ℝ) (v : n → ℝ) (A_sq : Matrix n n ℂ)
    {B : Type*} [Ring B] (S_op K_op : B) :
    (Matrix.circulant (cyclicAutocorrelation g_feat) =
       Matrix.circulant g_feat * (Matrix.circulant g_feat)ᴴ ∧
     (Matrix.circulant (cyclicAutocorrelation g_feat)).PosSemidef ∧
     ZMod.dft (cyclicAutocorrelation g_feat) k_freq =
       (Complex.normSq (ZMod.dft g_feat k_freq) : ℂ) ∧
     cyclicCentering N_cyc * Matrix.circulant (cyclicAutocorrelation g_feat) * cyclicCentering N_cyc =
       (cyclicCentering N_cyc * Matrix.circulant g_feat) *
         (cyclicCentering N_cyc * Matrix.circulant g_feat)ᴴ ∧
     cyclicRealFourierPair a_scale k_freq * (cyclicRealFourierPair a_scale k_freq).transpose =
       Matrix.circulant (fun i => a_scale ^ 2 * (ZMod.stdAddChar (k_freq * i)).re) ∧
     (cyclicRealFourierPair a_scale k_freq * (cyclicRealFourierPair a_scale k_freq).transpose)
       idx_cyc idx_cyc = a_scale ^ 2) ∧
    ((r1 * c1i) * (r1 * c1j) + (r1 * s1i) * (r1 * s1j) +
       (r2 * c2i) * (r2 * c2j) + (r2 * s2i) * (r2 * s2j) =
       r1 ^ 2 * c1_diff + r2 ^ 2 * c2_diff ∧
     (r1 * c1i) ^ 2 + (r1 * s1i) ^ 2 + (r2 * c2i) ^ 2 + (r2 * s2i) ^ 2 =
       r1 ^ 2 + r2 ^ 2) ∧
    ((∑ i, ∑ j, v i * InfoGeometry.Krein.FiniteGramFactorization.gramMatrix B_mat i j * v j) =
       ∑ k : m, (∑ i, v i * B_mat i k) ^ 2 ∧
     0 ≤ ∑ i, ∑ j, v i * InfoGeometry.Krein.FiniteGramFactorization.gramMatrix B_mat i j * v j ∧
     Matrix.charpoly (A_sq.conjTranspose * A_sq) = Matrix.charpoly (A_sq * A_sq.conjTranspose) ∧
     (A_sq * A_sqᴴ + A_sqᴴ * A_sq).PosSemidef) ∧
    (gramianOut S_op K_op = S_op * S_op - K_op * K_op - comm S_op K_op ∧
     gramianIn S_op K_op = S_op * S_op - K_op * K_op + comm S_op K_op ∧
     gramianOut S_op K_op - gramianIn S_op K_op = -(comm S_op K_op + comm S_op K_op)) := by
  have hGramShift :
      (r1 * c1i) * (r1 * c1j) + (r1 * s1i) * (r1 * s1j) +
        (r2 * c2i) * (r2 * c2j) + (r2 * s2i) * (r2 * s2j) =
        r1 ^ 2 * c1_diff + r2 ^ 2 * c2_diff := by
    linear_combination r1 ^ 2 * hCos1 + r2 ^ 2 * hCos2
  have hGramNorm :
      (r1 * c1i) ^ 2 + (r1 * s1i) ^ 2 + (r2 * c2i) ^ 2 + (r2 * s2i) ^ 2 =
        r1 ^ 2 + r2 ^ 2 := by
    linear_combination r1 ^ 2 * hCircle1 + r2 ^ 2 * hCircle2
  exact ⟨⟨cyclicAutocorrelation_gram g_feat,
          cyclicAutocorrelation_posSemidef g_feat,
          dft_cyclicAutocorrelation_eq_normSq g_feat k_freq,
          centered_cyclicAutocorrelation_gram g_feat,
          cyclicRealFourierPair_gram_eq_circulant a_scale k_freq,
          cyclicRealFourierPair_gram_diag a_scale k_freq idx_cyc⟩,
    ⟨hGramShift, hGramNorm⟩,
    ⟨InfoGeometry.Krein.FiniteGramFactorization.gramMatrix_quadratic_eq_sum_sq B_mat v,
     InfoGeometry.Krein.FiniteGramFactorization.gramMatrix_quadratic_nonneg B_mat v,
     gram_charpoly_eq_of_square A_sq,
     gramSum_posSemidef A_sq⟩,
    ⟨gramianOut_expand S_op K_op,
     gramianIn_expand S_op K_op,
     normalcyDefect_eq_neg_two_comm S_op K_op⟩⟩

end GramianTorusAndMetriplecticCoincidence

-- ============================================================================
-- NODE 𝔏𝔖₄: Open-Boundary Toeplitz vs. Periodic Circulant Commutator Defect & Peirce Leakage
-- ============================================================================

section ToeplitzBoundaryDefectAndPeirceLeakage

/-- Symmetric `3 × 3` Toeplitz matrix `T(t₀, t₁, t₂) = !![t₀, t₁, t₂; t₁, t₀, t₁; t₂, t₁, t₀]`. -/
def symToeplitz3 {R : Type*} (t0 t1 t2 : R) : Matrix (Fin 3) (Fin 3) R :=
  !![t0, t1, t2;
     t1, t0, t1;
     t2, t1, t0]

/-- Boundary commutator pattern `B₃ = !![1, 0, 0; -1, 0, 0; 0, 1, -1]`. -/
def toeplitzBoundaryDefect3 {R : Type*} [Ring R] : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     -1, 0, 0;
     0, 1, -1]

/--
Exact commutator between the open-boundary symmetric Toeplitz matrix `symToeplitz3 t0 t1 t2`
and the periodic shift `cyclicShift3`:
`symToeplitz3 t0 t1 t2 * cyclicShift3 - cyclicShift3 * symToeplitz3 t0 t1 t2 = (t2 - t1) • toeplitzBoundaryDefect3`.
-/
theorem symToeplitz3_comm_cyclicShift3 {R : Type*} [CommRing R] (t0 t1 t2 : R) :
    symToeplitz3 t0 t1 t2 * cyclicShift3 - cyclicShift3 * symToeplitz3 t0 t1 t2 =
      (t2 - t1) • toeplitzBoundaryDefect3 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.smul_apply,
    Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [symToeplitz3, cyclicShift3, toeplitzBoundaryDefect3]

/-- Explicit non-commutativity witness: open-boundary `symToeplitz3 (0 : ℤ) 0 1` and `cyclicShift3` do not commute. -/
theorem symToeplitz3_mul_cyclicShift3_ne :
    symToeplitz3 (0 : ℤ) 0 1 * cyclicShift3 ≠ cyclicShift3 * symToeplitz3 (0 : ℤ) 0 1 := by
  intro hEq
  have h00 := congrFun (congrFun hEq 0) 0
  revert h00
  decide

/--
**Theorem 4 (`𝔏𝔖₄` — `ls4_toeplitz_open_boundary_commutator_defect_and_peirce_corner_leakage`):**
1. **Open-Boundary Toeplitz vs. Periodic Circulant Cut (`arXiv:2602.15029` §2.2):**
   - `symToeplitz3 t0 t1 t2 * cyclicShift3 - cyclicShift3 * symToeplitz3 t0 t1 t2 = (t2 - t1) • toeplitzBoundaryDefect3`.
   - `symToeplitz3 t0 t1 t2` commutes with `cyclicShift3` **if and only if** `t2 = t1`
     (in which case `symToeplitz3 t0 t1 t1 = blockCirculant3 t0 t1 t1`).
2. **Causal Nilpotent Shift Boundary Defect (`causalToeplitz3_commute_and_shift_boundary_defect`):**
   - Any two lower-triangular causal Toeplitz matrices `causalToeplitz3 a0 a1 a2` and
     `causalToeplitz3 b0 b1 b2` commute, while `[causalShift3 R, (causalShift3 R)ᵀ] = !![-1, 0, 0; 0, 0, 0; 0, 0, 1]`.
3. **Peirce Corner Coherence Defect (`coherator_weak_vs_strict_socratic_defect`):**
   In any `[Ring B]` with `hP : P * P = P`, compressing `F²` vs `(P F P)²` leaves the exact
   off-diagonal corner leakage `coherenceDefect P F = conePlus P F * coneMinus P F`.
-/
theorem ls4_toeplitz_open_boundary_commutator_defect_and_peirce_corner_leakage
    {R : Type*} [CommRing R] (t0 t1 t2 a0 a1 a2 b0 b1 b2 : R)
    {B : Type*} [Ring B] (P F : B) (hP : P * P = P) :
    (symToeplitz3 t0 t1 t2 * cyclicShift3 - cyclicShift3 * symToeplitz3 t0 t1 t2 =
       (t2 - t1) • toeplitzBoundaryDefect3 ∧
     (symToeplitz3 t0 t1 t2 * cyclicShift3 = cyclicShift3 * symToeplitz3 t0 t1 t2 ↔ t2 = t1) ∧
     symToeplitz3 t0 t1 t1 = blockCirculant3 t0 t1 t1) ∧
    (causalToeplitz3 a0 a1 a2 * causalToeplitz3 b0 b1 b2 =
       causalToeplitz3 b0 b1 b2 * causalToeplitz3 a0 a1 a2 ∧
     causalShift3 R * (causalShift3 R).transpose -
       (causalShift3 R).transpose * causalShift3 R =
       !![(-1 : R), 0, 0; 0, 0, 0; 0, 0, 1]) ∧
    coherenceDefect P F = conePlus P F * coneMinus P F := by
  have hCommId := symToeplitz3_comm_cyclicShift3 t0 t1 t2
  have hCommIff :
      symToeplitz3 t0 t1 t2 * cyclicShift3 = cyclicShift3 * symToeplitz3 t0 t1 t2 ↔ t2 = t1 := by
    constructor
    · intro hEq
      have hSub : symToeplitz3 t0 t1 t2 * cyclicShift3 - cyclicShift3 * symToeplitz3 t0 t1 t2 = 0 :=
        sub_eq_zero.mpr hEq
      rw [hCommId] at hSub
      have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) hSub
      simpa [toeplitzBoundaryDefect3, sub_eq_zero] using h00
    · intro hEq
      apply sub_eq_zero.mp
      rw [hCommId, hEq, sub_self, zero_smul]
  have hCircEq : symToeplitz3 t0 t1 t1 = blockCirculant3 t0 t1 t1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hCausal := causalToeplitz3_commute_and_shift_boundary_defect a0 a1 a2 b0 b1 b2
  exact ⟨⟨hCommId, hCommIff, hCircEq⟩,
    ⟨hCausal.2.1, hCausal.2.2⟩,
    (coherator_weak_vs_strict_socratic_defect P F hP).1⟩

end ToeplitzBoundaryDefectAndPeirceLeakage

-- ============================================================================
-- NODE 𝔏𝔖₅: Birkhoff Bistochastic Permutations, Stochastic Grammar Drazin Wall, & Clifford MoE
-- ============================================================================

section BirkhoffStochasticGrammarAndCliffordMoE

/--
**Theorem 5 (`𝔏𝔖₅` — `ls5_birkhoff_bistochastic_permutation_polytope_and_stochastic_grammar_moe`):**
1. **Birkhoff–von Neumann Permutation Decomposition & Operator-Norm Contraction (`BirkhoffRouting`):**
   Every doubly stochastic matrix `W ∈ BirkhoffPolytope n` decomposes as a convex combination
   of permutation matrices `∑ σ : Equiv.Perm (Fin n), w σ • σ.permMatrix ℝ = W` (`w σ ≥ 0`, `∑ w σ = 1`)
   and is an operator-norm contraction `‖W‖ ≤ 1`.
2. **Algebraic Bistochastic Multiplicative Closure (`GibsonBasicDoublyStochastic.doublyStochastic_mul`):**
   If `A, B : Matrix (Fin n) (Fin n) R` are algebraically doubly stochastic, so is `A * B`.
3. **Stochastic Grammar Drazin-Index-1 Semisimplicity Wall & Born Amplitude Normalization:**
   - Any row-stochastic transition matrix `P ∈ Matrix.rowStochastic ℝ (Fin n)` has no nonzero
     length-2 Jordan chain at eigenvalue `1`: `(1 - P) *ᵥ x = y → (1 - P) *ᵥ y = 0 → y = 0`
     (`MarkovDrazin.no_length_two_generalized_fixed_vector`).
   - For any `T : StochasticTransitionMatrix n`, its Born square-root amplitude rows are
     `L²`-normalized (`∑ j, (T.amplitudeMatrix i j)² = 1`).
4. **Clifford `Cl(5,5)` Hypercube Mixture-of-Experts Partition of Unity & Marginalization (`Cl55PeirceMoERouting`):**
   For any commuting split involution pair `P_split : CommutingSplitPair A_alg`, the 4 hypercube
   expert projectors sum to `1` and marginalize over the second bit to `peircePlus P_split.K1`:
   `expertPlusPlus P_split + expertPlusMinus P_split = peircePlus P_split.K1`,
   `expertPlusPlus P_split + expertPlusMinus P_split + expertMinusPlus P_split + expertMinusMinus P_split = 1`,
   and the logistic MoE gate satisfies `sigmoid x + sigmoid (-x) = 1`.
--/
theorem ls5_birkhoff_bistochastic_permutation_polytope_and_stochastic_grammar_moe
    {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hW : BirkhoffRouting.IsDoublyStochastic W)
    {R : Type*} [CommSemiring R] {A_ds B_ds : Matrix (Fin n) (Fin n) R}
    (hA_ds : IsAlgebraicDoublyStochastic A_ds) (hB_ds : IsAlgebraicDoublyStochastic B_ds)
    (P_stoch : Matrix (Fin n) (Fin n) ℝ) (hP_stoch : P_stoch ∈ Matrix.rowStochastic ℝ (Fin n))
    (x_jord y_jord : Fin n → ℝ)
    (hxy : (1 - P_stoch) *ᵥ x_jord = y_jord) (hyy : (1 - P_stoch) *ᵥ y_jord = 0)
    (T_gram : InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge.StochasticTransitionMatrix n)
    (i_row : Fin n)
    {A_alg : Type*} [Ring A_alg] [Algebra ℝ A_alg]
    (P_split : InfoGeometry.Clifford.Cl55PeirceMoERouting.CommutingSplitPair A_alg)
    (z_logit : ℝ) :
    ((∃ w : Equiv.Perm (Fin n) → ℝ,
        (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧ ∑ σ, w σ • σ.permMatrix ℝ = W) ∧
     ‖W‖ ≤ 1) ∧
    IsAlgebraicDoublyStochastic (A_ds * B_ds) ∧
    (y_jord = 0 ∧
     ∑ j : Fin n, (T_gram.amplitudeMatrix i_row j) ^ 2 = 1) ∧
    (InfoGeometry.Clifford.Cl55PeirceMoERouting.expertPlusPlus P_split +
       InfoGeometry.Clifford.Cl55PeirceMoERouting.expertPlusMinus P_split =
       InfoGeometry.Clifford.Cl55PeirceMoERouting.peircePlus P_split.K1 ∧
     InfoGeometry.Clifford.Cl55PeirceMoERouting.expertPlusPlus P_split +
       InfoGeometry.Clifford.Cl55PeirceMoERouting.expertPlusMinus P_split +
       InfoGeometry.Clifford.Cl55PeirceMoERouting.expertMinusPlus P_split +
       InfoGeometry.Clifford.Cl55PeirceMoERouting.expertMinusMinus P_split = (1 : A_alg) ∧
     InfoGeometry.Clifford.Cl55PeirceMoERouting.sigmoid z_logit +
       InfoGeometry.Clifford.Cl55PeirceMoERouting.sigmoid (-z_logit) = 1) := by
  have hMarginal :
      InfoGeometry.Clifford.Cl55PeirceMoERouting.expertPlusPlus P_split +
        InfoGeometry.Clifford.Cl55PeirceMoERouting.expertPlusMinus P_split =
        InfoGeometry.Clifford.Cl55PeirceMoERouting.peircePlus P_split.K1 := by
    dsimp [InfoGeometry.Clifford.Cl55PeirceMoERouting.expertPlusPlus,
      InfoGeometry.Clifford.Cl55PeirceMoERouting.expertPlusMinus]
    rw [← mul_add, InfoGeometry.Clifford.Cl55PeirceMoERouting.peirce_sum_one P_split.K2, mul_one]
  exact ⟨⟨BirkhoffRouting.birkhoff_von_neumann_decomposition W hW,
          BirkhoffRouting.doubly_stochastic_is_contraction hW⟩,
    doublyStochastic_mul hA_ds hB_ds,
    ⟨InfoGeometry.QuantumContext.MarkovDrazin.no_length_two_generalized_fixed_vector
       P_stoch hP_stoch x_jord y_jord hxy hyy,
     T_gram.amplitude_row_l2_normalization i_row⟩,
    ⟨hMarginal,
     InfoGeometry.Clifford.Cl55PeirceMoERouting.hypercube_expert_sum_one P_split,
     InfoGeometry.Clifford.Cl55PeirceMoERouting.sigmoid_add_sigmoid_neg z_logit⟩⟩

end BirkhoffStochasticGrammarAndCliffordMoE

-- ============================================================================
-- NODE 𝔏𝔖₆: Recursive Tensor-Peirce Centralizer Homogenization & Monarch/Sylvester Tower
-- ============================================================================

section RecursiveTensorPeirceAndCentralizers

/--
**Theorem 6 (`𝔏𝔖₆` — `ls6_recursive_tensor_peirce_centralizer_homogenization_and_monarch_tower`):**
1. **`n`-Stage Recursive Tensor-Peirce Bijection (`toTensorTower_ofTensorTower`, `ofTensorTower_toTensorTower`):**
   For every depth `k : ℕ`, `toTensorTower k (ofTensorTower k T) = T` and
   `ofTensorTower k (toTensorTower k M) = M`.
2. **Centralizer-Homogenized Block Extraction & Trace-Sector Sum (`fromBlocks_pi_homogenization`):**
   On `Matrix.fromBlocks M00 M01 M10 M11 : Matrix (m ⊕ m) (m ⊕ m) R`, the four homogenized
   Peirce projections `pi00`, `pi01`, `pi10`, `pi11` embed each `m × m` block `M_{ab}` into
   the outer `2 × 2` centralizer `Matrix.fromBlocks M_{ab} 0 0 M_{ab} = I₂ ⊗ M_{ab}`, and the
   homogenized diagonal sum `pi00 ... + pi11 ...` equals `Matrix.fromBlocks (M00 + M11) 0 0 (M00 + M11)`.
3. **Doubled Sylvester Tensor-Sheet Commutant Duality (`DoubledSylvester.commutant_commutes`):**
   Left-sheet operators `sheet1 A_s = A_s ⊗ I_N` and right-sheet operators `sheet2 B_s = I_N ⊗ B_s`
   commute identically (`DoubledSylvester.bracket (sheet1 A_s) (sheet2 B_s) = 0`).
4. **Monarch Two-Stage Product-Index Rank-1 Slice (`routingSlice_monarch`):**
   Fixing fine output `a` and coarse input `j`, `routingSlice (monarch L R) a j` factors as the
   outer product `Matrix.vecMulVec (fun i => L a i j) (fun b => R j a b)`.
5. **Nilpotent Centralizer Differential (`centralizerDifferentialHom_comp_self`):**
   On the metric centralizer `{X : B // genV P A C * X = X * genV P A C}`, the Peirce graded
   derivation squares to zero (`(centralizerDifferentialHom hP A C).comp (centralizerDifferentialHom hP A C) = 0`).
-/
theorem ls6_recursive_tensor_peirce_centralizer_homogenization_and_monarch_tower
    {R : Type*} [CommRing R] (k : ℕ)
    (T_tower : TensorTower R k) (M_flat : FlatMat R k)
    {m : Type*} [Fintype m] [DecidableEq m]
    (M00 M01 M10 M11 : Matrix m m R)
    {N : ℕ} (A_s B_s : Matrix (Fin N) (Fin N) R)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (L_mon : J → Matrix I I R) (R_mon : I → Matrix J J R) (a_idx : J) (j_idx : I)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A_op C_op : B) :
    (toTensorTower k (ofTensorTower k T_tower) = T_tower ∧
     ofTensorTower k (toTensorTower k M_flat) = M_flat) ∧
    ((pi00 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
        Matrix.fromBlocks M00 0 0 M00 ∧
      pi01 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
        Matrix.fromBlocks M01 0 0 M01 ∧
      pi10 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
        Matrix.fromBlocks M10 0 0 M10 ∧
      pi11 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
        Matrix.fromBlocks M11 0 0 M11) ∧
     pi00 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) +
       pi11 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
       Matrix.fromBlocks (M00 + M11) 0 0 (M00 + M11)) ∧
    DoubledSylvester.bracket (DoubledSylvester.sheet1 A_s) (DoubledSylvester.sheet2 B_s) = 0 ∧
    routingSlice (monarch L_mon R_mon) a_idx j_idx =
      Matrix.vecMulVec (fun i => L_mon a_idx i j_idx) (fun b => R_mon j_idx a_idx b) ∧
    (centralizerDifferentialHom hP A_op C_op).comp (centralizerDifferentialHom hP A_op C_op) = 0 := by
  have hHomog := fromBlocks_pi_homogenization M00 M01 M10 M11
  have hDiagSum :
      pi00 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) +
        pi11 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
        Matrix.fromBlocks (M00 + M11) 0 0 (M00 + M11) := by
    rw [hHomog.1, hHomog.2.2.2, Matrix.fromBlocks_add, add_zero]
  exact ⟨⟨toTensorTower_ofTensorTower k T_tower,
          ofTensorTower_toTensorTower k M_flat⟩,
    ⟨hHomog, hDiagSum⟩,
    DoubledSylvester.commutant_commutes A_s B_s,
    routingSlice_monarch L_mon R_mon a_idx j_idx,
    centralizerDifferentialHom_comp_self hP A_op C_op⟩

end RecursiveTensorPeirceAndCentralizers

-- ============================================================================
-- NODE 𝔏𝔖₇: Master Coagulation — Language Symmetry, Yangian RTT, Birkhoff, & Peirce Spine
-- ============================================================================

section MasterLanguageSymmetryYangianPeirceSynthesis

/--
**Theorem 7 (`𝔏𝔖₇` — `ls7_language_symmetry_yangian_peirce_birkhoff_master_coagulation`):**
Unifies all 7 stages (`𝔏𝔖₁ ≺ ⋯ ≺ 𝔏𝔖₇`) of the Language Symmetry, Circulant/Toeplitz Spectral
Geometry, Birkhoff Bistochastic Polytope, Gramian Torus Ripple, Yangian Monodromy, & Recursive
Tensor-Peirce Centralizer Poset:
1. **Shift-Commutant Closure & Native Circulant Reconstruction (`𝔏𝔖₁`):**
   `comm S K₁ = 0 → comm S K₂ = 0 → comm S (K₁ * K₂) = 0 ∧ comm S (K₁ * K₁) = 0`, and
   `(∀ i j a, M_cyc (i + a) (j + a) = M_cyc i j) ↔ M_cyc = Matrix.circulant (fun i => M_cyc i 0)`.
2. **Centered Circulant Inverse-DFT Reconstruction, Autocorrelation PSD Gram, & Real 2D Fourier Coordinates (`𝔏𝔖₂`–`𝔏𝔖₃`):**
   `(cyclicCentering N_cyc * Matrix.circulant κ * cyclicCentering N_cyc) *ᵥ v_cyc = ZMod.dft.symm (fun k => (if k = 0 then 0 else ZMod.dft κ k) * ZMod.dft v_cyc k)`,
   `(Matrix.circulant (cyclicAutocorrelation g_feat)).PosSemidef`,
   `ZMod.dft (cyclicAutocorrelation g_feat) k_freq = (Complex.normSq (ZMod.dft g_feat k_freq) : ℂ)`, and
   `(cyclicRealFourierPair a_scale k_freq * (cyclicRealFourierPair a_scale k_freq).transpose) idx_cyc idx_cyc = a_scale ^ 2`.
3. **Open-Boundary Toeplitz vs. Periodic Circulant Cut (`𝔏𝔖₄`):**
   `symToeplitz3 t0 t1 t2 * cyclicShift3 = cyclicShift3 * symToeplitz3 t0 t1 t2 ↔ t2 = t1`.
4. **Birkhoff Bistochastic Permutation Convex Hull (`𝔏𝔖₅`):**
   `IsDoublyStochastic W → ∃ w, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧ ∑ σ, w σ • σ.permMatrix ℝ = W`.
5. **Recursive Tensor-Peirce Bijection & Centralizer Differential (`𝔏𝔖₆`):**
   `ofTensorTower k (toTensorTower k M_flat) = M_flat` and
   `(centralizerDifferentialHom hP A_op C_op).comp (centralizerDifferentialHom hP A_op C_op) = 0`.
6. **Yangian RTT Commutator & Quantum Determinant Centrality (`𝔏𝔖₇`):**
   `laxBlockA u θ η * laxBlockD (u - η) θ η - laxBlockB η * laxBlockC η = ((u - θ) ^ 2 - η ^ 2) • 1`.
7. **Peirce–Bruhat Counterterm Idempotency (`𝔏𝔖₇`):**
   For `P_hat := P + genPhi P A_op C_op - genSig P A_op C_op - genV P A_op C_op * conePlus P A_op`,
   `P_hat * P_hat = P_hat` and `evenGrade P (cornerConjugation P A_op C_op (P * Z_op * P) - P * Z_op * P) = comm (coneMinus P C_op * (P * Z_op * P)) (conePlus P A_op)`.
-/
theorem ls7_language_symmetry_yangian_peirce_birkhoff_master_coagulation
    {N_cyc : ℕ} [NeZero N_cyc]
    (M_cyc : Matrix (ZMod N_cyc) (ZMod N_cyc) ℂ) (κ v_cyc g_feat : ZMod N_cyc → ℂ)
    (a_scale : ℝ) (k_freq idx_cyc : ZMod N_cyc)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P)
    (S K₁ K₂ A_op C_op Z_op : B)
    (h₁ : comm S K₁ = 0) (h₂ : comm S K₂ = 0)
    {R : Type*} [CommRing R] (t0 t1 t2 u θ η : R)
    (k : ℕ) (M_flat : FlatMat R k)
    {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hW : BirkhoffRouting.IsDoublyStochastic W) :
    let P_hat := P + genPhi P A_op C_op - genSig P A_op C_op - genV P A_op C_op * conePlus P A_op
    ((comm S (K₁ * K₂) = 0 ∧ comm S (K₁ * K₁) = 0) ∧
     ((∀ i j a, M_cyc (i + a) (j + a) = M_cyc i j) ↔
        M_cyc = Matrix.circulant (fun i => M_cyc i 0))) ∧
    ((cyclicCentering N_cyc * Matrix.circulant κ * cyclicCentering N_cyc) *ᵥ v_cyc =
       ZMod.dft.symm
         (fun k_mode => (if k_mode = 0 then 0 else ZMod.dft κ k_mode) * ZMod.dft v_cyc k_mode) ∧
     (Matrix.circulant (cyclicAutocorrelation g_feat)).PosSemidef ∧
     ZMod.dft (cyclicAutocorrelation g_feat) k_freq =
       (Complex.normSq (ZMod.dft g_feat k_freq) : ℂ) ∧
     (cyclicRealFourierPair a_scale k_freq * (cyclicRealFourierPair a_scale k_freq).transpose)
       idx_cyc idx_cyc = a_scale ^ 2) ∧
    (symToeplitz3 t0 t1 t2 * cyclicShift3 = cyclicShift3 * symToeplitz3 t0 t1 t2 ↔ t2 = t1) ∧
    (∃ w : Equiv.Perm (Fin n) → ℝ,
       (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧ ∑ σ, w σ • σ.permMatrix ℝ = W) ∧
    (ofTensorTower k (toTensorTower k M_flat) = M_flat ∧
     (centralizerDifferentialHom hP A_op C_op).comp (centralizerDifferentialHom hP A_op C_op) = 0) ∧
    laxBlockA u θ η * laxBlockD (u - η) θ η - laxBlockB η * laxBlockC η =
      ((u - θ) ^ 2 - η ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) ∧
    (P_hat * P_hat = P_hat ∧
     evenGrade P (cornerConjugation P A_op C_op (P * Z_op * P) - P * Z_op * P) =
       comm (coneMinus P C_op * (P * Z_op * P)) (conePlus P A_op)) := by
  intro P_hat
  have hLS1 := ls1_shift_commutant_subalgebra_and_indirect_cooccurrence_closure
    S K₁ K₂ h₁ h₂ M_cyc (fun i j => M_cyc i j) κ g_feat k_freq idx_cyc idx_cyc t0 t1 t2
  have hLS4 := ls4_toeplitz_open_boundary_commutator_defect_and_peirce_corner_leakage
    t0 t1 t2 t0 t1 t2 t0 t1 t2 P Z_op hP
  have hYang := lax_rtt_and_quantum_determinant u 0 θ η
  have hPhat : P_hat * P_hat = P_hat := by
    dsimp only [P_hat]
    peirce_nf hP
  exact ⟨⟨⟨hLS1.1.2.2.1, hLS1.1.2.2.2.1⟩,
          matrix_translation_invariant_iff_eq_circulant M_cyc⟩,
    ⟨centered_circulant_mulVec_eq_invDFT κ v_cyc,
     cyclicAutocorrelation_posSemidef g_feat,
     dft_cyclicAutocorrelation_eq_normSq g_feat k_freq,
     cyclicRealFourierPair_gram_diag a_scale k_freq idx_cyc⟩,
    hLS4.1.2.1,
    BirkhoffRouting.birkhoff_von_neumann_decomposition W hW,
    ⟨ofTensorTower_toTensorTower k M_flat,
     centralizerDifferentialHom_comp_self hP A_op C_op⟩,
    hYang.2.2,
    ⟨hPhat, (cornerConjugation_even_shift_eq_reverse_commutator P A_op C_op Z_op hP).1⟩⟩

/--
**Theorem 1B (`𝔏𝔖₁`–`𝔏𝔖₃` — `helper_word_ablation_resilience_and_shift_equivariance`):**
Resolves the Ablation Paradox (`arXiv:2602.15029`, Sec. 4.1.1 & App. C.1):
Let `P * P = P` be the projector onto the target concepts (e.g., the 12 calendar months) and
`1 - P` be the projector onto the helper vocabulary (seasonal words in the corpus):
1. **Universal Socratic Two-Hop Gramian Identity:**
   `P * (M * M) * P - (P * M * P) * (P * M * P) = conePlus P M * coneMinus P M`.
2. **Ablation Recovery (`P * M * P = 0`):**
   When all direct co-occurrences between target words are deleted (`h_ablated : P * M * P = 0`),
   the projected Gram matrix `P * (M * M) * P` equals the helper-word excursion product
   `conePlus P M * coneMinus P M`.
3. **Two-Subspace Shift-Equivariant Helper Bridge (`T_P N_+ = N_+ T_H` & `T_H N_- = N_- T_P`):**
   Whenever the helper couplings intertwine the target shift `T_P` and helper shift `T_H`
   (`T_P * conePlus P M = conePlus P M * T_H` and `T_H * coneMinus P M = coneMinus P M * T_P`),
   the two-hop helper Gramian commutes with `T_P`:
   `T_P * (conePlus P M * coneMinus P M) = (conePlus P M * coneMinus P M) * T_P` and
   `comm T_P (conePlus P M * coneMinus P M) = 0`.
-/
theorem helper_word_ablation_resilience_and_shift_equivariance
    {B : Type*} [Ring B] (P M T_P T_H : B) (hP : P * P = P)
    (h_ablated : P * M * P = 0)
    (hT_plus : T_P * conePlus P M = conePlus P M * T_H)
    (hT_minus : T_H * coneMinus P M = coneMinus P M * T_P) :
    P * (M * M) * P - (P * M * P) * (P * M * P) = conePlus P M * coneMinus P M ∧
    P * (M * M) * P = conePlus P M * coneMinus P M ∧
    T_P * (conePlus P M * coneMinus P M) = (conePlus P M * coneMinus P M) * T_P ∧
    comm T_P (conePlus P M * coneMinus P M) = 0 := by
  have h_socratic : P * (M * M) * P - (P * M * P) * (P * M * P) = conePlus P M * coneMinus P M := by
    dsimp [conePlus, coneMinus]
    peirce_nf hP
  have h_del : P * (M * M) * P = conePlus P M * coneMinus P M := by
    have h_sub := h_socratic
    rw [h_ablated, zero_mul, sub_zero] at h_sub
    exact h_sub
  have h_intertwine :
      T_P * (conePlus P M * coneMinus P M) = (conePlus P M * coneMinus P M) * T_P := by
    calc
      T_P * (conePlus P M * coneMinus P M) = (T_P * conePlus P M) * coneMinus P M := by
        rw [← mul_assoc]
      _ = (conePlus P M * T_H) * coneMinus P M := by rw [hT_plus]
      _ = conePlus P M * (T_H * coneMinus P M) := by rw [mul_assoc]
      _ = conePlus P M * (coneMinus P M * T_P) := by rw [hT_minus]
      _ = (conePlus P M * coneMinus P M) * T_P := by rw [← mul_assoc]
  exact ⟨h_socratic, h_del, h_intertwine, sub_eq_zero.mpr h_intertwine⟩

/--
**Theorem 2B (`𝔏𝔖₄` & `𝔏𝔖₅` — `binary_involution_spectral_linearization`):**
For any involution `σ ∈ B` satisfying `σ * σ = 1` and a commuting operator `s`:
1. **Product of Opposite Attribute Parities:** `(1 + s * σ) * (1 - s * σ) = 1 - s * s`.
2. **Exact Quadratic Linearization:** `(1 + s * σ) * (1 + s * σ) = (1 + s * s) + (s + s) * σ`.
3. **Orthogonal Hypercube Projectors:** `(1 + σ) * (1 - σ) = 0`.
4. **Universal Spectral Linearization:**
   `f_plus * (1 + σ) + f_minus * (1 - σ) = (f_plus + f_minus) + (f_plus - f_minus) * σ`.
-/
theorem binary_involution_spectral_linearization
    {B : Type*} [Ring B] (σ s f_plus f_minus : B) (hσ : σ * σ = 1) (hs : s * σ = σ * s) :
    (1 + s * σ) * (1 - s * σ) = 1 - s * s ∧
    (1 + s * σ) * (1 + s * σ) = (1 + s * s) + (s + s) * σ ∧
    (1 + σ) * (1 - σ) = 0 ∧
    f_plus * (1 + σ) + f_minus * (1 - σ) = (f_plus + f_minus) + (f_plus - f_minus) * σ := by
  have hsσ2 : s * σ * (s * σ) = s * s := by
    calc
      s * σ * (s * σ) = s * (σ * s) * σ := by noncomm_ring
      _ = s * (s * σ) * σ := by rw [← hs]
      _ = (s * s) * (σ * σ) := by noncomm_ring
      _ = s * s := by rw [hσ, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (1 + s * σ) * (1 - s * σ) = 1 - s * σ + s * σ - s * σ * (s * σ) := by noncomm_ring
      _ = 1 - s * s := by rw [hsσ2]; abel
  · calc
      (1 + s * σ) * (1 + s * σ) = 1 + s * σ + s * σ + s * σ * (s * σ) := by noncomm_ring
      _ = (1 + s * s) + (s + s) * σ := by rw [hsσ2]; noncomm_ring
  · calc
      (1 + σ) * (1 - σ) = 1 - σ * σ := by noncomm_ring
      _ = 0 := by rw [hσ, sub_self]
  · noncomm_ring

/-- The rank-one matrix formed from two modes on the product feature space. -/
def productMode {m n : Type*} (v : m → ℂ) (w : n → ℂ) : Matrix m n ℂ :=
  fun i j => v i * w j

/--
Tensor-product eigenmode composition for finite feature spaces. Eigenvector equations for `A`
and `B` imply that the outer-product mode, vectorized over the product index, is an eigenvector
of `B ⊗ₖ A`. This supplies a concrete bridge for separately established Fourier and Walsh modes.
-/
theorem kronecker_product_eigenmode_of_factorization
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (v : m → ℂ) (w : n → ℂ)
    (eigA eigB : ℂ)
    (hA : A *ᵥ v = eigA • v) (hB : B *ᵥ w = eigB • w) :
    (B ⊗ₖ A) *ᵥ Matrix.vec (productMode v w) =
      (eigB * eigA) • Matrix.vec (productMode v w) := by
  let X : Matrix m n ℂ := productMode v w
  have hAv (i : m) : (∑ k, A i k * v k) = eigA * v i := by
    have hi := congrFun hA i
    simpa [Matrix.mulVec, dotProduct] using hi
  have hBw (j : n) : (∑ k, B j k * w k) = eigB * w j := by
    have hj := congrFun hB j
    simpa [Matrix.mulVec, dotProduct] using hj
  have hAX : A * X = eigA • X := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, X, productMode]
    calc
      (∑ k, A i k * (v k * w j)) = ∑ k, (A i k * v k) * w j := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = (∑ k, A i k * v k) * w j := by rw [Finset.sum_mul]
      _ = (eigA * v i) * w j := by rw [hAv i]
      _ = eigA * (v i * w j) := by ring
  have hXB : X * Bᵀ = eigB • X := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
      X, productMode]
    calc
      (∑ k, (v i * w k) * B j k) = ∑ k, v i * (B j k * w k) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = v i * (∑ k, B j k * w k) := by rw [Finset.mul_sum]
      _ = v i * (eigB * w j) := by rw [hBw j]
      _ = eigB * (v i * w j) := by ring
  have hProduct : A * X * Bᵀ = (eigA * eigB) • X := by
    rw [hAX, Matrix.smul_mul, hXB, smul_smul]
  calc
    (B ⊗ₖ A) *ᵥ Matrix.vec X = Matrix.vec (A * X * Bᵀ) :=
      Matrix.kronecker_mulVec_vec A X B
    _ = Matrix.vec ((eigA * eigB) • X) := congrArg Matrix.vec hProduct
    _ = (eigA * eigB) • Matrix.vec X := by
      ext ⟨i, j⟩
      rfl
    _ = (eigB * eigA) • Matrix.vec (productMode v w) := by
      rw [mul_comm eigA eigB]

/-- A translation-invariant two-state attribute kernel. -/
def binaryAttributeKernel2 (c0 c1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![c0, c1; c1, c0]

/-- The two real-valued Walsh characters, viewed as complex vectors. -/
def binaryWalshCharacter2 (e i : Fin 2) : ℂ :=
  if e = 0 ∨ i = 0 then 1 else -1

/-- The eigenvalue of the two-state translation kernel at Walsh frequency `e`. -/
def binaryAttributeEigenvalue2 (e : Fin 2) (c0 c1 : ℂ) : ℂ :=
  if e = 0 then c0 + c1 else c0 - c1

/-- The two-state attribute kernel is diagonal on its Walsh characters. -/
theorem binary_attribute_kernel_walsh_eigenmode2 (c0 c1 : ℂ) (e : Fin 2) :
    binaryAttributeKernel2 c0 c1 *ᵥ binaryWalshCharacter2 e =
      binaryAttributeEigenvalue2 e c0 c1 • binaryWalshCharacter2 e := by
  ext i
  fin_cases e <;> fin_cases i <;>
    simp [binaryAttributeKernel2, binaryWalshCharacter2, binaryAttributeEigenvalue2,
      Matrix.mulVec, dotProduct] <;> ring

/--
**Joint cyclic Fourier–one-bit Walsh eigenmode.** For a cyclic convolution kernel on `ZMod N`
and a two-state attribute kernel, the Kronecker product acts diagonally on the tensor product of
the native cyclic Fourier character and one of the two Walsh characters. The eigenvalue is the
product of the DFT eigenvalue and the Walsh eigenvalue. This is a finite product-space result;
it does not assert a corpus-level probabilistic model or a stability theorem for learned
embeddings.
-/
theorem cyclic_fourier_binary_walsh_product_eigenmode
    {N : ℕ} [NeZero N] (κ : ZMod N → ℂ) (k : ZMod N)
    (c0 c1 : ℂ) (e : Fin 2) :
    (binaryAttributeKernel2 c0 c1 ⊗ₖ Matrix.circulant κ) *ᵥ
        Matrix.vec (productMode (fun i => ZMod.stdAddChar (k * i))
          (binaryWalshCharacter2 e)) =
      (binaryAttributeEigenvalue2 e c0 c1 * ZMod.dft κ k) •
        Matrix.vec (productMode (fun i => ZMod.stdAddChar (k * i))
          (binaryWalshCharacter2 e)) := by
  have hSeason : Matrix.circulant κ *ᵥ
      (fun i => ZMod.stdAddChar (k * i)) = ZMod.dft κ k •
      (fun i => ZMod.stdAddChar (k * i)) :=
    InfoGeometry.LLM.circulant_mulVec_stdAddChar κ k
  have hAttribute : binaryAttributeKernel2 c0 c1 *ᵥ binaryWalshCharacter2 e =
      binaryAttributeEigenvalue2 e c0 c1 • binaryWalshCharacter2 e :=
    binary_attribute_kernel_walsh_eigenmode2 c0 c1 e
  exact kronecker_product_eigenmode_of_factorization
    (Matrix.circulant κ) (binaryAttributeKernel2 c0 c1)
    (fun i => ZMod.stdAddChar (k * i)) (binaryWalshCharacter2 e)
    (ZMod.dft κ k) (binaryAttributeEigenvalue2 e c0 c1) hSeason hAttribute

/-- The matrix of convolution by `κ` on the repository's native Klein-four
group, with the row/column convention matching left convolution. -/
def v4ConvolutionMatrix
    (κ : InfoGeometry.Topology.V4RootSystem.V4Group → ℂ) :
    Matrix InfoGeometry.Topology.V4RootSystem.V4Group
      InfoGeometry.Topology.V4RootSystem.V4Group ℂ :=
  fun g h => κ (g⁻¹ * h)

/-- A real `V₄` character viewed as a complex-valued mode. -/
def v4ComplexMode (m : Fin 4)
    (g : InfoGeometry.Topology.V4RootSystem.V4Group) : ℂ :=
  InfoGeometry.Canonical.V4GroupFourierTransform.v4Character m g

/-- Fourier coefficient giving the eigenvalue of left convolution on a `V₄`
character mode. -/
def v4ConvolutionEigenvalue
    (κ : InfoGeometry.Topology.V4RootSystem.V4Group → ℂ) (m : Fin 4) : ℂ :=
  ∑ a : InfoGeometry.Topology.V4RootSystem.V4Group,
    κ a * v4ComplexMode m a

/-- Convolution on the native Klein-four group is diagonal on each of its four
repository-owned Walsh characters. -/
theorem v4_convolution_character_eigenmode
    (κ : InfoGeometry.Topology.V4RootSystem.V4Group → ℂ) (m : Fin 4) :
    v4ConvolutionMatrix κ *ᵥ v4ComplexMode m =
      v4ConvolutionEigenvalue κ m • v4ComplexMode m := by
  classical
  funext g
  change (∑ h : InfoGeometry.Topology.V4RootSystem.V4Group,
      κ (g⁻¹ * h) * v4ComplexMode m h) =
    v4ConvolutionEigenvalue κ m * v4ComplexMode m g
  calc
    (∑ h : InfoGeometry.Topology.V4RootSystem.V4Group,
        κ (g⁻¹ * h) * v4ComplexMode m h) =
        ∑ a : InfoGeometry.Topology.V4RootSystem.V4Group,
          κ a * v4ComplexMode m (g * a) := by
      refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ ?_
      intro a
      simp [v4ComplexMode]
    _ = ∑ a : InfoGeometry.Topology.V4RootSystem.V4Group,
        (κ a * v4ComplexMode m a) * v4ComplexMode m g := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [v4ComplexMode,
        InfoGeometry.Canonical.V4GroupFourierTransform.v4Character_mul]
      push_cast
      ring
    _ = v4ConvolutionEigenvalue κ m * v4ComplexMode m g := by
      rw [v4ConvolutionEigenvalue, ← Finset.sum_mul]

/-- Concrete joint seasonal-Fourier × `V₄`-Walsh eigenmode for the tensor
product of the cyclic convolution matrix and the native `V₄` convolution
matrix. This instantiates both factor eigenrelations rather than taking them
as hypotheses. -/
theorem cyclic_fourier_v4_walsh_product_eigenmode
    {N : ℕ} [NeZero N] (κ : ZMod N → ℂ)
    (ν : InfoGeometry.Topology.V4RootSystem.V4Group → ℂ)
    (k : ZMod N) (m : Fin 4) :
    (v4ConvolutionMatrix ν ⊗ₖ Matrix.circulant κ) *ᵥ
        Matrix.vec (productMode (fun i => ZMod.stdAddChar (k * i))
          (v4ComplexMode m)) =
      (v4ConvolutionEigenvalue ν m * ZMod.dft κ k) •
        Matrix.vec (productMode (fun i => ZMod.stdAddChar (k * i))
          (v4ComplexMode m)) := by
  have hSeason : Matrix.circulant κ *ᵥ
      (fun i => ZMod.stdAddChar (k * i)) = ZMod.dft κ k •
      (fun i => ZMod.stdAddChar (k * i)) :=
    InfoGeometry.LLM.circulant_mulVec_stdAddChar κ k
  have hV4 : v4ConvolutionMatrix ν *ᵥ v4ComplexMode m =
      v4ConvolutionEigenvalue ν m • v4ComplexMode m :=
    v4_convolution_character_eigenmode ν m
  exact kronecker_product_eigenmode_of_factorization
    (Matrix.circulant κ) (v4ConvolutionMatrix ν)
    (fun i => ZMod.stdAddChar (k * i)) (v4ComplexMode m)
    (ZMod.dft κ k) (v4ConvolutionEigenvalue ν m) hSeason hV4

/-! ## Product transform and normalization

The transform below is the tensor product of Mathlib's unnormalized cyclic DFT
and the repository's native four-character transform on `V4Group`. Its inverse
therefore carries the `1/4` Walsh normalization, while the cyclic factor uses
`ZMod.dft.symm` with Mathlib's own normalization.
-/

private abbrev LanguageV4 := InfoGeometry.Topology.V4RootSystem.V4Group

/-- Complex extension of the four native real characters of `V4Group`. -/
def v4ComplexCharacter (m : Fin 4) (g : LanguageV4) : ℂ :=
  InfoGeometry.Canonical.V4GroupFourierTransform.v4Character m g

/-- Tensor Fourier transform on `ZMod N × V4Group`: cyclic DFT in the first
coordinate followed by the four-character Walsh transform in the second. -/
noncomputable def cyclicV4ProductFourier {N : ℕ} [NeZero N]
    (f : ZMod N × LanguageV4 → ℂ) (k : ZMod N) (m : Fin 4) : ℂ :=
  ∑ g : LanguageV4, v4ComplexCharacter m g *
    ZMod.dft (fun x : ZMod N => f (x, g)) k

/-- Inverse tensor transform, with the native `1/4` V₄ normalization and the
Mathlib inverse cyclic DFT. -/
noncomputable def cyclicV4ProductFourierInv {N : ℕ} [NeZero N]
    (F : ZMod N × Fin 4 → ℂ) (x : ZMod N) (g : LanguageV4) : ℂ :=
  (ZMod.dft.symm (fun k : ZMod N => fun h : LanguageV4 =>
    (1 / 4 : ℂ) * ∑ m : Fin 4, v4ComplexCharacter m h * F (k, m)) x) g

/-- The four native characters invert their complex-valued Fourier expansion. -/
theorem v4ComplexCharacter_inversion (z : LanguageV4 → ℂ) (g : LanguageV4) :
    (1 / 4 : ℂ) * ∑ m : Fin 4, v4ComplexCharacter m g *
      (∑ h : LanguageV4, v4ComplexCharacter m h * z h) = z g := by
  classical
  have hinner (m : Fin 4) :
      (∑ h : LanguageV4, v4ComplexCharacter m h * z h) =
        ∑ j : Fin 4, v4ComplexCharacter m
          (InfoGeometry.Canonical.V4GroupFourierTransform.v4EquivFin j) *
          z (InfoGeometry.Canonical.V4GroupFourierTransform.v4EquivFin j) := by
    rw [← Equiv.sum_comp
      InfoGeometry.Canonical.V4GroupFourierTransform.v4EquivFin
      (fun h => v4ComplexCharacter m h * z h)]
  simp_rw [hinner]
  cases g <;>
    simp [v4ComplexCharacter,
      InfoGeometry.Canonical.V4GroupFourierTransform.v4Character,
      InfoGeometry.Canonical.V4GroupFourierTransform.v4EquivFin,
      Fin.sum_univ_succ] <;> ring

/-- The product Fourier transform followed by its inverse recovers every
complex-valued function on the finite product carrier. -/
theorem cyclicV4ProductFourierInv_transform {N : ℕ} [NeZero N]
    (f : ZMod N × LanguageV4 → ℂ) :
    (fun p : ZMod N × LanguageV4 =>
      cyclicV4ProductFourierInv (fun q => cyclicV4ProductFourier f q.1 q.2)
        p.1 p.2) = f := by
  funext p
  rcases p with ⟨x, g⟩
  unfold cyclicV4ProductFourierInv cyclicV4ProductFourier
  -- Apply the finite V₄ inversion at each cyclic frequency, then the cyclic inverse.
  have hfun : (fun k : ZMod N => fun h : LanguageV4 =>
      (1 / 4 : ℂ) * ∑ m : Fin 4, v4ComplexCharacter m h *
        (∑ h' : LanguageV4, v4ComplexCharacter m h' *
          ZMod.dft (fun y : ZMod N => f (y, h')) k)) =
      (fun k => fun h => ZMod.dft (fun y : ZMod N => f (y, h)) k) := by
    funext k h
    exact v4ComplexCharacter_inversion
      (fun h' => ZMod.dft (fun y : ZMod N => f (y, h')) k) h
  rw [hfun]
  have hpi : ZMod.dft (fun y : ZMod N => fun h : LanguageV4 => f (y, h)) =
      (fun k h => ZMod.dft (fun y : ZMod N => f (y, h)) k) := by
    funext k h
    simp [ZMod.dft_apply, smul_eq_mul]
  rw [← hpi]
  exact congrFun (congrFun
    (InfoGeometry.LLM.zmodDft_inverse_left
      (Φ := fun y : ZMod N => fun h : LanguageV4 => f (y, h))) x) g

/-- Complex-valued `V₄` characters are multiplicative under group multiplication. -/
theorem v4ComplexCharacter_mul (m : Fin 4) (a b : LanguageV4) :
    v4ComplexCharacter m (a * b) =
      v4ComplexCharacter m a * v4ComplexCharacter m b := by
  unfold v4ComplexCharacter
  rw [InfoGeometry.Canonical.V4GroupFourierTransform.v4Character_mul]
  push_cast
  rfl

/-- Product-group convolution on `ZMod N × V4Group`, combining cyclic difference
convolution `(Matrix.circulant ... *ᵥ ...)` on `ZMod N` with group convolution
`g * h⁻¹` on `V4Group`. -/
def cyclicV4ProductConvolution {N : ℕ} [NeZero N]
    (K f : ZMod N × LanguageV4 → ℂ) (p : ZMod N × LanguageV4) : ℂ :=
  ∑ h : LanguageV4,
    (Matrix.circulant (fun x : ZMod N => K (x, p.2 * h⁻¹)) *ᵥ
      (fun y : ZMod N => f (y, h))) p.1

/-- **Product convolution multiplier theorem on `ZMod N × V4Group` (L3).**
The tensor Fourier transform `cyclicV4ProductFourier` sends `cyclicV4ProductConvolution K f`
to the pointwise product of the spectral coefficients `cyclicV4ProductFourier K k m` and
`cyclicV4ProductFourier f k m`. -/
theorem cyclicV4ProductFourier_convolution {N : ℕ} [NeZero N]
    (K f : ZMod N × LanguageV4 → ℂ) (k : ZMod N) (m : Fin 4) :
    cyclicV4ProductFourier (cyclicV4ProductConvolution K f) k m =
      cyclicV4ProductFourier K k m * cyclicV4ProductFourier f k m := by
  classical
  have hfn (g : LanguageV4) :
      (fun x : ZMod N => cyclicV4ProductConvolution K f (x, g)) =
        ∑ h : LanguageV4,
          Matrix.circulant (fun x : ZMod N => K (x, g * h⁻¹)) *ᵥ
            (fun y : ZMod N => f (y, h)) := by
    funext x
    simp [cyclicV4ProductConvolution, Finset.sum_apply]
  have hdft (g : LanguageV4) :
      ZMod.dft (fun x : ZMod N => cyclicV4ProductConvolution K f (x, g)) k =
        ∑ h : LanguageV4,
          ZMod.dft (fun x : ZMod N => K (x, g * h⁻¹)) k *
            ZMod.dft (fun y : ZMod N => f (y, h)) k := by
    rw [hfn g, map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro h _
    exact congrFun (InfoGeometry.LLM.dft_circulant_mulVec
      (fun x : ZMod N => K (x, g * h⁻¹)) (fun y : ZMod N => f (y, h))) k
  unfold cyclicV4ProductFourier
  simp_rw [hdft, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  calc
    (∑ g : LanguageV4,
        v4ComplexCharacter m g *
          (ZMod.dft (fun x : ZMod N => K (x, g * h⁻¹)) k *
            ZMod.dft (fun y : ZMod N => f (y, h)) k)) =
      ∑ a : LanguageV4,
        v4ComplexCharacter m (a * h) *
          (ZMod.dft (fun x : ZMod N => K (x, (a * h) * h⁻¹)) k *
            ZMod.dft (fun y : ZMod N => f (y, h)) k) := by
      refine (Fintype.sum_equiv (Equiv.mulRight h) _ _ ?_).symm
      intro a
      rfl
    _ = ∑ a : LanguageV4,
          (v4ComplexCharacter m a * ZMod.dft (fun x : ZMod N => K (x, a)) k) *
            (v4ComplexCharacter m h * ZMod.dft (fun y : ZMod N => f (y, h)) k) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_inv_cancel_right a h, v4ComplexCharacter_mul m a h]
      ring
    _ = (∑ a : LanguageV4,
          v4ComplexCharacter m a * ZMod.dft (fun x : ZMod N => K (x, a)) k) *
          (v4ComplexCharacter m h * ZMod.dft (fun y : ZMod N => f (y, h)) k) := by
      rw [← Finset.sum_mul]

/-- **Spectral recovery of product convolution on `ZMod N × V4Group` (L3).**
Applying `cyclicV4ProductFourierInv` to the pointwise product of spectral coefficients
recovers `cyclicV4ProductConvolution K f`. -/
theorem cyclicV4ProductConvolution_eq_inv_mul {N : ℕ} [NeZero N]
    (K f : ZMod N × LanguageV4 → ℂ) :
    (fun p : ZMod N × LanguageV4 =>
      cyclicV4ProductFourierInv
        (fun q => cyclicV4ProductFourier K q.1 q.2 * cyclicV4ProductFourier f q.1 q.2)
        p.1 p.2) =
      cyclicV4ProductConvolution K f := by
  have hconv :
      (fun q : ZMod N × Fin 4 =>
        cyclicV4ProductFourier K q.1 q.2 * cyclicV4ProductFourier f q.1 q.2) =
      (fun q : ZMod N × Fin 4 =>
        cyclicV4ProductFourier (cyclicV4ProductConvolution K f) q.1 q.2) := by
    funext q
    exact (cyclicV4ProductFourier_convolution K f q.1 q.2).symm
  rw [hconv]
  exact cyclicV4ProductFourierInv_transform (cyclicV4ProductConvolution K f)

/-- Pointwise XOR of two words in the native finite Boolean hypercube. -/
def languageWordXor {d : ℕ} (u v : Omega.Word d) : Omega.Word d :=
  fun i => Bool.xor (u i) (v i)

/-- XORing a Boolean word with itself cancels coordinatewise. -/
theorem languageWordXor_self {d : ℕ} (u v : Omega.Word d) :
    languageWordXor u (languageWordXor u v) = v := by
  funext i
  cases hu : u i <;> cases hv : v i <;>
    simp [languageWordXor, Bool.xor, hu, hv]

/-- Pointwise Boolean XOR is commutative. -/
theorem languageWordXor_comm {d : ℕ} (u v : Omega.Word d) :
    languageWordXor u v = languageWordXor v u := by
  funext i
  cases hu : u i <;> cases hv : v i <;>
    simp [languageWordXor, Bool.xor, hu, hv]

/-- Native repository Walsh characters are multiplicative under pointwise word XOR. -/
theorem language_walsh_character_xor
    {d : ℕ} (S : Finset (Fin d)) (u v : Omega.Word d) :
    Omega.Core.walshChar S (languageWordXor u v) =
      Omega.Core.walshChar S u * Omega.Core.walshChar S v := by
  unfold Omega.Core.walshChar languageWordXor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases hu : u i <;> cases hv : v i <;> simp [Bool.xor]

/-- XOR convolution by a kernel `c` on the `d`-dimensional Boolean cube. -/
def languageWalshConvolution {d : ℕ}
    (c f : Omega.Word d → ℂ) (x : Omega.Word d) : ℂ :=
  ∑ u : Omega.Word d, c u * f (languageWordXor u x)

/-- The Walsh coefficient of a hypercube kernel at coordinate subset `S`. -/
def languageWalshKernelEigenvalue {d : ℕ}
    (c : Omega.Word d → ℂ) (S : Finset (Fin d)) : ℂ :=
  ∑ u : Omega.Word d, c u * (Omega.Core.walshChar S u : ℂ)

/--
**General finite hypercube Walsh spectrum.** For every dimension `d`, every complex kernel on
`Omega.Word d`, and every coordinate subset `S`, the repository's native Walsh character
`walshChar S` is an eigenfunction of XOR convolution, with eigenvalue its Walsh coefficient.
This proves the attribute-side diagonalization for arbitrary finite bit dimension.
-/
theorem language_walsh_xor_convolution_eigenmode
    {d : ℕ} (c : Omega.Word d → ℂ) (S : Finset (Fin d)) (x : Omega.Word d) :
    languageWalshConvolution c (fun y => (Omega.Core.walshChar S y : ℂ)) x =
      languageWalshKernelEigenvalue c S * (Omega.Core.walshChar S x : ℂ) := by
  unfold languageWalshConvolution languageWalshKernelEigenvalue
  calc
    (∑ u : Omega.Word d, c u *
        (Omega.Core.walshChar S (languageWordXor u x) : ℂ)) =
      ∑ u : Omega.Word d,
        (c u * (Omega.Core.walshChar S u : ℂ)) *
          (Omega.Core.walshChar S x : ℂ) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [language_walsh_character_xor]
            push_cast
            ring
    _ = (∑ u : Omega.Word d,
          c u * (Omega.Core.walshChar S u : ℂ)) *
          (Omega.Core.walshChar S x : ℂ) := by rw [Finset.sum_mul]

/-- The word-indexed matrix whose row `x`, column `y` entry is the convolution
kernel evaluated at `x XOR y`. -/
def languageWalshConvolutionMatrix {d : ℕ} (c : Omega.Word d → ℂ) :
    Matrix (Omega.Word d) (Omega.Word d) ℂ :=
  fun x y => c (languageWordXor x y)

/-- Left XOR by a fixed word is a self-inverse permutation of the Boolean cube. -/
def languageWordXorEquiv {d : ℕ} (x : Omega.Word d) :
    Omega.Word d ≃ Omega.Word d where
  toFun := languageWordXor x
  invFun := languageWordXor x
  left_inv := languageWordXor_self x
  right_inv := languageWordXor_self x

/-- Matrix-vector multiplication by the XOR kernel is the defined XOR convolution. -/
theorem languageWalshConvolutionMatrix_mulVec {d : ℕ}
    (c f : Omega.Word d → ℂ) (x : Omega.Word d) :
    (languageWalshConvolutionMatrix c *ᵥ f) x = languageWalshConvolution c f x := by
  change (∑ y : Omega.Word d, c (languageWordXor x y) * f y) =
    ∑ u : Omega.Word d, c u * f (languageWordXor u x)
  refine Fintype.sum_equiv (languageWordXorEquiv x) _ _ ?_
  intro u
  simp only [languageWordXorEquiv, Equiv.coe_fn_mk]
  rw [languageWordXor_comm (languageWordXor x u) x,
    languageWordXor_self x u]

/-- The native word-indexed XOR-convolution matrix is diagonal on each native Walsh mode. -/
theorem languageWalshConvolutionMatrix_walsh_eigenmode {d : ℕ}
    (c : Omega.Word d → ℂ) (S : Finset (Fin d)) :
    languageWalshConvolutionMatrix c *ᵥ
        (fun x => (Omega.Core.walshChar S x : ℂ)) =
      languageWalshKernelEigenvalue c S •
        (fun x => (Omega.Core.walshChar S x : ℂ)) := by
  funext x
  rw [languageWalshConvolutionMatrix_mulVec]
  exact language_walsh_xor_convolution_eigenmode c S x

/-- The cyclic seasonal Fourier mode and arbitrary finite Boolean-cube Walsh mode
are jointly an eigenvector of the tensor product convolution matrix. -/
theorem cyclic_fourier_arbitrary_walsh_product_eigenmode
    {N d : ℕ} [NeZero N] (κ : ZMod N → ℂ) (c : Omega.Word d → ℂ)
    (k : ZMod N) (S : Finset (Fin d)) :
    (languageWalshConvolutionMatrix c ⊗ₖ Matrix.circulant κ) *ᵥ
        Matrix.vec (productMode (fun i => ZMod.stdAddChar (k * i))
          (fun x => (Omega.Core.walshChar S x : ℂ))) =
      (languageWalshKernelEigenvalue c S * ZMod.dft κ k) •
        Matrix.vec (productMode (fun i => ZMod.stdAddChar (k * i))
          (fun x => (Omega.Core.walshChar S x : ℂ))) := by
  have hSeason : Matrix.circulant κ *ᵥ
      (fun i => ZMod.stdAddChar (k * i)) = ZMod.dft κ k •
      (fun i => ZMod.stdAddChar (k * i)) :=
    InfoGeometry.LLM.circulant_mulVec_stdAddChar κ k
  have hAttribute : languageWalshConvolutionMatrix c *ᵥ
      (fun x => (Omega.Core.walshChar S x : ℂ)) =
      languageWalshKernelEigenvalue c S •
      (fun x => (Omega.Core.walshChar S x : ℂ)) :=
    languageWalshConvolutionMatrix_walsh_eigenmode c S
  exact kronecker_product_eigenmode_of_factorization
    (Matrix.circulant κ) (languageWalshConvolutionMatrix c)
    (fun i => ZMod.stdAddChar (k * i))
    (fun x => (Omega.Core.walshChar S x : ℂ))
    (ZMod.dft κ k) (languageWalshKernelEigenvalue c S) hSeason hAttribute

/-- Tensor Fourier–Walsh transform on `ZMod N × Omega.Word d` for arbitrary bit dimension `d`. -/
noncomputable def cyclicWalshProductFourier {N d : ℕ} [NeZero N]
    (f : ZMod N × Omega.Word d → ℂ) (k : ZMod N) (S : Finset (Fin d)) : ℂ :=
  ∑ u : Omega.Word d, (Omega.Core.walshChar S u : ℂ) *
    ZMod.dft (fun x : ZMod N => f (x, u)) k

/-- Product cyclic-difference and Boolean-XOR convolution on `ZMod N × Omega.Word d`. -/
def cyclicWalshProductConvolution {N d : ℕ} [NeZero N]
    (K f : ZMod N × Omega.Word d → ℂ) (p : ZMod N × Omega.Word d) : ℂ :=
  ∑ v : Omega.Word d,
    (Matrix.circulant (fun x : ZMod N => K (x, languageWordXor p.2 v)) *ᵥ
      (fun y : ZMod N => f (y, v))) p.1

/-- **Arbitrary-bit-dimension product convolution multiplier theorem on `ZMod N × Omega.Word d` (L3).**
The tensor Fourier–Walsh transform `cyclicWalshProductFourier` sends `cyclicWalshProductConvolution K f`
to the pointwise product `cyclicWalshProductFourier K k S * cyclicWalshProductFourier f k S`. -/
theorem cyclicWalshProductFourier_convolution {N d : ℕ} [NeZero N]
    (K f : ZMod N × Omega.Word d → ℂ) (k : ZMod N) (S : Finset (Fin d)) :
    cyclicWalshProductFourier (cyclicWalshProductConvolution K f) k S =
      cyclicWalshProductFourier K k S * cyclicWalshProductFourier f k S := by
  classical
  have hfn (u : Omega.Word d) :
      (fun x : ZMod N => cyclicWalshProductConvolution K f (x, u)) =
        ∑ v : Omega.Word d,
          Matrix.circulant (fun x : ZMod N => K (x, languageWordXor u v)) *ᵥ
            (fun y : ZMod N => f (y, v)) := by
    funext x
    simp [cyclicWalshProductConvolution, Finset.sum_apply]
  have hdft (u : Omega.Word d) :
      ZMod.dft (fun x : ZMod N => cyclicWalshProductConvolution K f (x, u)) k =
        ∑ v : Omega.Word d,
          ZMod.dft (fun x : ZMod N => K (x, languageWordXor u v)) k *
            ZMod.dft (fun y : ZMod N => f (y, v)) k := by
    rw [hfn u, map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro v _
    exact congrFun (InfoGeometry.LLM.dft_circulant_mulVec
      (fun x : ZMod N => K (x, languageWordXor u v)) (fun y : ZMod N => f (y, v))) k
  unfold cyclicWalshProductFourier
  simp_rw [hdft]
  have h_lhs (u : Omega.Word d) :
      (Omega.Core.walshChar S u : ℂ) *
        ∑ v : Omega.Word d,
          ZMod.dft (fun x : ZMod N => K (x, languageWordXor u v)) k *
            ZMod.dft (fun y : ZMod N => f (y, v)) k =
      ∑ v : Omega.Word d,
        (Omega.Core.walshChar S u : ℂ) *
          (ZMod.dft (fun x : ZMod N => K (x, languageWordXor u v)) k *
            ZMod.dft (fun y : ZMod N => f (y, v)) k) :=
    Finset.mul_sum _ _ _
  simp_rw [h_lhs]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  calc
    (∑ u : Omega.Word d,
        (Omega.Core.walshChar S u : ℂ) *
          (ZMod.dft (fun x : ZMod N => K (x, languageWordXor u v)) k *
            ZMod.dft (fun y : ZMod N => f (y, v)) k)) =
      ∑ w : Omega.Word d,
        (Omega.Core.walshChar S (languageWordXor v w) : ℂ) *
          (ZMod.dft (fun x : ZMod N => K (x, languageWordXor (languageWordXor v w) v)) k *
            ZMod.dft (fun y : ZMod N => f (y, v)) k) := by
      refine (Fintype.sum_equiv (languageWordXorEquiv v) _ _ ?_).symm
      intro w
      rfl
    _ = ∑ w : Omega.Word d,
          ((Omega.Core.walshChar S w : ℂ) * ZMod.dft (fun x : ZMod N => K (x, w)) k) *
            ((Omega.Core.walshChar S v : ℂ) * ZMod.dft (fun y : ZMod N => f (y, v)) k) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [languageWordXor_comm (languageWordXor v w) v,
          languageWordXor_self v w,
          language_walsh_character_xor S v w]
      push_cast
      ring
    _ = (∑ w : Omega.Word d,
          (Omega.Core.walshChar S w : ℂ) * ZMod.dft (fun x : ZMod N => K (x, w)) k) *
          ((Omega.Core.walshChar S v : ℂ) * ZMod.dft (fun y : ZMod N => f (y, v)) k) := by
      rw [← Finset.sum_mul]

/-! ## Concrete Partitioned Vocabulary Carrier for the Peirce Helper Excursion (L5) -/

/-- Concrete projector onto the target cyclic sub-vocabulary `Sum.inl` inside a partitioned
vocabulary `Sum G G` (target cyclic words `⊕` helper words). -/
def vocabTargetProjector (G R : Type*) [DecidableEq G] [Zero R] [One R] :
    Matrix (Sum G G) (Sum G G) R :=
  Matrix.fromBlocks 1 0 0 0

/-- Partitioned vocabulary co-occurrence matrix with ablated direct target-target block (`0`),
translation-invariant target-to-helper kernel `relativeKernelMatrix f`, helper-to-target kernel
`relativeKernelMatrix g`, and arbitrary helper-to-helper block `D`. -/
def ablatedVocabCooccurrenceMatrix {G R : Type*} [AddCommGroup G] [Zero R]
    (f g : G → R) (D : Matrix G G R) : Matrix (Sum G G) (Sum G G) R :=
  Matrix.fromBlocks 0 (relativeKernelMatrix f) (relativeKernelMatrix g) D

/-- Product of two `relativeKernelMatrix` matrices equals the `relativeKernelMatrix` of their
finite kernel convolution. -/
theorem relativeKernelMatrix_mul_eq {G R : Type*} [AddCommGroup G] [Fintype G] [Semiring R]
    (f g : G → R) :
    relativeKernelMatrix f * relativeKernelMatrix g =
      relativeKernelMatrix (finiteKernelConvolution f g) := by
  ext i j
  exact relativeKernelMatrix_mul_eq_convolution f g i j

/-- **Concrete partitioned-vocabulary Peirce excursion and translation-invariant month kernel (L5).**
On the partitioned vocabulary `Sum G G`:
1. `vocabTargetProjector G R` is idempotent.
2. Direct target-target co-occurrences are ablated (`P * M * P = 0`).
3. The off-diagonal Peirce excursion `conePlus P M * coneMinus P M` equals
   `Matrix.fromBlocks (relativeKernelMatrix (finiteKernelConvolution f g)) 0 0 0`.
4. The two-hop projected matrix `P * (M * M) * P` equals
   `Matrix.fromBlocks (relativeKernelMatrix (finiteKernelConvolution f g)) 0 0 0`.
5. Every target-block entry `(Sum.inl (i + a), Sum.inl (j + a))` of `P * (M * M) * P` equals
   `finiteKernelConvolution f g (j - i)` and is invariant under simultaneous cyclic shifts. -/
theorem partitioned_vocabulary_peirce_excursion_eq_convolution_kernel
    {G R : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Ring R]
    (f g : G → R) (D : Matrix G G R) (a i j : G) :
    vocabTargetProjector G R * vocabTargetProjector G R = vocabTargetProjector G R ∧
    vocabTargetProjector G R * ablatedVocabCooccurrenceMatrix f g D * vocabTargetProjector G R = 0 ∧
    conePlus (vocabTargetProjector G R) (ablatedVocabCooccurrenceMatrix f g D) *
        coneMinus (vocabTargetProjector G R) (ablatedVocabCooccurrenceMatrix f g D) =
      Matrix.fromBlocks (relativeKernelMatrix (finiteKernelConvolution f g)) 0 0 0 ∧
    vocabTargetProjector G R *
        (ablatedVocabCooccurrenceMatrix f g D * ablatedVocabCooccurrenceMatrix f g D) *
        vocabTargetProjector G R =
      Matrix.fromBlocks (relativeKernelMatrix (finiteKernelConvolution f g)) 0 0 0 ∧
    (vocabTargetProjector G R *
        (ablatedVocabCooccurrenceMatrix f g D * ablatedVocabCooccurrenceMatrix f g D) *
        vocabTargetProjector G R) (Sum.inl (i + a)) (Sum.inl (j + a)) =
      finiteKernelConvolution f g (j - i) := by
  have hIdem :
      vocabTargetProjector G R * vocabTargetProjector G R = vocabTargetProjector G R := by
    unfold vocabTargetProjector
    simp [Matrix.fromBlocks_multiply]
  have hAblated :
      vocabTargetProjector G R * ablatedVocabCooccurrenceMatrix f g D * vocabTargetProjector G R = 0 := by
    unfold vocabTargetProjector ablatedVocabCooccurrenceMatrix
    simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_zero]
  have hComp :
      (1 : Matrix (Sum G G) (Sum G G) R) - vocabTargetProjector G R =
        Matrix.fromBlocks 0 0 0 1 := by
    ext x y
    cases x <;> cases y <;>
      simp [vocabTargetProjector, Matrix.fromBlocks, Matrix.one_apply]
  have hPlus :
      conePlus (vocabTargetProjector G R) (ablatedVocabCooccurrenceMatrix f g D) =
        Matrix.fromBlocks 0 (relativeKernelMatrix f) 0 0 := by
    dsimp [conePlus]
    rw [hComp]
    unfold vocabTargetProjector ablatedVocabCooccurrenceMatrix
    simp [Matrix.fromBlocks_multiply]
  have hMinus :
      coneMinus (vocabTargetProjector G R) (ablatedVocabCooccurrenceMatrix f g D) =
        Matrix.fromBlocks 0 0 (relativeKernelMatrix g) 0 := by
    dsimp [coneMinus]
    rw [hComp]
    unfold vocabTargetProjector ablatedVocabCooccurrenceMatrix
    simp [Matrix.fromBlocks_multiply]
  have hExcursion :
      conePlus (vocabTargetProjector G R) (ablatedVocabCooccurrenceMatrix f g D) *
          coneMinus (vocabTargetProjector G R) (ablatedVocabCooccurrenceMatrix f g D) =
        Matrix.fromBlocks (relativeKernelMatrix (finiteKernelConvolution f g)) 0 0 0 := by
    rw [hPlus, hMinus]
    simp [Matrix.fromBlocks_multiply, relativeKernelMatrix_mul_eq]
  have hTwoHop :
      vocabTargetProjector G R *
          (ablatedVocabCooccurrenceMatrix f g D * ablatedVocabCooccurrenceMatrix f g D) *
          vocabTargetProjector G R =
        Matrix.fromBlocks (relativeKernelMatrix (finiteKernelConvolution f g)) 0 0 0 := by
    unfold vocabTargetProjector ablatedVocabCooccurrenceMatrix
    simp [Matrix.fromBlocks_multiply, relativeKernelMatrix_mul_eq]
  have hInl :
      (vocabTargetProjector G R *
          (ablatedVocabCooccurrenceMatrix f g D * ablatedVocabCooccurrenceMatrix f g D) *
          vocabTargetProjector G R) (Sum.inl (i + a)) (Sum.inl (j + a)) =
        finiteKernelConvolution f g (j - i) := by
    rw [hTwoHop]
    simp [Matrix.fromBlocks_apply₁₁, relativeKernelMatrix, add_sub_add_right_eq_sub]
  exact ⟨hIdem, hAblated, hExcursion, hTwoHop, hInl⟩

/-! ## Real Fourier Gram Factorization and Eigenvalue-Difference Identity (L6) -/

/-- **Cyclic real Fourier Gram factorization and circulant eigenvalue-difference identity (L6).**
1. The two-column real Fourier feature matrix `W := cyclicRealFourierPair a k` has Gram matrix
   exactly equal to the single-harmonic cosine circulant; consequently its Gram residual and the
   associated factorization gradient both vanish. No exact-rank claim is made.
2. For any circulant kernel `κ` and frequencies `k₁, k₂`, subtracting the `k₂` eigenvalue times
   the identity annihilates the `k₂` mode and scales the `k₁` mode by the eigenvalue difference.
   No ordering, distinctness, or positivity assumption on that difference is included. -/
theorem cyclic_fourier_gram_factorization_and_eigenvalue_difference
    {N : ℕ} [NeZero N] (a : ℝ) (k k₁ k₂ : ZMod N) (κ : ZMod N → ℂ) :
    (InfoGeometry.LLM.cyclicRealFourierPair a k *
        (InfoGeometry.LLM.cyclicRealFourierPair a k).transpose -
        Matrix.circulant (fun i : ZMod N => a ^ 2 * (ZMod.stdAddChar (k * i)).re) = 0 ∧
     (InfoGeometry.LLM.cyclicRealFourierPair a k *
        (InfoGeometry.LLM.cyclicRealFourierPair a k).transpose -
        Matrix.circulant (fun i : ZMod N => a ^ 2 * (ZMod.stdAddChar (k * i)).re)) *
        InfoGeometry.LLM.cyclicRealFourierPair a k = 0) ∧
    ((Matrix.circulant κ - ZMod.dft κ k₂ • (1 : Matrix (ZMod N) (ZMod N) ℂ)) *ᵥ
        (fun i : ZMod N => ZMod.stdAddChar (k₂ * i)) = 0 ∧
     (Matrix.circulant κ - ZMod.dft κ k₂ • (1 : Matrix (ZMod N) (ZMod N) ℂ)) *ᵥ
        (fun i : ZMod N => ZMod.stdAddChar (k₁ * i)) =
        (ZMod.dft κ k₁ - ZMod.dft κ k₂) • (fun i : ZMod N => ZMod.stdAddChar (k₁ * i))) := by
  have hGram :
      InfoGeometry.LLM.cyclicRealFourierPair a k *
          (InfoGeometry.LLM.cyclicRealFourierPair a k).transpose -
          Matrix.circulant (fun i : ZMod N => a ^ 2 * (ZMod.stdAddChar (k * i)).re) = 0 :=
    sub_eq_zero.mpr (InfoGeometry.LLM.cyclicRealFourierPair_gram_eq_circulant a k)
  have hGrad :
      (InfoGeometry.LLM.cyclicRealFourierPair a k *
          (InfoGeometry.LLM.cyclicRealFourierPair a k).transpose -
          Matrix.circulant (fun i : ZMod N => a ^ 2 * (ZMod.stdAddChar (k * i)).re)) *
          InfoGeometry.LLM.cyclicRealFourierPair a k = 0 := by
    simp [hGram]
  have hMode2 :
      (Matrix.circulant κ - ZMod.dft κ k₂ • (1 : Matrix (ZMod N) (ZMod N) ℂ)) *ᵥ
        (fun i : ZMod N => ZMod.stdAddChar (k₂ * i)) = 0 := by
    calc
      _ = ZMod.dft κ k₂ • (fun i : ZMod N => ZMod.stdAddChar (k₂ * i)) -
          ZMod.dft κ k₂ • (fun i : ZMod N => ZMod.stdAddChar (k₂ * i)) := by
            rw [Matrix.sub_mulVec, InfoGeometry.LLM.circulant_mulVec_stdAddChar κ k₂,
              Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = 0 := sub_self _
  have hMode1 :
      (Matrix.circulant κ - ZMod.dft κ k₂ • (1 : Matrix (ZMod N) (ZMod N) ℂ)) *ᵥ
        (fun i : ZMod N => ZMod.stdAddChar (k₁ * i)) =
        (ZMod.dft κ k₁ - ZMod.dft κ k₂) • (fun i : ZMod N => ZMod.stdAddChar (k₁ * i)) := by
    rw [Matrix.sub_mulVec, InfoGeometry.LLM.circulant_mulVec_stdAddChar κ k₁,
        Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  exact ⟨⟨hGram, hGrad⟩, ⟨hMode2, hMode1⟩⟩

/--
The `3 × 3` tridiagonal discrete Laplacian matrix associated to the Kac–Murdock–Szegő (KMS)
open-chain exponential Toeplitz matrix `symToeplitz3 1 ρ (ρ ^ 2)`:
`L_tri(ρ) = !![1, -ρ, 0; -ρ, 1 + ρ², -ρ; 0, -ρ, 1]`.
-/
def kmsTridiagonalLaplacian3 {R : Type*} [Ring R] (ρ : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, -ρ, 0;
     -ρ, 1 + ρ ^ 2, -ρ;
     0, -ρ, 1]

/--
**Theorem 3B (`𝔏𝔖₆` — `open_boundary_exponential_kernel_tridiagonal_inverse`, Prop. 3 of `arXiv:2602.15029`):**
The open-boundary exponential co-occurrence Toeplitz matrix `symToeplitz3 1 α (α ^ 2)` (`K_{ij} = α^{|i-j|}`)
is inverted up to `(1 - α ^ 2)` by the tridiagonal discrete Laplacian `kmsTridiagonalLaplacian3 α`
on both the left and the right.
-/
theorem open_boundary_exponential_kernel_tridiagonal_inverse
    {R : Type*} [CommRing R] (α : R) :
    symToeplitz3 1 α (α ^ 2) * kmsTridiagonalLaplacian3 α =
      (1 - α ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) ∧
    kmsTridiagonalLaplacian3 α * symToeplitz3 1 α (α ^ 2) =
      (1 - α ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) := by
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symToeplitz3, kmsTridiagonalLaplacian3, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring

/-- **Open-Chain KMS / Graph Laplacian Eigenvector Horseshoe Theorem:**
Over any commutative ring `R`:
1. For any `ρ : R`, the first antisymmetric open-chain mode `![-1, 0, 1]` is an exact eigenvector
   of `symToeplitz3 1 ρ (ρ ^ 2)` with eigenvalue `1 - ρ ^ 2` and of `kmsTridiagonalLaplacian3 ρ`
   with eigenvalue `1`.
2. At `ρ = 1`, `![1, 1, 1]`, `![-1, 0, 1]`, and `![1, -2, 1]` are mutually orthogonal exact
   eigenvectors of `kmsTridiagonalLaplacian3 1` with eigenvalues `0`, `1`, and `3`.
3. At every chain site `i : Fin 3`, the second harmonic eigenvector `![1, -2, 1]` and the
   DCT-I second harmonic `![1, -1, 1]` are exact quadratic horseshoe functions of the first
   harmonic eigenvector `![-1, 0, 1]`:
   `![1, -2, 1] i = 3 * (![-1, 0, 1] i) ^ 2 - 2` and
   `![1, -1, 1] i = 2 * (![-1, 0, 1] i) ^ 2 - 1`. -/
theorem kmsTridiagonalLaplacian3_eigenvector_horseshoe
    {R : Type*} [CommRing R] (ρ : R) (i : Fin 3) :
    symToeplitz3 1 ρ (ρ ^ 2) *ᵥ ![(-1 : R), 0, 1] = (1 - ρ ^ 2) • ![(-1 : R), 0, 1] ∧
    kmsTridiagonalLaplacian3 ρ *ᵥ ![(-1 : R), 0, 1] = (1 : R) • ![(-1 : R), 0, 1] ∧
    kmsTridiagonalLaplacian3 (1 : R) *ᵥ ![(1 : R), 1, 1] = 0 ∧
    kmsTridiagonalLaplacian3 (1 : R) *ᵥ ![(-1 : R), 0, 1] = (1 : R) • ![(-1 : R), 0, 1] ∧
    kmsTridiagonalLaplacian3 (1 : R) *ᵥ ![(1 : R), -2, 1] = (3 : R) • ![(1 : R), -2, 1] ∧
    dotProduct ![(1 : R), 1, 1] ![(-1 : R), 0, 1] = 0 ∧
    dotProduct ![(1 : R), 1, 1] ![(1 : R), -2, 1] = 0 ∧
    dotProduct ![(-1 : R), 0, 1] ![(1 : R), -2, 1] = 0 ∧
    ![(1 : R), -2, 1] i = 3 * (![(-1 : R), 0, 1] i) ^ 2 - 2 ∧
    ![(1 : R), -1, 1] i = 2 * (![(-1 : R), 0, 1] i) ^ 2 - 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext j
    fin_cases j <;> simp [symToeplitz3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  · ext j
    fin_cases j <;> simp [kmsTridiagonalLaplacian3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext j
    fin_cases j <;> simp [kmsTridiagonalLaplacian3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext j
    fin_cases j <;> simp [kmsTridiagonalLaplacian3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext j
    fin_cases j <;> simp [kmsTridiagonalLaplacian3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  · simp [dotProduct, Fin.sum_univ_three]
  · simp [dotProduct, Fin.sum_univ_three]
    ring
  · simp [dotProduct, Fin.sum_univ_three]
  · fin_cases i <;> simp <;> ring
  · fin_cases i <;> simp <;> ring

/--
**Theorem 7B (`𝔏𝔖₇` — `ls7_peirce_helper_excursion_bkm_attribute_surprisal_and_kms_toeplitz_laplacian`):**
Collects finite algebraic identities under explicit hypotheses, motivated by parts of
`arXiv:2602.15029` (Sections 2.1.1, 2.1.2, and Eq. (44)). The Peirce excursion identity below
does not identify its factor with a measured month kernel from the empirical helper-word experiment;
the binary log identity is conditional on a supplied factor and does not derive PMI's probability
factorization:
1. **Two-Hop Helper-Word Peirce Excursion (`Q_+ = N_+ N_- = conePlus P M * coneMinus P M`):**
   - For any idempotent `P * P = P` and operator `M : B` in `[Ring B]`, the `(1, 1)` Peirce block
     of `M²` decomposes as:
     `P * (M * M) * P = (P * M * P) * (P * M * P) + conePlus P M * coneMinus P M`.
   - **Survival of Circular Geometry Under Direct Co-Occurrence Deletion (`P * M * P = 0`):**
     When direct co-occurrences inside the `P`-subspace (e.g., month-to-month co-occurrences) are
     deleted (`P * M * P = 0`), the two-hop block reduces purely to the helper-word excursion
     `P * (M * M) * P = conePlus P M * coneMinus P M`.
   - **Shift-Commutant Preservation on the Algebraic Excursion Term:**
     Whenever a shift operator `S : B` commutes with `P` (`comm S P = 0`) and with `M`
     (`comm S M = 0`), `S` commutes with both off-diagonal transitions (`comm S (conePlus P M) = 0`,
     `comm S (coneMinus P M) = 0`) and with their two-hop excursion product
     `comm S (conePlus P M * coneMinus P M) = 0`. This proves commutation with the supplied shift
     under the stated hypotheses; a cyclic matrix realization requires an additional finite-shift
     representation.
2. **Conditional Binary Log-Factor Identity (`log(1 + s * σ)`) and Two-Sheeted Operator Normal Form (`ModularSurprisalVolumeClockingBKMClosurePoset`, `V4GroupFourierTransform`):**
   - For any binary attribute product `σ : ℝ` with `σ ^ 2 = 1` and coupling `s ∈ (-1, 1)`, the
     transcendental logarithm `Real.log (1 + s * σ)` collapses to the exact linear form in `σ`:
     `Real.log (1 + s * σ) = (Real.log (1 + s) + Real.log (1 - s)) / 2 + ((Real.log (1 + s) - Real.log (1 - s)) / 2) * σ`,
   - Over `[Ring B] [Algebra ℝ B]`, `ModularSurprisalVolumeClockingBKMClosurePoset.realSheetSurprisalOp P (1 + s) (1 - s)`
     is in exact two-sheeted idempotent normal form
     `((-(Real.log (1 + s) + Real.log (1 - s)) / 2) : ℝ) • (1 : B) - (((-Real.log (1 - s) - -Real.log (1 + s)) / 2) : ℝ) • invS P`,
   - And on the binary attribute hypercube `V4Group`, Walsh–Hadamard inversion recovers any attribute
     profile: `(1 / 4 : ℝ) * ∑ m : Fin 4, v4Character m g_v4 * v4Fourier m z_v4 = z_v4 g_v4`.
3. **Open 1D Interval Kac–Murdock–Szegő Symmetric Toeplitz Matrix & Exact Tridiagonal Discrete Laplacian Inverse:**
   - Over any `[CommRing R]`, the open-chain exponential kernel `symToeplitz3 1 ρ (ρ ^ 2)` and the
     tridiagonal discrete Laplacian `kmsTridiagonalLaplacian3 ρ` satisfy:
     `symToeplitz3 1 ρ (ρ ^ 2) * kmsTridiagonalLaplacian3 ρ = (1 - ρ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R)`
     and `kmsTridiagonalLaplacian3 ρ * symToeplitz3 1 ρ (ρ ^ 2) = (1 - ρ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R)`,
   - Zero periodic wrap-around corners (`kmsTridiagonalLaplacian3 ρ 0 2 = 0 ∧ kmsTridiagonalLaplacian3 ρ 2 0 = 0`),
   - Interior vs. boundary diagonal weight defect (`kmsTridiagonalLaplacian3 ρ 1 1 - kmsTridiagonalLaplacian3 ρ 0 0 = ρ ^ 2`).
4. **Lissajous Higher-Harmonic Extrinsic Curvature (`k²` / `k⁴` Ripple Scaling) & Joint Seasonal Circle `×` Binary Hypercube Product Character (`ℤ_N × V₄`):**
   - On the two-harmonic Clifford torus (`c₁² + s₁² = 1`, `c₂² + s₂² = 1`), the second-harmonic
     acceleration/velocity curvature excess satisfies
     `((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (4 * r₂ * c₂) ^ 2 + (4 * r₂ * s₂) ^ 2) - ((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (2 * r₂ * c₂) ^ 2 + (2 * r₂ * s₂) ^ 2) = 12 * r₂ ^ 2`,
   - And the joint product character `(t, g) ↦ ZMod.stdAddChar (k_freq * t) * (v4Character m_v4 g : ℂ)`
     on `ZMod N_cyc × V4Group` is multiplicative across both the seasonal circle and the binary
     attribute hypercube.
-/
theorem ls7_peirce_helper_excursion_bkm_attribute_surprisal_and_kms_toeplitz_laplacian
    {B : Type*} [Ring B] [Algebra ℝ B] {P : B} (hP : P * P = P)
    (S M : B) (hSP : comm S P = 0) (hSM : comm S M = 0)
    (s σ r₁ r₂ c₁ s₁ c₂ s₂ : ℝ) (hs_low : -1 < s) (hs_high : s < 1) (hσ : σ ^ 2 = 1)
    (hC1 : c₁ ^ 2 + s₁ ^ 2 = 1) (hC2 : c₂ ^ 2 + s₂ ^ 2 = 1)
    {R : Type*} [CommRing R] (ρ : R)
    {N_cyc : ℕ} [NeZero N_cyc] (k_freq t₁ t₂ : ZMod N_cyc)
    (m_v4 : Fin 4) (g₁ g₂ g_v4 : InfoGeometry.Topology.V4RootSystem.V4Group)
    (z_v4 : InfoGeometry.Topology.V4RootSystem.V4Group → ℝ) :
    (P * (M * M) * P = (P * M * P) * (P * M * P) + conePlus P M * coneMinus P M ∧
     (P * M * P = 0 → P * (M * M) * P = conePlus P M * coneMinus P M) ∧
     comm S (conePlus P M) = 0 ∧
     comm S (coneMinus P M) = 0 ∧
     comm S (conePlus P M * coneMinus P M) = 0) ∧
    (Real.log (1 + s * σ) =
       (Real.log (1 + s) + Real.log (1 - s)) / 2 +
         ((Real.log (1 + s) - Real.log (1 - s)) / 2) * σ ∧
     Real.log ((1 + s) / (1 - s)) = Real.log (1 + s) - Real.log (1 - s) ∧
     (-Real.log (1 + s)) • P + (-Real.log (1 - s)) • (1 - P) =
       ((-(Real.log (1 + s) + Real.log (1 - s)) / 2) : ℝ) • (1 : B) -
         (((-Real.log (1 - s) - -Real.log (1 + s)) / 2) : ℝ) • invS P ∧
     (1 / 4 : ℝ) *
       ∑ m : Fin 4,
         InfoGeometry.Canonical.V4GroupFourierTransform.v4Character m g_v4 *
           InfoGeometry.Canonical.V4GroupFourierTransform.v4Fourier m z_v4 =
       z_v4 g_v4) ∧
    (symToeplitz3 1 ρ (ρ ^ 2) * kmsTridiagonalLaplacian3 ρ =
       (1 - ρ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) ∧
     kmsTridiagonalLaplacian3 ρ * symToeplitz3 1 ρ (ρ ^ 2) =
       (1 - ρ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) ∧
     kmsTridiagonalLaplacian3 ρ 0 2 = 0 ∧
     kmsTridiagonalLaplacian3 ρ 2 0 = 0 ∧
     kmsTridiagonalLaplacian3 ρ 1 1 - kmsTridiagonalLaplacian3 ρ 0 0 = ρ ^ 2) ∧
    (((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (r₂ * c₂) ^ 2 + (r₂ * s₂) ^ 2 = r₁ ^ 2 + r₂ ^ 2 ∧
      ((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (4 * r₂ * c₂) ^ 2 + (4 * r₂ * s₂) ^ 2) -
        ((r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (2 * r₂ * c₂) ^ 2 + (2 * r₂ * s₂) ^ 2) =
        12 * r₂ ^ 2) ∧
     ZMod.stdAddChar (k_freq * (t₁ + t₂)) *
         (InfoGeometry.Canonical.V4GroupFourierTransform.v4Character m_v4 (g₁ * g₂) : ℂ) =
       (ZMod.stdAddChar (k_freq * t₁) *
         (InfoGeometry.Canonical.V4GroupFourierTransform.v4Character m_v4 g₁ : ℂ)) *
       (ZMod.stdAddChar (k_freq * t₂) *
         (InfoGeometry.Canonical.V4GroupFourierTransform.v4Character m_v4 g₂ : ℂ))) := by
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
  have hCommPlus : comm S (conePlus P M) = 0 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm, conePlus]
    calc
      S * (P * M * (1 - P)) - P * M * (1 - P) * S =
          ((S * P) * M) * (1 - P) - (P * M) * ((1 - P) * S) := by noncomm_ring
      _ = ((P * S) * M) * (1 - P) - (P * M) * (S * (1 - P)) := by rw [hSP_eq, hS1P]
      _ = (P * (S * M)) * (1 - P) - (P * M) * (S * (1 - P)) := by rw [mul_assoc P S M]
      _ = (P * (M * S)) * (1 - P) - (P * M) * (S * (1 - P)) := by rw [hSM_eq]
      _ = 0 := by noncomm_ring
  have hCommMinus : comm S (coneMinus P M) = 0 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm, coneMinus]
    calc
      S * ((1 - P) * M * P) - (1 - P) * M * P * S =
          ((S * (1 - P)) * M) * P - ((1 - P) * M) * (P * S) := by noncomm_ring
      _ = (((1 - P) * S) * M) * P - ((1 - P) * M) * (S * P) := by rw [← hS1P, hSP_eq]
      _ = ((1 - P) * (S * M)) * P - ((1 - P) * M) * (S * P) := by rw [mul_assoc (1 - P) S M]
      _ = ((1 - P) * (M * S)) * P - ((1 - P) * M) * (S * P) := by rw [hSM_eq]
      _ = 0 := by noncomm_ring
  have hPlusEq : S * conePlus P M = conePlus P M * S := sub_eq_zero.mp hCommPlus
  have hMinusEq : S * coneMinus P M = coneMinus P M * S := sub_eq_zero.mp hCommMinus
  have hCommProd : comm S (conePlus P M * coneMinus P M) = 0 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    calc
      S * (conePlus P M * coneMinus P M) - conePlus P M * coneMinus P M * S =
          (S * conePlus P M) * coneMinus P M - conePlus P M * (coneMinus P M * S) := by
        rw [← mul_assoc, ← mul_assoc]
      _ = (conePlus P M * S) * coneMinus P M - conePlus P M * (S * coneMinus P M) := by
        rw [hPlusEq, hMinusEq]
      _ = 0 := by rw [mul_assoc, sub_self]
  have hBinLog :=
    InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.binary_attribute_log_affine
      s σ hs_low hs_high (by simpa [sq] using hσ)
  have hLogPMI := hBinLog.2
  have hp_pos : 0 < 1 + s := hBinLog.1.1
  have hq_pos : 0 < 1 - s := hBinLog.1.2
  have hLogRatio : Real.log ((1 + s) / (1 - s)) = Real.log (1 + s) - Real.log (1 - s) :=
    Real.log_div hp_pos.ne' hq_pos.ne'
  have hSurp :
      (-Real.log (1 + s)) • P + (-Real.log (1 - s)) • (1 - P) =
        ((-(Real.log (1 + s) + Real.log (1 - s)) / 2) : ℝ) • (1 : B) -
          (((-Real.log (1 - s) - -Real.log (1 + s)) / 2) : ℝ) • invS P := by
    dsimp [invS]
    module
  have hKMS_right :
      symToeplitz3 1 ρ (ρ ^ 2) * kmsTridiagonalLaplacian3 ρ =
        (1 - ρ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symToeplitz3, kmsTridiagonalLaplacian3, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring
  have hKMS_left :
      kmsTridiagonalLaplacian3 ρ * symToeplitz3 1 ρ (ρ ^ 2) =
        (1 - ρ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symToeplitz3, kmsTridiagonalLaplacian3, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring
  have hKMS_02 : kmsTridiagonalLaplacian3 ρ 0 2 = 0 := by
    simp [kmsTridiagonalLaplacian3]
  have hKMS_20 : kmsTridiagonalLaplacian3 ρ 2 0 = 0 := by
    simp [kmsTridiagonalLaplacian3]
  have hKMS_defect : kmsTridiagonalLaplacian3 ρ 1 1 - kmsTridiagonalLaplacian3 ρ 0 0 = ρ ^ 2 := by
    simp [kmsTridiagonalLaplacian3]
  have hTorusNorm :
      (r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (r₂ * c₂) ^ 2 + (r₂ * s₂) ^ 2 = r₁ ^ 2 + r₂ ^ 2 := by
    calc
      (r₁ * c₁) ^ 2 + (r₁ * s₁) ^ 2 + (r₂ * c₂) ^ 2 + (r₂ * s₂) ^ 2 =
          r₁ ^ 2 * (c₁ ^ 2 + s₁ ^ 2) + r₂ ^ 2 * (c₂ ^ 2 + s₂ ^ 2) := by ring
      _ = r₁ ^ 2 * 1 + r₂ ^ 2 * 1 := by rw [hC1, hC2]
      _ = r₁ ^ 2 + r₂ ^ 2 := by ring
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
  have hJointChar :
      ZMod.stdAddChar (k_freq * (t₁ + t₂)) *
          (InfoGeometry.Canonical.V4GroupFourierTransform.v4Character m_v4 (g₁ * g₂) : ℂ) =
        (ZMod.stdAddChar (k_freq * t₁) *
          (InfoGeometry.Canonical.V4GroupFourierTransform.v4Character m_v4 g₁ : ℂ)) *
        (ZMod.stdAddChar (k_freq * t₂) *
          (InfoGeometry.Canonical.V4GroupFourierTransform.v4Character m_v4 g₂ : ℂ)) := by
    rw [mul_add, AddChar.map_add_eq_mul,
        InfoGeometry.Canonical.V4GroupFourierTransform.v4Character_mul m_v4 g₁ g₂]
    push_cast
    ring
  exact ⟨⟨hExcursion, hDel, hCommPlus, hCommMinus, hCommProd⟩,
         ⟨hLogPMI,
          hLogRatio,
          hSurp,
          InfoGeometry.Canonical.V4GroupFourierTransform.v4Fourier_inversion z_v4 g_v4⟩,
         ⟨hKMS_right, hKMS_left, hKMS_02, hKMS_20, hKMS_defect⟩,
         ⟨⟨hTorusNorm, hLissajous⟩, hJointChar⟩⟩

/--
**Theorem 7C (`𝔏𝔖₇` / `𝔊𝔔₁–𝔊𝔔₇` — `ls7_galois_quotient_dihedral_peter_weyl_and_surprisal_survival`):**
Unifies the three Galois–quotient representation-geometry laws in the `𝔏𝔖₇` master stage:
1. **Galois Stratification of `ℤ₁₂`, Integer Ramanujan Sums & `ZMod` Frequency Rescaling (`𝔊𝔔₁–𝔊𝔔₂`):**
   `Nat.totient 1 + Nat.totient 2 + Nat.totient 3 + Nat.totient 4 + Nat.totient 6 + Nat.totient 12 = 12`,
   `Nat.totient 12 = 4`, `(ℤ/12ℤ)^× = {1, 5, 7, 11} ≅ V₄` exponent-2 law, `σ₅` swapping `k = 1`
   and `k = 5` while fixing `k = 3` and `k = 6`, `ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x))`,
   and the integer Ramanujan divisor-shell orthogonality `∑_{d | 12} c_d(x) = 12 · δ_{x ≡ 0 mod 12}` on `Fin 12`.
2. **Non-Abelian Dihedral `D_N = ℤ_N ⋊ ℤ_2` `2 × 2` Peter–Weyl Peirce Block (`𝔊𝔔₃–𝔊𝔔₄`):**
   `invS P * peirceRotor2D P X Y c s * invS P = peirceRotor2D P X Y c (-s)`
   and `comm (invS P) (peirceRotor2D P X Y c s) = s * (genPhi P X Y + genPhi P X Y)`.
3. **Quotient Surprisal Normal Form & 2nd-Order Micro-Attribute Variance Survival (`𝔊𝔔₅–𝔊𝔔₇`):**
   For `L = surprisalNormalFormOp u_bar delta_u σ = u_bar + delta_u * σ` with `P_H * P_H = P_H`
   and `σ * σ = 1`:
   - Macro-attribute (`P_H * σ * P_H = σ * P_H`): `P_H * L * P_H = L * P_H`.
   - Micro-attribute (`P_H * σ * P_H = 0`): `P_H * L * P_H = u_bar * P_H` at 1st order, and
     `P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H` at 2nd order.
-/
theorem ls7_galois_quotient_dihedral_peter_weyl_and_surprisal_survival
    {N : ℕ} [NeZero N] (p k x : ZMod N)
    {B : Type*} [Ring B] (P X Y c s : B) (hP : P * P = P)
    (hc_S : invS P * c = c * invS P)
    (hs_S : invS P * s = s * invS P)
    (P_H u_bar delta_u σ : B)
    (hPH : P_H * P_H = P_H)
    (hσ2 : σ * σ = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_σ : u_bar * σ = σ * u_bar)
    (hd_σ : delta_u * σ = σ * delta_u) :
    (((Nat.totient 1 + Nat.totient 2 + Nat.totient 3 +
        Nat.totient 4 + Nat.totient 6 + Nat.totient 12 = 12 ∧
       Nat.totient 12 = 4 ∧
       (1 * 1) % 12 = 1 ∧ (5 * 5) % 12 = 1 ∧ (7 * 7) % 12 = 1 ∧ (11 * 11) % 12 = 1 ∧
       (5 * 1) % 12 = 5 ∧ (5 * 5) % 12 = 1 ∧
       (5 * 3) % 12 = 3 ∧ (5 * 6) % 12 = 6) ∧
      ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x))) ∧
     (∀ m : Fin 12,
       GaloisQuotientNonAbelianFourierPoset.ramanujanSum12 1 m.val +
       GaloisQuotientNonAbelianFourierPoset.ramanujanSum12 2 m.val +
       GaloisQuotientNonAbelianFourierPoset.ramanujanSum12 3 m.val +
       GaloisQuotientNonAbelianFourierPoset.ramanujanSum12 4 m.val +
       GaloisQuotientNonAbelianFourierPoset.ramanujanSum12 6 m.val +
       GaloisQuotientNonAbelianFourierPoset.ramanujanSum12 12 m.val =
         if m.val = 0 then 12 else 0)) ∧
    (invS P *
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c s *
        invS P =
      InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c (-s) ∧
     comm (invS P)
        (InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c s) =
      s * (genPhi P X Y + genPhi P X Y)) ∧
    (let L :=
       InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.surprisalNormalFormOp
         u_bar delta_u σ
     (P_H * σ * P_H = σ * P_H → P_H * L * P_H = L * P_H) ∧
     (P_H * σ * P_H = 0 →
       P_H * L * P_H = u_bar * P_H ∧
       P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H)) := by
  have hSynth :=
    InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.finite_arithmetic_peirce_and_compression_conjunction
      p k x P X Y c s hP hc_S hs_S P_H u_bar delta_u σ hPH hσ2 hu_P hd_P hu_σ hd_σ
  have hRamanujan :=
    GaloisQuotientNonAbelianFourierPoset.ramanujanSum12_divisor_shells_and_fourier_orthogonality.2.2
  exact ⟨⟨hSynth.1, hRamanujan⟩, hSynth.2.1, hSynth.2.2⟩

/--
**Theorem 7D (`ls7_cl11_tensor_stage_factorization_ramanujan24_and_peirce_compression_synthesis`):**
Packages the finite binary matrix stage tensor factorization from
`InfoGeometry.Clifford.Cl11TensorStageFactorization` (`stageTensorFactorization`,
`stageTensorFactorization_stageEmbed_tmul`, `factorizedStageToLimit_stageEmbed`) together with
the finite `N = 12` and `N = 24` Ramanujan divisor-sum calculations
(`z12_z24_divisor_ramanujan_sum_and_unit_residue_squares`) and the conditional Peirce reflected-rotor
norm and off-diagonal compression identities
(`peirce_reflected_rotor_norm_and_off_diagonal_compression_defect`). This theorem is
a conjunction of those finite-stage and conditional results and does not establish an
infinite-factor classification or a carrier map between the matrix-tower and ring parameters.
-/
theorem ls7_cl11_tensor_stage_factorization_ramanujan24_and_peirce_compression_synthesis
    (n m : ℕ)
    (A_st : InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
    (B_st : InfoGeometry.Clifford.Cl11TensorTower.MatStage m)
    (z_st : TensorProduct ℝ
      (InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
      (InfoGeometry.Clifford.Cl11TensorTower.MatStage m))
    {B : Type*} [Ring B] (P X Y c s : B) (hP : P * P = P)
    (hc_S : invS P * c = c * invS P)
    (hs_S : invS P * s = s * invS P)
    (hcs : c * s = s * c)
    (hc_J : c * genJ P X Y = genJ P X Y * c)
    (hs_J : s * genJ P X Y = genJ P X Y * s)
    (P_H u_bar delta_u : B)
    (hPH : P_H * P_H = P_H)
    (hPhi2 : genPhi P_H X Y * genPhi P_H X Y = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_Phi : u_bar * genPhi P_H X Y = genPhi P_H X Y * u_bar)
    (hd_Phi : delta_u * genPhi P_H X Y = genPhi P_H X Y * delta_u) :
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
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum12 1 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum12 2 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum12 3 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum12 4 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum12 6 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum12 12 x.val =
          if x.val = 0 then 12 else 0) ∧
     (∀ x : Fin 24,
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum24 1 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum24 2 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum24 3 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum24 4 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum24 6 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum24 8 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum24 12 x.val +
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.ramanujanSum24 24 x.val =
          if x.val = 0 then 24 else 0)) ∧
    (((InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c s * invS P) *
        invS P =
      InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c s ∧
     InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c s *
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c (-s) =
      c * c - s * s * (genJ P X Y * genJ P X Y) ∧
     (InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c s * invS P) *
        (InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c s * invS P) =
      c * c - s * s * (genJ P X Y * genJ P X Y)) ∧
    (let L :=
        InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.surprisalNormalFormOp
          u_bar delta_u (genPhi P_H X Y)
     P_H * genPhi P_H X Y * P_H = 0 ∧
     P_H * L * P_H = u_bar * P_H ∧
     P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) =
      (delta_u * delta_u) * P_H)) := by
  have hS2 : invS P * invS P = 1 := by
    peirce_nf hP
  have htwo :
      (InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c s * invS P) *
        invS P =
      InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirceRotor2D P X Y c s := by
    rw [mul_assoc, hS2, mul_one]
  have hStage :=
    InfoGeometry.Clifford.Cl11TensorStageFactorization.stageTensorFactorization_stageEmbed_tmul
      n m A_st B_st
  have hLimit :=
    InfoGeometry.Clifford.Cl11TensorStageFactorization.factorizedStageToLimit_stageEmbed
      n m z_st
  have hRam :=
    InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.z12_z24_divisor_ramanujan_sum_and_unit_residue_squares
  have hPeirce :=
    InfoGeometry.Canonical.LanguageStatisticsCirculantBirkhoffYangianPeircePoset.peirce_reflected_rotor_norm_and_off_diagonal_compression_defect
      P X Y c s hP hc_S hs_S hcs hc_J hs_J P_H u_bar delta_u hPH hPhi2 hu_P hd_P hu_Phi hd_Phi
  exact ⟨⟨hStage, hLimit⟩, ⟨hRam.2.2.1, hRam.2.2.2⟩, ⟨⟨htwo, hPeirce.1.2.1, hPeirce.1.2.2⟩, hPeirce.2⟩⟩

/--
**Theorem 7E (`ls7_wigner_clebsch_gordan_s4_zorn_cross_and_dressed_peirce_bott_synthesis`):**
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
theorem ls7_wigner_clebsch_gordan_s4_zorn_cross_and_dressed_peirce_bott_synthesis
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
        dressedPeirceProjector P M_op M_op ∧
     CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op *
        CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op =
        CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op ∧
     CliffordBottKTheoryWignerS4Poset.K_diag P
        (CliffordBottKTheoryWignerS4Poset.P_hat_KO P M_op - P) =
        - comm (conePlus P M_op) (coneMinus P M_op) ∧
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
**Theorem 7F (`ls7_wigner_hurwitz_adams_frobenius_pythagorean_and_d23_filter_synthesis`):**
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
theorem ls7_wigner_hurwitz_adams_frobenius_pythagorean_and_d23_filter_synthesis
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
**Theorem 7G (`ls7_pin_minus_88_octahedral_reflection_cl11_parity_time_and_abk_triality_synthesis`):**
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
theorem ls7_pin_minus_88_octahedral_reflection_cl11_parity_time_and_abk_triality_synthesis
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
**Theorem 7H (`ls7_kitaev_local_bulk_gap_collar_healing_and_universal_invertibility_rotor_synthesis`):**
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
theorem ls7_kitaev_local_bulk_gap_collar_healing_and_universal_invertibility_rotor_synthesis
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

end MasterLanguageSymmetryYangianPeirceSynthesis

end InfoGeometry.Canonical.LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset
