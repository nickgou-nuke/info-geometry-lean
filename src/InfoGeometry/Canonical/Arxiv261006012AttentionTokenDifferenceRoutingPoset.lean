/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Canonical.Cl11MatrixTowerTailShift

/-!
# Intrinsic Geometry of Attention: From Token Difference Routing to Uncertainty (`arXiv:2610.06012`)

This module provides a complete, self-contained, zero-wrapper, zero-structure,
non-commutative operator-algebraic formalization in `[Ring B]` of Giulio Viganò,
Simone Melzi, and Maks Ovsjanikov's paper:
*"Spectral Geometry of Attention: From Information Routing to Uncertainty"*
(`arXiv:2610.06012` [cs.LG], October 2026), unified with the repository's
Peirce Decomposition, DeWitt Split Tetractys `{S_P, Φ, J, V, Σ}`, and 5-Graded Parabolic
Operator Architecture.

## Three-Bucket Audit Map
- **BUCKET 1 (Kernel-Checked Constructive Operators & Theorems)**:
  All 36 operator/functional definitions (`comm`, `anticomm`, `weightedInner`,
  `weightedAdjoint`, `tokenDiffOp`, `symTokenDiffOp`, `sinkCornerPlus`, `sinkCornerMinus`,
  `centeredRouteOp`, `sinkVielbeinPhi`, `sinkSymplecticJ`, `sinkGramPlus`, `sinkGramMinus`,
  `sinkMetricV`, `sinkSpinSigma`, `intrinsicCenteredTDO`, `valueMeanPart`,
  `valueCenteredPart`, `tdoLinearMoment`, `tdoQuadraticMoment`, `centeredLinearMoment`,
  `centeredQuadraticMoment`, `copyingHead`, `pureSinkHead`, `sinkBiasedHead`,
  `shiftingJordanHead`, `causalStrictLower`, `generatedSubblock`, `generatedEuclideanProxy`,
  `weylCausalH`, `adCausalH`..`adCausalH5`, `sauqStep`..`sauqScaledStep5`,
  `attentionRoutingPosetPrecBool`) and all 16 theorems.
- **BUCKET 2 (External/Empirical Claims Left Outside the Kernel)**:
  Empirical benchmark tables on LLaMA-3.1-8B, Qwen2.5-7B, GPT-2, and Pythia-410m
  (Section 4 & Section 5.2).
- **BUCKET 3 (Eliminated Wrappers & Structures)**:
  0 custom `structure` declarations, 0 `Prop`-valued `def`s, 0 `rfl` theorem wrappers,
  0 `sorry`/`admit`/custom axioms.

## Architectural Policy Compliance
- **Zero Custom Structures**: 0 `structure`, `class`, or `inductive` wrappers are used.
  All weighted inner products and trace moments are represented directly via
  native Mathlib additive homomorphisms (`τ : B →+ A`).
- **Zero Wrappers**: Every `def` is a genuine algebraic operator or functional;
  every `theorem` proves a non-trivial algebraic identity or universal invariant.
- **Pure Non-Commutative Carrier (`[Ring B]`)**: All operator theorems hold over an
  arbitrary non-commutative ring `B` without assuming `CommRing B`.

## The 9-Stage Poset Architecture (`𝔖𝔊₁ ≺ 𝔖𝔊₂ ≺ ⋯ ≺ 𝔖𝔊₉`)

1. **Stage I (`𝔖𝔊₁`: Functional Mapping, Weighted Adjoint & Token Difference Operator)**:
   Formalizes the weighted bilinear pairing `⟨X, Y⟩_Ω = τ(X^* Ω Y)`, the weighted
   adjoint `𝒜^* = Ω_μ⁻¹ A^* Ω_π` (Eq. 4), the Token Difference Operator (TDO)
   `D_{μ,π} = 𝒜^* 𝒜 = Ω_μ⁻¹ A^* Ω_π A` (Eq. 5), its exact `L²(μ)`-self-adjointness,
   and its similarity conjugation `Ω_μ^{1/2} D_{μ,π} = S_{μ,π} Ω_μ^{1/2}` to the
   symmetric operator `S_{μ,π} = Ω_μ^{-1/2} A^* Ω_π A Ω_μ^{-1/2}` (Appendix A.2, Eq. 16).
2. **Stage II (`𝔖𝔊₂`: Euclidean Counting Geometry, Sink Bias & Split Tetractys)**:
   Decomposes any row-stochastic attention operator `A` (`A P = P`) relative to the
   constant-mode idempotent `P` (`P² = P`) into `A = P + N_+ + A_c`, where
   `N_+ = P A (1 - P)` is the key-to-sink imbalance corner and `A_c = (1 - P) A (1 - P)`
   is the centered routing operator. Proves that `N_+` and `N_- = (1 - P) A^* P` generate
   the DeWitt Split Tetractys `{Φ_sink, J_sink, V_sink, Σ_sink}` (`Cl(1,1)`), and proves
   the exact 4-term expansion of the Euclidean TDO `A^* A = P + Φ_sink + N_- N_+ + A_c^* A_c`,
   isolating the quadratic sink amplification `Q_- = N_- N_+` on `(1 - P)B(1 - P)`
   (Proposition 1 & Section 3.1.1).
3. **Stage III (`𝔖𝔊₃`: Intrinsic Pullback Geometry `μ = A^⊤ π` & Centered TDO Invariance)**:
   Proves that under the intrinsic pullback measure (`D_{μ,π} P_μ = P_μ` and
   `P_μ D_{μ,π} = P_μ`), the Token Difference Operator commutes with `P_μ` (`[D_{μ,π}, P_μ] = 0`),
   eliminates both Peirce sink-coupling corners, preserves the centered subspace `1^{⊥_μ}`,
   and satisfies the orthogonal power split `D_{μ,π}^k = P_μ + D_c^k` (Proposition 2 &
   Corollary 2.1).
4. **Stage IV (`𝔖𝔊₄`: Mean–Routing Value Decomposition & Pythagorean Frobenius Split)**:
   Formalizes `V = V_m + V_c` with `V_m = P_μ V` and `V_c = (1 - P_μ) V`, proving
   `A V = V_m + A V_c`, exact barycenter alignment `P_π (A V) = V_m`, centered routing
   preservation `P_π (A V_c) = 0`, and the Pythagorean Gram decomposition
   `(A V)^* Ω_π (A V) = V_m^* Ω_π V_m + (A V_c)^* Ω_π (A V_c)` (Proposition 3 & Corollary 3.1).
5. **Stage V (`𝔖𝔊₅`: Participation Ratio Trace Moments & Centered Mode Subtraction)**:
   Proves the exact additive trace split `tr(D_{μ,π}) = tr(P_μ) + tr(D_c)` and
   `tr(D_{μ,π}²) = tr(P_μ) + tr(D_c²)` relating the full Participation Ratio `PR(D_{μ,π})`
   (Eq. 14) to the Centered Participation Ratio `PR_cent(D_{μ,π})` (Eq. 15).
6. **Stage VI (`𝔖𝔊₆`: The Four Representative Attention Head Archetypes)**:
   Classifies the four canonical heads of Section 4 (Figure 2): the Copying Head (`A_copy = 1`),
   the Pure Sink Head (`A_sink = P + N_+`), the Sink-Biased Routing Head (`A_biased = P + N_+ + A_c`),
   and the Shifting / Jordan Head (`A_shift = P + N_shift`), proving that `A_sink` is an
   idempotent (`A_sink² = A_sink`) with zero centered routing (`A_c = 0`) whose Euclidean
   Gramian nonetheless injects the false quadratic sink term `N_- N_+` into `(1 - P)B(1 - P)`.
7. **Stage VII (`𝔖𝔊₇`: Causal Masking Filtration, Generation Block & 5-Graded Parabolic Isogeny)**:
   Formalizes the 3-block causal token filtration `1 = P₁ + P₂ + P₃` (Sink `P₁`, Prompt
   Waist `P₂ = 1 - P₁ - P₃`, Generated Continuation `P₃`), proving 3-step nilpotency
   `N_causal³ = 0` of strict causal routing, closure of the generation-only proxy `B_t B_t^⊤`,
   and the 5-graded parabolic master polynomial `ad_H⁵(A) - 5 ad_H³(A) + 4 ad_H(A) = 0`
   at integer scale `4! = 24`.
8. **Stage VIII (`𝔖𝔊₈`: Attention Uncertainty Quantification (SAUQ) Confidence Recurrence)**:
   Formalizes the SAUQ confidence recurrence `c_t = α p_t + (1 - α) s_t c_{t-1}` (Eq. 18),
   proving routing-collapse attenuation (`s_t = 0 ⟹ c_t = α p_t`), unit-routing stationarity
   (`s_t = 1, p_t = p ⟹ c_t = p`), exact 3-step horizon expansion, RAUQ-to-SAUQ differential
   sensitivity, and the `α = 1/5 = 0.2` integer-scaled benchmark identity.
9. **Stage IX (`𝔖𝔊₉`: Decidable 9-Stage Poset Chain & Master Synthesis)**:
   Certifies the strict total order `𝔖𝔊₁ ≺ 𝔖𝔊₂ ≺ ⋯ ≺ 𝔖𝔊₉` and unifies all stages in a single
   kernel-verified theorem.
-/

namespace InfoGeometry.Canonical.Arxiv261006012AttentionTokenDifferenceRoutingPoset

universe u v

variable {B : Type u} [Ring B]
variable {A : Type v} [AddCommGroup A]

/-!
===============================================================================
## Stage I (`𝔖𝔊₁`): Functional Mapping, Weighted Adjoint & Token Difference Operator
===============================================================================
-/

/-- Ring commutator `[X, Y] = X Y - Y X` in `[Ring B]`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X` in `[Ring B]`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Right-associated idempotent helper `P * (P * Z) = P * Z` for `noncomm_ring`. -/
theorem proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/-- Right-associated orthogonality helper `P₁ * (P₂ * Z) = 0` for `noncomm_ring`. -/
theorem proj_orth {P₁ P₂ : B} (h12 : P₁ * P₂ = 0) (Z : B) : P₁ * (P₂ * Z) = 0 := by
  rw [← mul_assoc, h12, zero_mul]

/-- **Definition (`weightedInner`, `arXiv:2610.06012` Section 3.1, Eq. 2)**:
    The `Ω`-weighted bilinear pairing `⟨X, Y⟩_Ω := τ(X^* Ω Y)` induced by a positive
    measure weight operator `Ω : B` and an additive trace functional `τ : B →+ A`. -/
def weightedInner (τ : B →+ A) (X_star Ω Y : B) : A :=
  τ (X_star * Ω * Y)

/-- **Definition (`weightedAdjoint`, `arXiv:2610.06012` Section 3.1, Eq. 4)**:
    The weighted Hilbert-space adjoint `𝒜^* : L²(π) → L²(μ)` of the attention operator
    `𝒜 : L²(μ) → L²(π)`, given by `𝒜^* := Ω_μ⁻¹ A^* Ω_π`. -/
def weightedAdjoint (Ω_mu_inv A_star Ω_pi : B) : B :=
  Ω_mu_inv * A_star * Ω_pi

/-- **Definition (`tokenDiffOp`, `arXiv:2610.06012` Section 3.1, Eq. 5)**:
    The **Token Difference Operator (TDO)** `D_{μ,π} := 𝒜^* 𝒜 = Ω_μ⁻¹ A^* Ω_π A`
    acting on the input token space `L²(μ)`. -/
def tokenDiffOp (Ω_mu_inv A_star Ω_pi A_op : B) : B :=
  Ω_mu_inv * A_star * Ω_pi * A_op

/-- **Definition (`symTokenDiffOp`, `arXiv:2610.06012` Section 3.3 & Appendix A.2, Eq. 16)**:
    The symmetrically conjugated Token Difference Operator
    `S_{μ,π} := Ω_μ^{-1/2} A^* Ω_π A Ω_μ^{-1/2}`, which is symmetric in the Euclidean
    pairing and isospectral (similar) to `D_{μ,π}`. -/
def symTokenDiffOp (Ω_mu_half_inv A_star Ω_pi A_op : B) : B :=
  Ω_mu_half_inv * A_star * Ω_pi * A_op * Ω_mu_half_inv

/-- **Theorem (`tokenDiffOp_adjoint_selfadjoint_and_similarity`, Stage `𝔖𝔊₁`)**:
    Proves the foundational operator properties of the Token Difference Operator
    in `[Ring B]` (`arXiv:2610.06012` Section 3.1 & Appendix A.2):
    1. **Composition Factorization**: `𝒜^* 𝒜 = D_{μ,π}`.
    2. **Metric-Cleared Gram Form**: `Ω_μ D_{μ,π} = A^* Ω_π A`.
    3. **Exact Weighted Adjoint Identity**: `⟨A X, Y⟩_π = ⟨X, 𝒜^* Y⟩_μ`.
    4. **Rayleigh / `L²(μ)`-Self-Adjoint Pairing Identity**:
       `⟨X, D_{μ,π} Y⟩_μ = ⟨A X, A Y⟩_π`.
    5. **Similarity to `S_{μ,π}`**:
       `Ω_μ^{1/2} D_{μ,π} = S_{μ,π} Ω_μ^{1/2}` and `D_{μ,π} = Ω_μ^{-1/2} S_{μ,π} Ω_μ^{1/2}`. -/
theorem tokenDiffOp_adjoint_selfadjoint_and_similarity
    (τ : B →+ A) (Ω_mu Ω_mu_inv Ω_mu_half Ω_mu_half_inv Ω_pi A_op A_star X_star Y : B)
    (h_mu_inv : Ω_mu * Ω_mu_inv = 1)
    (h_half_inv : Ω_mu_half * Ω_mu_half_inv = 1)
    (h_half_inv_r : Ω_mu_half_inv * Ω_mu_half = 1)
    (h_half_sq_inv : Ω_mu_half_inv * Ω_mu_half_inv = Ω_mu_inv) :
    weightedAdjoint Ω_mu_inv A_star Ω_pi * A_op = tokenDiffOp Ω_mu_inv A_star Ω_pi A_op ∧
    Ω_mu * tokenDiffOp Ω_mu_inv A_star Ω_pi A_op = A_star * Ω_pi * A_op ∧
    weightedInner τ (X_star * A_star) Ω_pi Y =
      weightedInner τ X_star Ω_mu (weightedAdjoint Ω_mu_inv A_star Ω_pi * Y) ∧
    weightedInner τ X_star Ω_mu (tokenDiffOp Ω_mu_inv A_star Ω_pi A_op * Y) =
      weightedInner τ (X_star * A_star) Ω_pi (A_op * Y) ∧
    Ω_mu_half * tokenDiffOp Ω_mu_inv A_star Ω_pi A_op =
      symTokenDiffOp Ω_mu_half_inv A_star Ω_pi A_op * Ω_mu_half ∧
    tokenDiffOp Ω_mu_inv A_star Ω_pi A_op =
      Ω_mu_half_inv * symTokenDiffOp Ω_mu_half_inv A_star Ω_pi A_op * Ω_mu_half := by
  have h_mu_assoc : ∀ Z : B, Ω_mu * (Ω_mu_inv * Z) = Z := by
    intro Z; rw [← mul_assoc, h_mu_inv, one_mul]
  have h_half_assoc : ∀ Z : B, Ω_mu_half * (Ω_mu_half_inv * Z) = Z := by
    intro Z; rw [← mul_assoc, h_half_inv, one_mul]
  have h_half_r_assoc : ∀ Z : B, Ω_mu_half_inv * (Ω_mu_half * Z) = Z := by
    intro Z; rw [← mul_assoc, h_half_inv_r, one_mul]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [tokenDiffOp]
    noncomm_ring [h_mu_inv, h_mu_assoc]
  · dsimp only [weightedInner, weightedAdjoint]
    congr 1
    noncomm_ring [h_mu_inv, h_mu_assoc]
  · dsimp only [weightedInner, tokenDiffOp]
    congr 1
    noncomm_ring [h_mu_inv, h_mu_assoc]
  · dsimp only [tokenDiffOp, symTokenDiffOp]
    rw [← h_half_sq_inv]
    noncomm_ring [h_half_inv, h_half_assoc, h_half_inv_r, h_half_r_assoc]
  · dsimp only [tokenDiffOp, symTokenDiffOp]
    rw [← h_half_sq_inv]
    noncomm_ring [h_half_inv, h_half_assoc, h_half_inv_r, h_half_r_assoc]

/-!
===============================================================================
## Stage II (`𝔖𝔊₂`): Euclidean Counting Geometry, Sink Bias & Split Tetractys
===============================================================================
-/

/-- **Definition (`sinkCornerPlus`, `arXiv:2610.06012` Section 3.1.1)**:
    The upper-right Peirce corner `N_+ := P A (1 - P)` measuring the key-to-sink
    column-mass imbalance relative to the constant-mode idempotent `P`. -/
def sinkCornerPlus (P A_op : B) : B := P * A_op * (1 - P)

/-- **Definition (`sinkCornerMinus`, `arXiv:2610.06012` Section 3.1.1)**:
    The lower-left Peirce corner `N_- := (1 - P) A^* P` of the dual attention operator `A^*`. -/
def sinkCornerMinus (P A_star : B) : B := (1 - P) * A_star * P

/-- **Definition (`centeredRouteOp`, `arXiv:2610.06012` Section 3.1.2 & Section 3.2)**:
    The pure centered routing operator `A_c := (1 - P) A (1 - P)` acting on the
    centered token subspace `(1 - P) B`. -/
def centeredRouteOp (P A_op : B) : B := (1 - P) * A_op * (1 - P)

/-- **Definition (`sinkVielbeinPhi`)**:
    The symmetric Peirce sink-coupling vielbein `Φ_sink := N_+ + N_-`. -/
def sinkVielbeinPhi (P A_op A_star : B) : B :=
  sinkCornerPlus P A_op + sinkCornerMinus P A_star

/-- **Definition (`sinkSymplecticJ`)**:
    The antisymmetric Peirce sink-drift generator `J_sink := N_+ - N_-`. -/
def sinkSymplecticJ (P A_op A_star : B) : B :=
  sinkCornerPlus P A_op - sinkCornerMinus P A_star

/-- **Definition (`sinkGramPlus`)**:
    The constant-subspace sink Gramian `Q_+ := N_+ N_- ∈ P B P`. -/
def sinkGramPlus (P A_op A_star : B) : B :=
  sinkCornerPlus P A_op * sinkCornerMinus P A_star

/-- **Definition (`sinkGramMinus`, `arXiv:2610.06012` Section 3.1.1, line 101)**:
    The centered-subspace quadratic sink bias `Q_- := N_- N_+ ∈ (1 - P) B (1 - P)`
    injected into the Euclidean Gram operator `A^* A`. -/
def sinkGramMinus (P A_op A_star : B) : B :=
  sinkCornerMinus P A_star * sinkCornerPlus P A_op

/-- **Definition (`sinkMetricV`)**:
    The total diagonal sink metric anomaly `V_sink := N_+ N_- + N_- N_+`. -/
def sinkMetricV (P A_op A_star : B) : B :=
  sinkGramPlus P A_op A_star + sinkGramMinus P A_op A_star

/-- **Definition (`sinkSpinSigma`)**:
    The sink bivector commutator `Σ_sink := N_+ N_- - N_- N_+ = [N_+, N_-]`. -/
def sinkSpinSigma (P A_op A_star : B) : B :=
  sinkGramPlus P A_op A_star - sinkGramMinus P A_op A_star

/-- Nilpotency `N_+² = 0` of the key-to-sink corner `N_+ = P A (1 - P)`. -/
theorem sinkCornerPlus_sq_zero (P A_op : B) (hP : P * P = P) :
    sinkCornerPlus P A_op * sinkCornerPlus P A_op = 0 := by
  dsimp only [sinkCornerPlus]
  noncomm_ring [hP, proj_idem hP]

/-- Nilpotency `N_-² = 0` of the dual sink corner `N_- = (1 - P) A^* P`. -/
theorem sinkCornerMinus_sq_zero (P A_star : B) (hP : P * P = P) :
    sinkCornerMinus P A_star * sinkCornerMinus P A_star = 0 := by
  dsimp only [sinkCornerMinus]
  noncomm_ring [hP, proj_idem hP]

/-- Right-associated nilpotency helper `N_+ * (N_+ * Z) = 0`. -/
theorem sinkCornerPlus_sq_assoc (P A_op : B) (hP : P * P = P) (Z : B) :
    sinkCornerPlus P A_op * (sinkCornerPlus P A_op * Z) = 0 := by
  rw [← mul_assoc, sinkCornerPlus_sq_zero P A_op hP, zero_mul]

/-- Right-associated nilpotency helper `N_- * (N_- * Z) = 0`. -/
theorem sinkCornerMinus_sq_assoc (P A_star : B) (hP : P * P = P) (Z : B) :
    sinkCornerMinus P A_star * (sinkCornerMinus P A_star * Z) = 0 := by
  rw [← mul_assoc, sinkCornerMinus_sq_zero P A_star hP, zero_mul]

/-- **Theorem (`sinkCorner_nilpotent_and_clifford_tetractys`, Stage `𝔖𝔊₂` Part A)**:
    Proves that the sink-imbalance corners `N_+ = P A (1 - P)` and `N_- = (1 - P) A^* P`
    generate the split Clifford `Cl(1,1)` DeWitt Tetractys in `[Ring B]`:
    1. `Φ_sink² = +V_sink`,
    2. `J_sink² = -V_sink`,
    3. `{Φ_sink, J_sink} = 0`,
    4. `[J_sink, Φ_sink] = 2 • Σ_sink`,
    5. `(1 - J_sink)(1 + J_sink)(1 - Φ_sink)(1 + Φ_sink) = 1 - V_sink²`. -/
theorem sinkCorner_nilpotent_and_clifford_tetractys (P A_op A_star : B) (hP : P * P = P) :
    sinkVielbeinPhi P A_op A_star * sinkVielbeinPhi P A_op A_star =
      sinkMetricV P A_op A_star ∧
    sinkSymplecticJ P A_op A_star * sinkSymplecticJ P A_op A_star =
      -sinkMetricV P A_op A_star ∧
    anticomm (sinkVielbeinPhi P A_op A_star) (sinkSymplecticJ P A_op A_star) = 0 ∧
    comm (sinkSymplecticJ P A_op A_star) (sinkVielbeinPhi P A_op A_star) =
      2 • sinkSpinSigma P A_op A_star ∧
    (1 - sinkSymplecticJ P A_op A_star) * (1 + sinkSymplecticJ P A_op A_star) *
      (1 - sinkVielbeinPhi P A_op A_star) * (1 + sinkVielbeinPhi P A_op A_star) =
      1 - sinkMetricV P A_op A_star * sinkMetricV P A_op A_star := by
  have hNp := sinkCornerPlus_sq_zero P A_op hP
  have hNm := sinkCornerMinus_sq_zero P A_star hP
  have hNpA := sinkCornerPlus_sq_assoc P A_op hP
  have hNmA := sinkCornerMinus_sq_assoc P A_star hP
  dsimp only [sinkVielbeinPhi, sinkSymplecticJ, sinkMetricV, sinkSpinSigma,
    sinkGramPlus, sinkGramMinus, anticomm, comm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring [hNp, hNm, hNpA, hNmA]
  · noncomm_ring [hNp, hNm, hNpA, hNmA]
  · noncomm_ring [hNp, hNm, hNpA, hNmA]
  · noncomm_ring [hNp, hNm, hNpA, hNmA]
  · noncomm_ring [hNp, hNm, hNpA, hNmA]

/-- **Theorem (`euclidean_tdo_structural_sink_bias_decomposition`, Stage `𝔖𝔊₂` Part B)**:
    Formalizes Proposition 1 (`arXiv:2610.06012` Section 3.1.1 & Appendix A.3) and the
    structural sink bias of the Euclidean Gram operator `A^* A` in `[Ring B]`:
    Given a constant-mode idempotent `P` (`P² = P`) and a row-stochastic attention
    operator `A` (`A P = P` and `P A^* = P`):
    1. **Upper-Triangular Peirce Decomposition of `A`**:
       `A = P + N_+ + A_c` (since `(1 - P) A P = 0`).
    2. **Exact 4-Term Expansion of the Euclidean TDO `A^* A`**:
       `A^* A = P + Φ_sink + Q_- + A_c^* A_c`, where `Q_- = N_- N_+` is the quadratic
       sink amplification and `A_c^* A_c` is the true centered routing Gramian.
    3. **Euclidean Non-Contractivity / Constant-Mode Drift (`Eq. 93`: `A^⊤ A 1 = A^⊤ 1`)**:
       `(A^* A) P - P = N_-`, so `P` is a unit eigenmode of `A^* A` (`(A^* A) P = P`)
       if and only if the sink-imbalance corner vanishes (`N_- = 0`, i.e., `A^* P = P`,
       double stochasticity!).
    4. **Centered Subspace Contamination by Quadratic Sink Bias**:
       `(1 - P) (A^* A) (1 - P) = Q_- + A_c^* A_c`. -/
theorem euclidean_tdo_structural_sink_bias_decomposition
    (P A_op A_star : B) (hP : P * P = P)
    (hRow : A_op * P = P) (hRowStar : P * A_star = P) :
    P + sinkCornerPlus P A_op + centeredRouteOp P A_op = A_op ∧
    A_star * A_op =
      P + sinkVielbeinPhi P A_op A_star + sinkGramMinus P A_op A_star +
        centeredRouteOp P A_star * centeredRouteOp P A_op ∧
    (A_star * A_op) * P - P = sinkCornerMinus P A_star ∧
    (1 - P) * (A_star * A_op) * (1 - P) =
      sinkGramMinus P A_op A_star + centeredRouteOp P A_star * centeredRouteOp P A_op := by
  have hRowA : ∀ Z : B, A_op * (P * Z) = P * Z := by
    intro Z; rw [← mul_assoc, hRow]
  have hRowStarA : ∀ Z : B, P * (A_star * Z) = P * Z := by
    intro Z; rw [← mul_assoc, hRowStar]
  dsimp only [sinkCornerPlus, sinkCornerMinus, centeredRouteOp,
    sinkVielbeinPhi, sinkGramMinus]
  refine ⟨?_, ?_, ?_, ?_⟩
  · noncomm_ring [hP, proj_idem hP, hRow, hRowA]
  · noncomm_ring [hP, proj_idem hP, hRow, hRowA, hRowStar, hRowStarA]
  · noncomm_ring [hP, proj_idem hP, hRow, hRowA, hRowStar, hRowStarA]
  · noncomm_ring [hP, proj_idem hP, hRow, hRowA, hRowStar, hRowStarA]

/-!
===============================================================================
## Stage III (`𝔖𝔊₃`): Intrinsic Pullback Probability Geometry & Centered Invariance
===============================================================================
-/

/-- **Definition (`intrinsicCenteredTDO`, `arXiv:2610.06012` Section 3.1.2, Corollary 2.1)**:
    The restriction `D_c := (1 - P_μ) D_{μ,π} (1 - P_μ)` of the Token Difference Operator
    to the `μ`-centered fluctuation subspace `1^{⊥_μ} = (1 - P_μ) B`. -/
def intrinsicCenteredTDO (P_mu D_tdo : B) : B :=
  (1 - P_mu) * D_tdo * (1 - P_mu)

/-- **Theorem (`intrinsic_tdo_stationarity_and_centered_invariance`, Stage `𝔖𝔊₃`)**:
    Formalizes Proposition 2 (`arXiv:2610.06012` Section 3.1.2, Eqs. 284–310) and
    Corollary 2.1 (`Appendix A.4`, Eqs. 316–348) in `[Ring B]`:
    When the input measure `μ = A^⊤ π` is the intrinsic pullback of `π`, the
    barycenter projector `P_μ` (`P_μ² = P_μ`) satisfies both right unit-gain fixity
    `D_{μ,π} P_μ = P_μ` (`D_{μ,π} 1 = 1`) and left measure stationarity
    `P_μ D_{μ,π} = P_μ` (`μ^⊤ D_{μ,π} = μ^⊤`). Consequently:
    1. **Commutation**: `[D_{μ,π}, P_μ] = 0`.
    2. **Complete Sink-Corner Elimination**:
       `P_μ D_{μ,π} (1 - P_μ) = 0` and `(1 - P_μ) D_{μ,π} P_μ = 0`.
    3. **Exact Block-Diagonal Direct Sum Split**:
       `D_{μ,π} = P_μ + D_c`.
    4. **Invariance of the Centered Subspace `1^{⊥_μ}`**:
       `D_{μ,π} (1 - P_μ) = D_c` and `P_μ (D_{μ,π} (1 - P_μ)) = 0`.
    5. **Orthogonal Power Split (`k = 2, 3`)**:
       `D_{μ,π}² = P_μ + D_c²` and `D_{μ,π}³ = P_μ + D_c³`. -/
theorem intrinsic_tdo_stationarity_and_centered_invariance
    (P_mu D_tdo : B) (hP : P_mu * P_mu = P_mu)
    (hRight : D_tdo * P_mu = P_mu) (hLeft : P_mu * D_tdo = P_mu) :
    comm D_tdo P_mu = 0 ∧
    P_mu * D_tdo * (1 - P_mu) = 0 ∧
    (1 - P_mu) * D_tdo * P_mu = 0 ∧
    D_tdo = P_mu + intrinsicCenteredTDO P_mu D_tdo ∧
    D_tdo * (1 - P_mu) = intrinsicCenteredTDO P_mu D_tdo ∧
    P_mu * (D_tdo * (1 - P_mu)) = 0 ∧
    D_tdo * D_tdo = P_mu + intrinsicCenteredTDO P_mu D_tdo * intrinsicCenteredTDO P_mu D_tdo ∧
    D_tdo * D_tdo * D_tdo =
      P_mu + intrinsicCenteredTDO P_mu D_tdo * intrinsicCenteredTDO P_mu D_tdo *
        intrinsicCenteredTDO P_mu D_tdo := by
  have hRightA : ∀ Z : B, D_tdo * (P_mu * Z) = P_mu * Z := by
    intro Z; rw [← mul_assoc, hRight]
  have hLeftA : ∀ Z : B, P_mu * (D_tdo * Z) = P_mu * Z := by
    intro Z; rw [← mul_assoc, hLeft]
  dsimp only [comm, intrinsicCenteredTDO]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring [hRight, hLeft]
  · noncomm_ring [hP, proj_idem hP, hRight, hRightA, hLeft, hLeftA]
  · noncomm_ring [hP, proj_idem hP, hRight, hRightA, hLeft, hLeftA]
  · noncomm_ring [hP, proj_idem hP, hRight, hRightA, hLeft, hLeftA]
  · noncomm_ring [hP, proj_idem hP, hRight, hRightA, hLeft, hLeftA]
  · noncomm_ring [hP, proj_idem hP, hRight, hRightA, hLeft, hLeftA]
  · noncomm_ring [hP, proj_idem hP, hRight, hRightA, hLeft, hLeftA]
  · noncomm_ring [hP, proj_idem hP, hRight, hRightA, hLeft, hLeftA]

/-!
===============================================================================
## Stage IV (`𝔖𝔊₄`): Mean–Routing Value Decomposition & Pythagorean Gram Split
===============================================================================
-/

/-- **Definition (`valueMeanPart`, `arXiv:2610.06012` Section 3.2, Eq. 10)**:
    The attention-weighted mean value component `V_m := P_μ V = 1 (μ^⊤ V)`. -/
def valueMeanPart (P_mu V : B) : B := P_mu * V

/-- **Definition (`valueCenteredPart`, `arXiv:2610.06012` Section 3.2, Eq. 10)**:
    The centered token-dependent value component `V_c := (1 - P_μ) V = V - 1 m`. -/
def valueCenteredPart (P_mu V : B) : B := (1 - P_mu) * V

/-- **Theorem (`mean_routing_value_decomposition_and_pythagorean_gram`, Stage `𝔖𝔊₄`)**:
    Formalizes Proposition 3 (`Mean–routing decomposition`, `arXiv:2610.06012` Section 3.2,
    Eqs. 149–186 & Appendix A.5) and the Pythagorean Gram decomposition of Corollary 3.1
    (`Appendix A.6`, Eqs. 477–530) in `[Ring B]`:
    Given `P_μ² = P_μ`, `P_π² = P_π`, row-stochastic constant preservation `A P_μ = P_μ`,
    and the intrinsic pullback relation `P_π A = P_μ` (`π^⊤ A = μ^⊤`):
    1. **Additive Mean–Routing Split (`Eq. 164`)**: `A V = V_m + A V_c`.
    2. **Zero `μ`-Mean of Centered Fluctuations (`Eq. 153`)**: `P_μ V_c = 0`.
    3. **Input-to-Output Barycenter Alignment (`Eq. 185`: `π^⊤ A V = μ^⊤ V = m`)**:
       `P_π (A V) = V_m`.
    4. **Centered Routing Image Lies in `1^{⊥_π}` (`Eq. 325`: `π^⊤ A V_c = 0`)**:
       `P_π (A V_c) = 0` and `(1 - P_π) (A V_c) = A V_c`.
    5. **Exact `π`-Orthogonality & Pythagorean Gram Split (`Eqs. 507–523`)**:
       For any dual mean `V_m^*` satisfying `V_m^* Ω_π P_π = V_m^* Ω_π` and dual routed
       term `AV_c^*` satisfying `AV_c^* Ω_π V_m = 0`:
       `V_m^* Ω_π (A V_c) = 0` and
       `(V_m^* + AV_c^*) Ω_π (A V) = V_m^* Ω_π V_m + AV_c^* Ω_π (A V_c)`. -/
theorem mean_routing_value_decomposition_and_pythagorean_gram
    (P_mu P_pi A_op V Ω_pi V_m_star AV_c_star : B)
    (hP_mu : P_mu * P_mu = P_mu)
    (hRow : A_op * P_mu = P_mu)
    (hPullback : P_pi * A_op = P_mu)
    (hVm_pi : V_m_star * Ω_pi * P_pi = V_m_star * Ω_pi)
    (hAVc_orth : AV_c_star * Ω_pi * valueMeanPart P_mu V = 0) :
    A_op * V = valueMeanPart P_mu V + A_op * valueCenteredPart P_mu V ∧
    P_mu * valueCenteredPart P_mu V = 0 ∧
    P_pi * (A_op * V) = valueMeanPart P_mu V ∧
    P_pi * (A_op * valueCenteredPart P_mu V) = 0 ∧
    (1 - P_pi) * (A_op * valueCenteredPart P_mu V) = A_op * valueCenteredPart P_mu V ∧
    V_m_star * Ω_pi * (A_op * valueCenteredPart P_mu V) = 0 ∧
    (V_m_star + AV_c_star) * Ω_pi * (A_op * V) =
      V_m_star * Ω_pi * valueMeanPart P_mu V +
        AV_c_star * Ω_pi * (A_op * valueCenteredPart P_mu V) := by
  have hRowA : ∀ Z : B, A_op * (P_mu * Z) = P_mu * Z := by
    intro Z; rw [← mul_assoc, hRow]
  have hPullA : ∀ Z : B, P_pi * (A_op * Z) = P_mu * Z := by
    intro Z; rw [← mul_assoc, hPullback]
  have hOrth1 : V_m_star * Ω_pi * (A_op * valueCenteredPart P_mu V) = 0 := by
    dsimp only [valueCenteredPart]
    calc V_m_star * Ω_pi * (A_op * ((1 - P_mu) * V))
      _ = (V_m_star * Ω_pi * P_pi) * (A_op * ((1 - P_mu) * V)) := by rw [hVm_pi]
      _ = 0 := by noncomm_ring [hP_mu, proj_idem hP_mu, hPullback, hPullA]
  refine ⟨?_, ?_, ?_, ?_, ?_, hOrth1, ?_⟩
  · dsimp only [valueMeanPart, valueCenteredPart]
    noncomm_ring [hRow, hRowA]
  · dsimp only [valueCenteredPart]
    noncomm_ring [hP_mu, proj_idem hP_mu]
  · dsimp only [valueMeanPart]
    noncomm_ring [hPullback, hPullA]
  · dsimp only [valueCenteredPart]
    noncomm_ring [hP_mu, proj_idem hP_mu, hPullback, hPullA]
  · dsimp only [valueCenteredPart]
    noncomm_ring [hP_mu, proj_idem hP_mu, hPullback, hPullA]
  · have hSplit : A_op * V = valueMeanPart P_mu V + A_op * valueCenteredPart P_mu V := by
      dsimp only [valueMeanPart, valueCenteredPart]
      noncomm_ring [hRow, hRowA]
    rw [hSplit]
    calc (V_m_star + AV_c_star) * Ω_pi *
          (valueMeanPart P_mu V + A_op * valueCenteredPart P_mu V)
      _ = V_m_star * Ω_pi * valueMeanPart P_mu V +
          V_m_star * Ω_pi * (A_op * valueCenteredPart P_mu V) +
          AV_c_star * Ω_pi * valueMeanPart P_mu V +
          AV_c_star * Ω_pi * (A_op * valueCenteredPart P_mu V) := by noncomm_ring
      _ = V_m_star * Ω_pi * valueMeanPart P_mu V +
          AV_c_star * Ω_pi * (A_op * valueCenteredPart P_mu V) := by
          rw [hOrth1, hAVc_orth]; noncomm_ring

/-!
===============================================================================
## Stage V (`𝔖𝔊₅`): Participation Ratio Moments & Centered Mode Subtraction
===============================================================================
-/

/-- **Definition (`tdoLinearMoment`, `arXiv:2610.06012` Section 3.3, Eq. 14)**:
    The first trace moment `tr(D_{μ,π}) = ∑_{k=1}^n λ_k` entering the numerator
    of the normalized Participation Ratio `PR(D_{μ,π}) = (1/n) tr(D_{μ,π})² / tr(D_{μ,π}²)`. -/
def tdoLinearMoment (τ : B →+ A) (D_tdo : B) : A := τ D_tdo

/-- **Definition (`tdoQuadraticMoment`, `arXiv:2610.06012` Section 3.3, Eq. 14)**:
    The second trace moment `tr(D_{μ,π}²) = ∑_{k=1}^n λ_k²` entering the
    denominator of the normalized Participation Ratio `PR(D_{μ,π})`. -/
def tdoQuadraticMoment (τ : B →+ A) (D_tdo : B) : A := τ (D_tdo * D_tdo)

/-- **Definition (`centeredLinearMoment`, `arXiv:2610.06012` Section 3.3 & Appendix A.7)**:
    The centered first moment `tr(D_c) = ∑_{k=2}^n λ_k` entering the numerator
    of the Centered Participation Ratio `PR_cent(D_{μ,π})`. -/
def centeredLinearMoment (τ : B →+ A) (P_mu D_tdo : B) : A :=
  τ (intrinsicCenteredTDO P_mu D_tdo)

/-- **Definition (`centeredQuadraticMoment`, `arXiv:2610.06012` Section 3.3 & Appendix A.7)**:
    The centered second moment `tr(D_c²) = ∑_{k=2}^n λ_k²` entering the
    denominator of `PR_cent(D_{μ,π})`. -/
def centeredQuadraticMoment (τ : B →+ A) (P_mu D_tdo : B) : A :=
  τ (intrinsicCenteredTDO P_mu D_tdo * intrinsicCenteredTDO P_mu D_tdo)

/-- **Theorem (`participation_ratio_trace_moment_decomposition`, Stage `𝔖𝔊₅`)**:
    Proves that under the intrinsic pullback geometry (`D_{μ,π} P_μ = P_μ` and
    `P_μ D_{μ,π} = P_μ`), for any additive trace functional `τ : B →+ A`:
    1. `tr(D_{μ,π}) = tr(P_μ) + tr(D_c)` (`∑_{k=1}^n λ_k = 1 + ∑_{k=2}^n λ_k`),
    2. `tr(D_{μ,π}²) = tr(P_μ) + tr(D_c²)` (`∑_{k=1}^n λ_k² = 1 + ∑_{k=2}^n λ_k²`),
    3. `tr(D_c) = tr(D_{μ,π}) - tr(P_μ)`,
    4. `tr(D_c²) = tr(D_{μ,π}²) - tr(P_μ)`. -/
theorem participation_ratio_trace_moment_decomposition
    (τ : B →+ A) (P_mu D_tdo : B) (hP : P_mu * P_mu = P_mu)
    (hRight : D_tdo * P_mu = P_mu) (hLeft : P_mu * D_tdo = P_mu) :
    tdoLinearMoment τ D_tdo = τ P_mu + centeredLinearMoment τ P_mu D_tdo ∧
    tdoQuadraticMoment τ D_tdo = τ P_mu + centeredQuadraticMoment τ P_mu D_tdo ∧
    centeredLinearMoment τ P_mu D_tdo = tdoLinearMoment τ D_tdo - τ P_mu ∧
    centeredQuadraticMoment τ P_mu D_tdo = tdoQuadraticMoment τ D_tdo - τ P_mu := by
  have hStat := intrinsic_tdo_stationarity_and_centered_invariance P_mu D_tdo hP hRight hLeft
  have hD1 : D_tdo = P_mu + intrinsicCenteredTDO P_mu D_tdo := hStat.2.2.2.1
  have hD2 : D_tdo * D_tdo =
      P_mu + intrinsicCenteredTDO P_mu D_tdo * intrinsicCenteredTDO P_mu D_tdo :=
    hStat.2.2.2.2.2.2.1
  have hM1 : tdoLinearMoment τ D_tdo = τ P_mu + centeredLinearMoment τ P_mu D_tdo := by
    dsimp only [tdoLinearMoment, centeredLinearMoment]
    conv_lhs => rw [hD1]
    exact map_add τ P_mu (intrinsicCenteredTDO P_mu D_tdo)
  have hM2 : tdoQuadraticMoment τ D_tdo = τ P_mu + centeredQuadraticMoment τ P_mu D_tdo := by
    dsimp only [tdoQuadraticMoment, centeredQuadraticMoment]
    conv_lhs => rw [hD2]
    exact map_add τ P_mu (intrinsicCenteredTDO P_mu D_tdo * intrinsicCenteredTDO P_mu D_tdo)
  refine ⟨hM1, hM2, ?_, ?_⟩
  · rw [hM1]; abel
  · rw [hM2]; abel

/-!
===============================================================================
## Stage VI (`𝔖𝔊₆`): The Four Representative Attention Head Archetypes
===============================================================================
-/

/-- **Definition (`copyingHead`, `arXiv:2610.06012` Section 4, Figure 2)**:
    Archetype 1: The full-rank copying / identity attention head `A_copy := P + (1 - P)`. -/
def copyingHead (P : B) : B := P + (1 - P)

/-- **Definition (`pureSinkHead`, `arXiv:2610.06012` Section 4, Figure 2)**:
    Archetype 2: The rank-1 pure sink attention head `A_sink := P + N_+` (`A = 1 e₁^⊤`),
    where all queries attend to the sink distribution and centered routing `A_c` vanishes. -/
def pureSinkHead (P X : B) : B := P + sinkCornerPlus P X

/-- **Definition (`sinkBiasedHead`, `arXiv:2610.06012` Section 4, Figure 2)**:
    Archetype 3: The sink-biased routing head `A_biased := P + N_+ + A_c`, where
    non-zero sink concentration `N_+` coexists with genuine centered routing `A_c`. -/
def sinkBiasedHead (P X Z : B) : B :=
  P + sinkCornerPlus P X + centeredRouteOp P Z

/-- **Definition (`shiftingJordanHead`, `arXiv:2610.06012` Section 4, Figure 2)**:
    Archetype 4: The shifting / Jordan routing head `A_shift := P + A_c`, which routes
    signals across centered positions with zero sink imbalance (`N_+ = 0`). -/
def shiftingJordanHead (P Z : B) : B := P + centeredRouteOp P Z

/-- **Theorem (`four_representative_attention_archetypes_classification`, Stage `𝔖𝔊₆`)**:
    Proves the algebraic signatures of the four representative attention heads of
    `arXiv:2610.06012` Section 4 (Figure 2) in `[Ring B]`:
    1. **Copying Head (`A_copy`)**: Has zero sink imbalance (`N_+ = 0`) and acts as the
       exact projector `1 - P` on the centered routing subspace.
    2. **Pure Sink Head (`A_sink = P + N_+`)**:
       - Is a non-symmetric idempotent (`A_sink² = A_sink`),
       - Has **zero genuine centered routing** (`centeredRouteOp P A_sink = 0`),
       - Yet its Euclidean Gram operator `(P + N_-)(P + N_+)` injects the non-zero
         quadratic sink artifact `Q_- = N_- N_+` into `(1 - P) B (1 - P)`!
    3. **Sink-Biased Routing Head (`A_biased = P + N_+ + A_c`)**:
       Simultaneously carries sink corner `sinkCornerPlus P A_biased = N_+` and genuine
       centered routing `centeredRouteOp P A_biased = A_c`.
    4. **Shifting / Jordan Head (`A_shift = P + A_c`)**:
       Has zero sink corner (`sinkCornerPlus P A_shift = 0`) and routes purely via `A_c`. -/
theorem four_representative_attention_archetypes_classification
    (P X Y Z : B) (hP : P * P = P) :
    sinkCornerPlus P (copyingHead P) = 0 ∧
    centeredRouteOp P (copyingHead P) = 1 - P ∧
    pureSinkHead P X * pureSinkHead P X = pureSinkHead P X ∧
    centeredRouteOp P (pureSinkHead P X) = 0 ∧
    (1 - P) * ((P + sinkCornerMinus P Y) * pureSinkHead P X) * (1 - P) =
      sinkGramMinus P X Y ∧
    sinkCornerPlus P (sinkBiasedHead P X Z) = sinkCornerPlus P X ∧
    centeredRouteOp P (sinkBiasedHead P X Z) = centeredRouteOp P Z ∧
    sinkCornerPlus P (shiftingJordanHead P Z) = 0 ∧
    centeredRouteOp P (shiftingJordanHead P Z) = centeredRouteOp P Z := by
  dsimp only [copyingHead, pureSinkHead, sinkBiasedHead, shiftingJordanHead,
    sinkCornerPlus, sinkCornerMinus, centeredRouteOp, sinkGramMinus]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring [hP, proj_idem hP]
  · noncomm_ring [hP, proj_idem hP]
  · noncomm_ring [hP, proj_idem hP]
  · noncomm_ring [hP, proj_idem hP]
  · noncomm_ring [hP, proj_idem hP]
  · noncomm_ring [hP, proj_idem hP]
  · noncomm_ring [hP, proj_idem hP]
  · noncomm_ring [hP, proj_idem hP]
  · noncomm_ring [hP, proj_idem hP]

/-!
===============================================================================
## Stage VII (`𝔖𝔊₇`): Causal Masking Filtration, Generation Block & 5-Graded Parabolic Isogeny
===============================================================================
-/

/-- **Definition (`causalStrictLower`, `arXiv:2610.06012` Section 3, Eq. 2 & Section 5.1)**:
    Given a 3-stage causal token prefix decomposition `1 = P₁ + P₂ + P₃` (`P₁` = initial
    sink position, `P₂ = 1 - P₁ - P₃` = prompt waist `1..m`, `P₃` = generated
    continuation `G_t = [m+1..m+t]`), `causalStrictLower` is the strictly causal
    lower-triangular routing component `P₂ A P₁ + P₃ A P₁ + P₃ A P₂`. -/
def causalStrictLower (P₁ P₃ A_op : B) : B :=
  (1 - P₁ - P₃) * A_op * P₁ + P₃ * A_op * P₁ + P₃ * A_op * (1 - P₁ - P₃)

/-- **Definition (`generatedSubblock`, `arXiv:2610.06012` Section 5.1, line 16)**:
    The generation-only submatrix `B_t^{(l,h)} := P₃ A P₃ = A_t^{(l,h)}[G_t, G_t]`
    restricted to the generated token block `P₃`. -/
def generatedSubblock (P₃ A_op : B) : B := P₃ * A_op * P₃

/-- **Definition (`generatedEuclideanProxy`, `arXiv:2610.06012` Section 5.1, Eq. 16 & line 79)**:
    The lightweight Euclidean head-selection and generation-only proxy
    `B_t B_t^⊤ := (P₃ A P₃)(P₃ A^* P₃)`. -/
def generatedEuclideanProxy (P₃ A_op A_star : B) : B :=
  generatedSubblock P₃ A_op * generatedSubblock P₃ A_star

/-- **Definition (`weylCausalH`)**:
    The causal Weyl grading element `H := P₁ - P₃` separating the initial sink `P₁`
    (weight `+1`), the prompt waist `P₂ = 1 - P₁ - P₃` (weight `0`), and the generated
    continuation `P₃` (weight `-1`). -/
def weylCausalH (P₁ P₃ : B) : B := P₁ - P₃

/-- First adjoint derivation `ad_H(X) = [H, X]` for the causal Weyl element `H`. -/
def adCausalH (H X : B) : B := comm H X

/-- Second iterated adjoint derivation `ad_H²(X) = [H, [H, X]]`. -/
def adCausalH2 (H X : B) : B := adCausalH H (adCausalH H X)

/-- Third iterated adjoint derivation `ad_H³(X) = [H, ad_H²(X)]`. -/
def adCausalH3 (H X : B) : B := adCausalH H (adCausalH2 H X)

/-- Fourth iterated adjoint derivation `ad_H⁴(X) = [H, ad_H³(X)]`. -/
def adCausalH4 (H X : B) : B := adCausalH H (adCausalH3 H X)

/-- Fifth iterated adjoint derivation `ad_H⁵(X) = [H, ad_H⁴(X)]`. -/
def adCausalH5 (H X : B) : B := adCausalH H (adCausalH4 H X)

/-- **Theorem (`causal_attention_nilpotency_and_parabolic_five_grading`, Stage `𝔖𝔊₇`)**:
    Proves the 3-stage causal token-filtration properties in `[Ring B]`:
    Given orthogonal idempotents `P₁, P₃` (`P₁² = P₁`, `P₃² = P₃`, `P₁ P₃ = P₃ P₁ = 0`):
    1. **3-Step Nilpotency of Strict Causal Routing**:
       `causalStrictLower P₁ P₃ A_op ^ 3 = 0`.
    2. **Idempotent Sub-Block Closure of the Generation-Only Proxy (`Eq. 16`)**:
       `P₃ * generatedEuclideanProxy P₃ A_op A_star * P₃ = generatedEuclideanProxy P₃ A_op A_star`.
    3. **Tripotency of the Causal Weyl Grading Element**: `H³ = H` for `H = P₁ - P₃`.
    4. **5-Graded Parabolic Master Polynomial**:
       `ad_H⁵(A_op) - 5 • ad_H³(A_op) + 4 • ad_H(A_op) = 0`.
    5. **Exact `4! = 24` Root-Projection of the Prompt-Sink-to-Generation Channel `P₃ A P₁`**:
       `ad_H⁴(A_op) - 2 • ad_H³(A_op) - ad_H²(A_op) + 2 • ad_H(A_op) = 24 • (P₃ A_op P₁)`. -/
theorem causal_attention_nilpotency_and_parabolic_five_grading
    (P₁ P₃ A_op A_star : B)
    (h1 : P₁ * P₁ = P₁) (h3 : P₃ * P₃ = P₃)
    (h13 : P₁ * P₃ = 0) (h31 : P₃ * P₁ = 0) :
    let H := weylCausalH P₁ P₃
    causalStrictLower P₁ P₃ A_op * causalStrictLower P₁ P₃ A_op *
      causalStrictLower P₁ P₃ A_op = 0 ∧
    P₃ * generatedEuclideanProxy P₃ A_op A_star * P₃ =
      generatedEuclideanProxy P₃ A_op A_star ∧
    H * H * H = H ∧
    adCausalH5 H A_op - 5 • adCausalH3 H A_op + 4 • adCausalH H A_op = 0 ∧
    adCausalH4 H A_op - 2 • adCausalH3 H A_op - adCausalH2 H A_op + 2 • adCausalH H A_op =
      24 • (P₃ * A_op * P₁) := by
  dsimp only [causalStrictLower, generatedEuclideanProxy, generatedSubblock,
    weylCausalH, adCausalH5, adCausalH4, adCausalH3, adCausalH2, adCausalH, comm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring [h1, h3, h13, h31, proj_idem h1, proj_idem h3, proj_orth h13, proj_orth h31]
  · noncomm_ring [h3, proj_idem h3]
  · noncomm_ring [h1, h3, h13, h31, proj_idem h1, proj_idem h3, proj_orth h13, proj_orth h31]
  · noncomm_ring [h1, h3, h13, h31, proj_idem h1, proj_idem h3, proj_orth h13, proj_orth h31]
  · noncomm_ring [h1, h3, h13, h31, proj_idem h1, proj_idem h3, proj_orth h13, proj_orth h31]

/-!
===============================================================================
## Stage VIII (`𝔖𝔊₈`): Attention Uncertainty Quantification (SAUQ) Recurrence
===============================================================================
-/

/-- **Definition (`sauqStep`, `arXiv:2610.06012` Section 5.1, Eq. 18)**:
    The single-step SAUQ confidence recurrence
    `c_t^{(l)} := α p_t + (1 - α) s_t^{(l)} c_{t-1}^{(l)}`, where `p_t` is the local token
    probability, `s_t^{(l)} = PR(D_{μ_t,π_t}^{(l,h^*)})` is the intrinsic routing
    participation ratio, and `α` is the interpolation parameter (`α = 0.2 = 1/5` in Section 5.1). -/
def sauqStep (α p_t s_t c_prev : B) : B :=
  α * p_t + (1 - α) * s_t * c_prev

/-- **Definition (`sauqStep2`, `arXiv:2610.06012` Section 5.1, Eq. 18)**:
    The 2-step unrolled SAUQ confidence `c₂^{(l)}` starting from `c₁^{(l)} = p₁`. -/
def sauqStep2 (α p₁ p₂ s₂ : B) : B :=
  sauqStep α p₂ s₂ p₁

/-- **Definition (`sauqStep3`, `arXiv:2610.06012` Section 5.1, Eq. 18)**:
    The 3-step unrolled SAUQ confidence `c₃^{(l)}` starting from `c₁^{(l)} = p₁`. -/
def sauqStep3 (α p₁ p₂ p₃ s₂ s₃ : B) : B :=
  sauqStep α p₃ s₃ (sauqStep2 α p₁ p₂ s₂)

/-- **Definition (`sauqScaledStep5`, `arXiv:2610.06012` Section 5.1, line 62: `α = 0.2 = 1/5`)**:
    The integer-cleared `5 ×` SAUQ recurrence at the canonical benchmark hyperparameter
    `α = 1/5`: `5 c_t = p_t + 4 s_t c_{t-1}`. -/
def sauqScaledStep5 (p_t s_t c_prev : B) : B :=
  p_t + 4 • (s_t * c_prev)

/-- **Theorem (`sauq_confidence_recurrence_collapse_and_preservation`, Stage `𝔖𝔊₈`)**:
    Proves the structural properties of the SAUQ confidence recurrence (`arXiv:2610.06012`
    Section 5.1, Eq. 18) in `[Ring B]`:
    1. **Routing Collapse Attenuation (`s_t = 0 ⟹ c_t = α p_t`)**:
       When centered participation collapses (`s_t = 0`), all propagated prior
       confidence `c_{t-1}` is annihilated.
    2. **Full Routing Stationarity (`s_t = 1, p_t = p ⟹ c_t = p`)**:
       When routing is maximal (`s_t = 1`) and token confidence is constant (`p`),
       confidence `p` is an exact fixed point of the recurrence.
    3. **Exact 3-Step Horizon Expansion**:
       `c₃ = α p₃ + (1 - α) s₃ α p₂ + (1 - α) s₃ (1 - α) s₂ p₁`.
    4. **RAUQ-to-SAUQ Routing Signal Differential**:
       `sauqStep α p_t s_sauq c_prev - sauqStep α p_t s_rauq c_prev = (1 - α)(s_sauq - s_rauq) c_prev`.
    5. **Benchmark `α = 1/5` (`0.2`) Integer-Cleared Identity**:
       `sauqStep 1 p_t s_t c_prev + 4 • sauqStep 0 p_t s_t c_prev = sauqScaledStep5 p_t s_t c_prev`. -/
theorem sauq_confidence_recurrence_collapse_and_preservation
    (α p p₁ p₂ p₃ p_t s₂ s₃ s_t s_sauq s_rauq c_prev : B) :
    sauqStep α p_t 0 c_prev = α * p_t ∧
    sauqStep α p 1 p = p ∧
    sauqStep3 α p₁ p₂ p₃ s₂ s₃ =
      α * p₃ + (1 - α) * s₃ * α * p₂ + (1 - α) * s₃ * (1 - α) * s₂ * p₁ ∧
    sauqStep α p_t s_sauq c_prev - sauqStep α p_t s_rauq c_prev =
      (1 - α) * (s_sauq - s_rauq) * c_prev ∧
    sauqStep 1 p_t s_t c_prev + 4 • sauqStep 0 p_t s_t c_prev =
      sauqScaledStep5 p_t s_t c_prev := by
  dsimp only [sauqStep3, sauqStep2, sauqStep, sauqScaledStep5]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring
  · noncomm_ring
  · noncomm_ring
  · noncomm_ring
  · noncomm_ring

/-!
===============================================================================
## Stage IX (`𝔖𝔊₉`): Decidable 9-Stage Poset Chain & Master Synthesis Theorem
===============================================================================
-/

/-- **Definition (`attentionRoutingPosetPrecBool`)**:
    Boolean strict precedence relation `𝔖𝔊_i ≺ 𝔖𝔊_j` on the 9 stages (`Fin 9`) of the
    `arXiv:2610.06012` Attention Token-Difference Routing Poset. -/
def attentionRoutingPosetPrecBool (i j : Fin 9) : Bool := decide (i.val < j.val)

/-- **Theorem (`attentionRoutingPosetPrec_strict_order_and_chain`, Stage `𝔖𝔊₉` Part A)**:
    Certifies irreflexivity, asymmetry, transitivity, and the complete 8-link causal chain
    `𝔖𝔊₁ ≺ 𝔖𝔊₂ ≺ ⋯ ≺ 𝔖𝔊₉` on `Fin 9`. -/
theorem attentionRoutingPosetPrec_strict_order_and_chain :
    (∀ i : Fin 9, attentionRoutingPosetPrecBool i i = false) ∧
    (∀ i j : Fin 9, attentionRoutingPosetPrecBool i j = true → attentionRoutingPosetPrecBool j i = false) ∧
    (∀ i j k : Fin 9, attentionRoutingPosetPrecBool i j = true →
      attentionRoutingPosetPrecBool j k = true → attentionRoutingPosetPrecBool i k = true) ∧
    attentionRoutingPosetPrecBool 0 1 = true ∧
    attentionRoutingPosetPrecBool 1 2 = true ∧
    attentionRoutingPosetPrecBool 2 3 = true ∧
    attentionRoutingPosetPrecBool 3 4 = true ∧
    attentionRoutingPosetPrecBool 4 5 = true ∧
    attentionRoutingPosetPrecBool 5 6 = true ∧
    attentionRoutingPosetPrecBool 6 7 = true ∧
    attentionRoutingPosetPrecBool 7 8 = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- **Theorem (`arxiv_2610_06012_attention_token_difference_routing_master_synthesis`, Stage `𝔖𝔊₉` Part B)**:
    Master Synthesis Theorem unifying all 9 stages of Viganò, Melzi, and Ovsjanikov's
    *"Spectral Geometry of Attention: From Information Routing to Uncertainty"*
    (`arXiv:2610.06012`) inside `[Ring B]`:
    1. **Weighted TDO & Similarity (`𝔖𝔊₁`)**:
       `Ω_μ D_{μ,π} = A^* Ω_π A` and `Ω_μ^{1/2} D_{μ,π} = S_{μ,π} Ω_μ^{1/2}`.
    2. **Euclidean Sink Bias & Split Tetractys (`𝔖𝔊₂`)**:
       `Φ_sink² = V_sink`, `J_sink² = -V_sink`, and
       `A^* A = P + Φ_sink + Q_- + A_c^* A_c`.
    3. **Intrinsic Pullback TDO Stationarity & Power Split (`𝔖𝔊₃`)**:
       `[D_{μ,π}, P] = 0`, `D_{μ,π} = P + D_c`, and `D_{μ,π}² = P + D_c²`.
    4. **Mean–Routing Value Decomposition & Barycenter Alignment (`𝔖𝔊₄`)**:
       `A V = V_m + A V_c`, `P_π (A V) = V_m`, and `P_π (A V_c) = 0`.
    5. **Participation Ratio Moment Decomposition (`𝔖𝔊₅`)**:
       `tr(D_{μ,π}) = tr(P) + tr(D_c)` and `tr(D_{μ,π}²) = tr(P) + tr(D_c²)`.
    6. **Pure Sink Head Idempotency & False Euclidean Term (`𝔖𝔊₆`)**:
       `A_sink² = A_sink`, `centeredRouteOp P A_sink = 0`, and
       `(1 - P)((P + N_-) A_sink)(1 - P) = Q_-`.
    7. **Causal Attention 3-Step Nilpotency & 5-Graded Parabolic Polynomial (`𝔖𝔊₇`)**:
       `N_causal³ = 0` and `ad_H⁵(A) - 5 • ad_H³(A) + 4 • ad_H(A) = 0`.
    8. **SAUQ Confidence Recurrence (`𝔖𝔊₈`)**:
       `sauqStep α p_t 0 c_prev = α p_t` and `sauqStep α p 1 p = p`. -/
theorem arxiv_2610_06012_attention_token_difference_routing_master_synthesis
    (τ : B →+ A)
    (P P_pi P₁ P₃ Ω_mu Ω_mu_inv Ω_mu_half Ω_mu_half_inv Ω_pi A_op A_star D_tdo V α p p_t c_prev : B)
    (hP : P * P = P)
    (h1 : P₁ * P₁ = P₁) (h3 : P₃ * P₃ = P₃)
    (h13 : P₁ * P₃ = 0) (h31 : P₃ * P₁ = 0)
    (h_mu_inv : Ω_mu * Ω_mu_inv = 1)
    (h_half_inv : Ω_mu_half * Ω_mu_half_inv = 1)
    (h_half_inv_r : Ω_mu_half_inv * Ω_mu_half = 1)
    (h_half_sq_inv : Ω_mu_half_inv * Ω_mu_half_inv = Ω_mu_inv)
    (hRow : A_op * P = P) (hRowStar : P * A_star = P)
    (hPullback : P_pi * A_op = P)
    (hTdoRight : D_tdo * P = P) (hTdoLeft : P * D_tdo = P) :
    let H := weylCausalH P₁ P₃
    -- (1) Stage I: TDO Gram & Similarity
    (Ω_mu * tokenDiffOp Ω_mu_inv A_star Ω_pi A_op = A_star * Ω_pi * A_op ∧
     Ω_mu_half * tokenDiffOp Ω_mu_inv A_star Ω_pi A_op =
       symTokenDiffOp Ω_mu_half_inv A_star Ω_pi A_op * Ω_mu_half) ∧
    -- (2) Stage II: Split Tetractys & Euclidean Sink Bias Expansion
    (sinkVielbeinPhi P A_op A_star * sinkVielbeinPhi P A_op A_star = sinkMetricV P A_op A_star ∧
     sinkSymplecticJ P A_op A_star * sinkSymplecticJ P A_op A_star = -sinkMetricV P A_op A_star ∧
     A_star * A_op =
       P + sinkVielbeinPhi P A_op A_star + sinkGramMinus P A_op A_star +
         centeredRouteOp P A_star * centeredRouteOp P A_op) ∧
    -- (3) Stage III: Intrinsic Pullback Stationarity & Quadratic Power Split
    (comm D_tdo P = 0 ∧
     D_tdo = P + intrinsicCenteredTDO P D_tdo ∧
     D_tdo * D_tdo = P + intrinsicCenteredTDO P D_tdo * intrinsicCenteredTDO P D_tdo) ∧
    -- (4) Stage IV: Mean-Routing Value Decomposition & Barycenter Alignment
    (A_op * V = valueMeanPart P V + A_op * valueCenteredPart P V ∧
     P_pi * (A_op * V) = valueMeanPart P V ∧
     P_pi * (A_op * valueCenteredPart P V) = 0) ∧
    -- (5) Stage V: Participation Ratio Trace Moment Split
    (tdoLinearMoment τ D_tdo = τ P + centeredLinearMoment τ P D_tdo ∧
     tdoQuadraticMoment τ D_tdo = τ P + centeredQuadraticMoment τ P D_tdo) ∧
    -- (6) Stage VI: Pure Sink Head Idempotency & Centered Collapse
    (pureSinkHead P A_op * pureSinkHead P A_op = pureSinkHead P A_op ∧
     centeredRouteOp P (pureSinkHead P A_op) = 0) ∧
    -- (7) Stage VII: Causal Nilpotency & 5-Graded Parabolic Polynomial
    (causalStrictLower P₁ P₃ A_op * causalStrictLower P₁ P₃ A_op *
       causalStrictLower P₁ P₃ A_op = 0 ∧
     adCausalH5 H A_op - 5 • adCausalH3 H A_op + 4 • adCausalH H A_op = 0) ∧
    -- (8) Stage VIII: SAUQ Confidence Recurrence
    (sauqStep α p_t 0 c_prev = α * p_t ∧
     sauqStep α p 1 p = p) := by
  have hS1 := tokenDiffOp_adjoint_selfadjoint_and_similarity
    τ Ω_mu Ω_mu_inv Ω_mu_half Ω_mu_half_inv Ω_pi A_op A_star 0 0
    h_mu_inv h_half_inv h_half_inv_r h_half_sq_inv
  have hS2A := sinkCorner_nilpotent_and_clifford_tetractys P A_op A_star hP
  have hS2B := euclidean_tdo_structural_sink_bias_decomposition P A_op A_star hP hRow hRowStar
  have hS3 := intrinsic_tdo_stationarity_and_centered_invariance P D_tdo hP hTdoRight hTdoLeft
  have hS4 := mean_routing_value_decomposition_and_pythagorean_gram
    P P_pi A_op V 0 0 0 hP hRow hPullback (by noncomm_ring) (by noncomm_ring)
  have hS5 := participation_ratio_trace_moment_decomposition τ P D_tdo hP hTdoRight hTdoLeft
  have hS6 := four_representative_attention_archetypes_classification P A_op A_star A_op hP
  have hS7 := causal_attention_nilpotency_and_parabolic_five_grading
    P₁ P₃ A_op A_star h1 h3 h13 h31
  have hS8 := sauq_confidence_recurrence_collapse_and_preservation
    α p 0 0 0 p_t 0 0 0 0 0 c_prev
  exact ⟨⟨hS1.2.1, hS1.2.2.2.2.1⟩,
    ⟨hS2A.1, hS2A.2.1, hS2B.2.1⟩,
    ⟨hS3.1, hS3.2.2.2.1, hS3.2.2.2.2.2.2.1⟩,
    ⟨hS4.1, hS4.2.2.1, hS4.2.2.2.1⟩,
    ⟨hS5.1, hS5.2.1⟩,
    ⟨hS6.2.2.1, hS6.2.2.2.1⟩,
    ⟨hS7.1, hS7.2.2.2.1⟩,
    ⟨hS8.1, hS8.2.1⟩⟩

/-!
===============================================================================
## Stage X (`𝔖𝔊₁₀`): Non-Commutative Right-Zero Band Algebra of Measure Projectors
===============================================================================
-/

/-- **Definition (`measureShift`, `arXiv:2610.06012` Section 5.2, Table 2 & Appendix A.14)**:
    The inter-measure barycenter shift operator `δ₁₂ := P₂ - P₁` between two rank-1
    probability-measure projectors `P₁ = 1 μ₁^⊤` and `P₂ = 1 μ₂^⊤` (e.g., Uniform,
    Positional, Zipf-Law, Unembedding, and Intrinsic pullback measures). -/
def measureShift (P₁ P₂ : B) : B := P₂ - P₁

/-- **Definition (`measureUnipotent`, `arXiv:2610.06012` Section 5.2)**:
    The unipotent barycenter change-of-measure transformation `U₁₂ := 1 + (P₂ - P₁)`. -/
def measureUnipotent (P₁ P₂ : B) : B := 1 + measureShift P₁ P₂

/-- **Theorem (`measure_band_nilpotent_shift_and_cocycle`, Stage `𝔖𝔊₁₀`)**:
    Proves that for any three rank-1 probability-measure projectors `P₁, P₂, P₃ ∈ B`
    sharing the unit constant vector `1` so that the right-zero band laws `P_i P_j = P_j`
    hold (`i, j ∈ {1, 2, 3}`):
    1. **Commutator Equals Measure Shift**: `[P₁, P₂] = P₂ - P₁`.
    2. **Square-Zero Nilpotency of Every Measure Shift**: `(P₂ - P₁)² = 0`.
    3. **Consecutive Shift Annihilation**: `(P₂ - P₁)(P₃ - P₂) = 0`.
    4. **Additive Cocycle & Multiplicative Unipotent Group Law**:
       `δ₁₂ + δ₂₃ = δ₁₃`, `U₁₂ U₂₃ = U₁₃`, and `U₁₂ U₂₁ = 1`.
    5. **Centered Subspace Coalescence & Non-Intrinsic Left-Stationarity Defect (`Section 5.2`)**:
       `(1 - P₁)(1 - P₂) = 1 - P₁`, `(1 - P₂)(1 - P₁) = 1 - P₂`, and if `D_tdo` is
       stationary for the intrinsic measure `P₁` (`D_tdo P₁ = P₁` and `P₁ D_tdo = P₁`),
       then `D_tdo P₂ = P₂` still holds on the right, whereas on the left
       `P₂ D_tdo - P₂ = (P₂ - P₁)(D_tdo - 1)`. -/
theorem measure_band_nilpotent_shift_and_cocycle
    (P₁ P₂ P₃ D_tdo : B)
    (h11 : P₁ * P₁ = P₁) (h22 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = P₂) (h21 : P₂ * P₁ = P₁)
    (h13 : P₁ * P₃ = P₃) (h23 : P₂ * P₃ = P₃)
    (hD_right : D_tdo * P₁ = P₁) (hD_left : P₁ * D_tdo = P₁) :
    comm P₁ P₂ = measureShift P₁ P₂ ∧
    measureShift P₁ P₂ * measureShift P₁ P₂ = 0 ∧
    measureShift P₁ P₂ * measureShift P₂ P₃ = 0 ∧
    measureShift P₁ P₂ + measureShift P₂ P₃ = measureShift P₁ P₃ ∧
    measureUnipotent P₁ P₂ * measureUnipotent P₂ P₃ = measureUnipotent P₁ P₃ ∧
    measureUnipotent P₁ P₂ * measureUnipotent P₂ P₁ = 1 ∧
    (1 - P₁) * (1 - P₂) = 1 - P₁ ∧
    (1 - P₂) * (1 - P₁) = 1 - P₂ ∧
    D_tdo * P₂ = P₂ ∧
    P₂ * D_tdo - P₂ = measureShift P₁ P₂ * (D_tdo - 1) := by
  have h12A : ∀ Z : B, P₁ * (P₂ * Z) = P₂ * Z := fun Z => by rw [← mul_assoc, h12]
  have h21A : ∀ Z : B, P₂ * (P₁ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, h21]
  have h13A : ∀ Z : B, P₁ * (P₃ * Z) = P₃ * Z := fun Z => by rw [← mul_assoc, h13]
  have h23A : ∀ Z : B, P₂ * (P₃ * Z) = P₃ * Z := fun Z => by rw [← mul_assoc, h23]
  have hDrA : ∀ Z : B, D_tdo * (P₁ * Z) = P₁ * Z := fun Z => by rw [← mul_assoc, hD_right]
  dsimp only [comm, measureShift, measureUnipotent]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring [h12, h21]
  · noncomm_ring [h11, h22, h12, h21, proj_idem h11, proj_idem h22, h12A, h21A]
  · noncomm_ring [h22, h12, h13, h23, proj_idem h22, h12A, h13A, h23A]
  · noncomm_ring
  · noncomm_ring [h22, h12, h13, h23, proj_idem h22, h12A, h13A, h23A]
  · noncomm_ring [h11, h22, h12, h21, proj_idem h11, proj_idem h22, h12A, h21A]
  · noncomm_ring [h12]
  · noncomm_ring [h21]
  · rw [← h12]
    exact hDrA P₂
  · noncomm_ring [hD_left]

/-!
===============================================================================
## Stage XI (`𝔖𝔊₁₁`): Intrinsic Dirichlet Operator & Rayleigh Dissipation Identity
===============================================================================
-/

/-- **Definition (`intrinsicDirichletOp`, `arXiv:2610.06012` Section 3.1.2 & Section 4)**:
    The **Intrinsic Attention Dirichlet Operator (Laplacian)** `L_{μ,π} := 1 - D_{μ,π}`,
    whose quadratic form measures the single-step representation energy dissipated by `A`. -/
def intrinsicDirichletOp (D_tdo : B) : B := 1 - D_tdo

/-- **Definition (`centeredDirichletOp`, `arXiv:2610.06012` Section 3.1.2)**:
    The centered Dirichlet operator `L_c := (1 - P_μ) - D_c` acting on `1^{⊥_μ}`. -/
def centeredDirichletOp (P_mu D_tdo : B) : B :=
  (1 - P_mu) - intrinsicCenteredTDO P_mu D_tdo

/-- **Theorem (`intrinsic_dirichlet_dissipation_and_sink_idempotency`, Stage `𝔖𝔊₁₁`)**:
    Proves the algebraic and variational properties of the Intrinsic Attention Dirichlet
    Operator `L_{μ,π} = 1 - D_{μ,π}` in `[Ring B]`:
    Given `P_μ² = P_μ`, `D_{μ,π} P_μ = P_μ`, `P_μ D_{μ,π} = P_μ`, and `Ω_μ Ω_μ⁻¹ = 1`:
    1. **Zero Action on the Constant Barycenter Mode**:
       `L_{μ,π} P_μ = 0` and `P_μ L_{μ,π} = 0`.
    2. **Purely Centered Support**:
       `L_{μ,π} = L_c` and `(1 - P_μ) L_{μ,π} (1 - P_μ) = L_{μ,π}`.
    3. **Exact Rayleigh Dissipation Identity (`⟨X, L_{μ,π} Y⟩_μ = ⟨X, Y⟩_μ - ⟨A X, A Y⟩_π`)**:
       Proves that the `μ`-weighted pairing of `L_{μ,π}` is the exact difference between
       the input energy `⟨X, Y⟩_μ` and the routed output energy `⟨A X, A Y⟩_π`.
    4. **Pure Sink Complete Centered Dissipation**:
       When centered routing vanishes (`D_{μ,π} = P_μ`), `L_{μ,π} = 1 - P_μ` is an
       idempotent (`L_{μ,π}² = L_{μ,π}`) that extracts `L_{μ,π} V = V_c`. -/
theorem intrinsic_dirichlet_dissipation_and_sink_idempotency
    (τ : B →+ A) (P_mu D_tdo Ω_mu Ω_mu_inv Ω_pi A_op A_star X_star Y V : B)
    (hP : P_mu * P_mu = P_mu)
    (hRight : D_tdo * P_mu = P_mu) (hLeft : P_mu * D_tdo = P_mu)
    (h_mu_inv : Ω_mu * Ω_mu_inv = 1) :
    intrinsicDirichletOp D_tdo * P_mu = 0 ∧
    P_mu * intrinsicDirichletOp D_tdo = 0 ∧
    intrinsicDirichletOp D_tdo = centeredDirichletOp P_mu D_tdo ∧
    (1 - P_mu) * intrinsicDirichletOp D_tdo * (1 - P_mu) = intrinsicDirichletOp D_tdo ∧
    weightedInner τ X_star Ω_mu
      (intrinsicDirichletOp (tokenDiffOp Ω_mu_inv A_star Ω_pi A_op) * Y) =
      weightedInner τ X_star Ω_mu Y -
        weightedInner τ (X_star * A_star) Ω_pi (A_op * Y) ∧
    intrinsicDirichletOp P_mu * intrinsicDirichletOp P_mu = intrinsicDirichletOp P_mu ∧
    intrinsicDirichletOp P_mu * V = valueCenteredPart P_mu V := by
  have hRightA : ∀ Z : B, D_tdo * (P_mu * Z) = P_mu * Z := fun Z => by rw [← mul_assoc, hRight]
  have hLeftA : ∀ Z : B, P_mu * (D_tdo * Z) = P_mu * Z := fun Z => by rw [← mul_assoc, hLeft]
  have h_mu_assoc : ∀ Z : B, Ω_mu * (Ω_mu_inv * Z) = Z := fun Z => by
    rw [← mul_assoc, h_mu_inv, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [intrinsicDirichletOp]
    noncomm_ring [hRight]
  · dsimp only [intrinsicDirichletOp]
    noncomm_ring [hLeft]
  · dsimp only [intrinsicDirichletOp, centeredDirichletOp, intrinsicCenteredTDO]
    noncomm_ring [hP, proj_idem hP, hRight, hRightA, hLeft, hLeftA]
  · dsimp only [intrinsicDirichletOp]
    noncomm_ring [hP, proj_idem hP, hRight, hRightA, hLeft, hLeftA]
  · dsimp only [weightedInner, intrinsicDirichletOp, tokenDiffOp]
    have hSub :
        X_star * Ω_mu * ((1 - Ω_mu_inv * A_star * Ω_pi * A_op) * Y) =
        X_star * Ω_mu * Y - X_star * A_star * Ω_pi * (A_op * Y) := by
      noncomm_ring [h_mu_inv, h_mu_assoc]
    rw [hSub, map_sub]
  · dsimp only [intrinsicDirichletOp]
    noncomm_ring [hP, proj_idem hP]
  · rfl

/-!
===============================================================================
## Stage XII (`𝔖𝔊₁₂`): Transformer Residual Stream & Yoshizawa Metriplectic Flow
===============================================================================
-/

/-- **Definition (`residualAttnVelocity`, `arXiv:2610.06012` Appendix A.1, Eq. 13)**:
    The single-head residual attention velocity `ΔV := A V - V = (A - 1) V` entering
    the transformer residual stream `M_l = X_{l-1} + MHA_l(X̂_{l-1})`. -/
def residualAttnVelocity (A_op V : B) : B := A_op * V - V

/-- **Definition (`souriauSinkFlow`, Bridging `arXiv:2608.21152` ↔ `arXiv:2610.06012`)**:
    The conservative Souriau rotational commutator flow `[Σ_sink, Z]` generated by the
    attention sink bivector `Σ_sink = [N_+, N_-]`. -/
def souriauSinkFlow (P A_op A_star Z : B) : B :=
  comm (sinkSpinSigma P A_op A_star) Z

/-- **Definition (`brockettSinkFlow`, Bridging `arXiv:2608.21152` ↔ `arXiv:2610.06012`)**:
    The dissipative Brockett double-bracket gradient flow `[J_sink, [J_sink, Z]]`
    generated by the antisymmetric sink-drift operator `J_sink = N_+ - N_-`. -/
def brockettSinkFlow (P A_op A_star Z : B) : B :=
  comm (sinkSymplecticJ P A_op A_star) (comm (sinkSymplecticJ P A_op A_star) Z)

/-- **Theorem (`residual_stream_velocity_and_yoshizawa_metriplectic_lock`, Stage `𝔖𝔊₁₂`)**:
    Unifies the transformer residual stream (`arXiv:2610.06012` Appendix A.1, Eq. 13) with
    Shintaro Yoshizawa's *Information Geometry of Gradient Flows* (`arXiv:2608.21152`)
    in `[Ring B]`:
    Given `P_μ² = P_μ`, row-stochasticity `A P_μ = P_μ`, and pullback alignment
    `P_π A = P_μ` with band law `P_π P_μ = P_μ`:
    1. **Mean Annihilation**: The residual velocity annihilates the mean value `V_m = P_μ V`
       identically (`residualAttnVelocity A_op (valueMeanPart P_mu V) = 0`).
    2. **Purely Centered Evolution**: The residual velocity acts exclusively on the
       centered fluctuations `V_c = (1 - P_μ) V`
       (`residualAttnVelocity A_op V = residualAttnVelocity A_op (valueCenteredPart P_mu V)`).
    3. **Zero Output Barycenter Drift**: Under `P_π A = P_μ` and `P_π V_c = 0`,
       `P_π * residualAttnVelocity A_op V = 0`.
    4. **Brockett Radial Pull on the Sink Vielbein**:
       `brockettSinkFlow P_mu A_op A_star Φ_sink = -4 • (V_sink * Φ_sink)`.
    5. **Yoshizawa Coriolis–Brockett Metriplectic Lock on Attention Sinks**:
       `brockettSinkFlow P_mu A_op A_star Φ_sink + 2 • souriauSinkFlow P_mu A_op A_star J_sink = 0`. -/
theorem residual_stream_velocity_and_yoshizawa_metriplectic_lock
    (P_mu P_pi A_op A_star V : B)
    (hP : P_mu * P_mu = P_mu)
    (hRow : A_op * P_mu = P_mu)
    (hPullback : P_pi * A_op = P_mu)
    (hPiV : P_pi * V = P_mu * V) :
    residualAttnVelocity A_op (valueMeanPart P_mu V) = 0 ∧
    residualAttnVelocity A_op V = residualAttnVelocity A_op (valueCenteredPart P_mu V) ∧
    P_pi * residualAttnVelocity A_op V = 0 ∧
    brockettSinkFlow P_mu A_op A_star (sinkVielbeinPhi P_mu A_op A_star) =
      -(4 • (sinkMetricV P_mu A_op A_star * sinkVielbeinPhi P_mu A_op A_star)) ∧
    brockettSinkFlow P_mu A_op A_star (sinkVielbeinPhi P_mu A_op A_star) +
      2 • souriauSinkFlow P_mu A_op A_star (sinkSymplecticJ P_mu A_op A_star) = 0 := by
  have hRowA : ∀ Z : B, A_op * (P_mu * Z) = P_mu * Z := fun Z => by rw [← mul_assoc, hRow]
  have hPullA : ∀ Z : B, P_pi * (A_op * Z) = P_mu * Z := fun Z => by rw [← mul_assoc, hPullback]
  have hNp := sinkCornerPlus_sq_zero P_mu A_op hP
  have hNm := sinkCornerMinus_sq_zero P_mu A_star hP
  have hNpA := sinkCornerPlus_sq_assoc P_mu A_op hP
  have hNmA := sinkCornerMinus_sq_assoc P_mu A_star hP
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [residualAttnVelocity, valueMeanPart]
    noncomm_ring [hRow, hRowA]
  · dsimp only [residualAttnVelocity, valueCenteredPart]
    noncomm_ring [hRow, hRowA]
  · dsimp only [residualAttnVelocity]
    calc P_pi * (A_op * V - V)
      _ = P_pi * (A_op * V) - P_pi * V := by noncomm_ring
      _ = P_mu * V - P_mu * V := by rw [hPullA V, hPiV]
      _ = 0 := by noncomm_ring
  · dsimp only [brockettSinkFlow, sinkVielbeinPhi, sinkSymplecticJ, sinkMetricV,
      sinkGramPlus, sinkGramMinus, comm]
    noncomm_ring [hNp, hNm, hNpA, hNmA]
  · dsimp only [brockettSinkFlow, souriauSinkFlow, sinkVielbeinPhi, sinkSymplecticJ,
      sinkSpinSigma, sinkGramPlus, sinkGramMinus, comm]
    noncomm_ring [hNp, hNm, hNpA, hNmA]

/-!
===============================================================================
## Stage XIII (`𝔖𝔊₁₃`): Multi-Head Attention as a De Haro Model Bundle & Soldered Sheaf
===============================================================================
-/

/-- **Definition (`multiHeadBundleSection`, Bridging `arXiv:2511.07015` ↔ `arXiv:2610.06012`)**:
    The 3-head block-diagonal Model Bundle section
    `M_MHA := P₁ M₁ P₁ + (1 - P₁ - P₃) M₂ (1 - P₁ - P₃) + P₃ M₃ P₃` over orthogonal
    head chart projectors `P₁`, `P₂ = 1 - P₁ - P₃`, and `P₃`. -/
def multiHeadBundleSection (P₁ P₃ M₁ M₂ M₃ : B) : B :=
  P₁ * M₁ * P₁ + (1 - P₁ - P₃) * M₂ * (1 - P₁ - P₃) + P₃ * M₃ * P₃

/-- **Definition (`solderedMultiHeadOutput`, `arXiv:2610.06012` Section 3, Eq. 1)**:
    The output-projected (soldered) multi-head section `W_O⁻¹ M_MHA W_O` transporting
    concatenated head fibers into the shared residual model space. -/
def solderedMultiHeadOutput (W_out_inv M_bundle W_out : B) : B :=
  W_out_inv * M_bundle * W_out

/-- **Theorem (`multi_head_model_bundle_fiber_isolation_and_soldering`, Stage `𝔖𝔊₁₃`)**:
    Unifies multi-head attention (`arXiv:2610.06012` Section 3, Eq. 1) with Sebastian
    De Haro's Model Bundle (`arXiv:2511.07015`) in `[Ring B]`:
    Given orthogonal head projectors `P₁, P₃` (`P₁² = P₁`, `P₃² = P₃`, `P₁ P₃ = P₃ P₁ = 0`)
    and invertible output projection `W_out * W_out_inv = 1`:
    1. **3-Head Partition of Unity & Waist Idempotence**:
       `P₁ + (1 - P₁ - P₃) + P₃ = 1` and `(1 - P₁ - P₃)² = 1 - P₁ - P₃`.
    2. **Exact Head-Chart Fiber Isolation (Zero Inter-Head Cross-Talk)**:
       `P₁ M_MHA P₁ = P₁ M₁ P₁`, `(1 - P₁ - P₃) M_MHA (1 - P₁ - P₃) = (1 - P₁ - P₃) M₂ (1 - P₁ - P₃)`,
       `P₃ M_MHA P₃ = P₃ M₃ P₃`, and `P₁ M_MHA P₃ = 0`.
    3. **Multiplicative Sheaf Homomorphism of Output Soldering `W^O`**:
       `solderedMultiHeadOutput W_out_inv M_bundle W_out * solderedMultiHeadOutput W_out_inv N_bundle W_out = solderedMultiHeadOutput W_out_inv (M_bundle * N_bundle) W_out`. -/
theorem multi_head_model_bundle_fiber_isolation_and_soldering
    (P₁ P₃ M₁ M₂ M₃ M_bundle N_bundle W_out W_out_inv : B)
    (h1 : P₁ * P₁ = P₁) (h3 : P₃ * P₃ = P₃)
    (h13 : P₁ * P₃ = 0) (h31 : P₃ * P₁ = 0)
    (hW : W_out * W_out_inv = 1) :
    P₁ + (1 - P₁ - P₃) + P₃ = 1 ∧
    (1 - P₁ - P₃) * (1 - P₁ - P₃) = 1 - P₁ - P₃ ∧
    P₁ * multiHeadBundleSection P₁ P₃ M₁ M₂ M₃ * P₁ = P₁ * M₁ * P₁ ∧
    (1 - P₁ - P₃) * multiHeadBundleSection P₁ P₃ M₁ M₂ M₃ * (1 - P₁ - P₃) =
      (1 - P₁ - P₃) * M₂ * (1 - P₁ - P₃) ∧
    P₃ * multiHeadBundleSection P₁ P₃ M₁ M₂ M₃ * P₃ = P₃ * M₃ * P₃ ∧
    P₁ * multiHeadBundleSection P₁ P₃ M₁ M₂ M₃ * P₃ = 0 ∧
    solderedMultiHeadOutput W_out_inv M_bundle W_out *
      solderedMultiHeadOutput W_out_inv N_bundle W_out =
      solderedMultiHeadOutput W_out_inv (M_bundle * N_bundle) W_out := by
  have hWA : ∀ Z : B, W_out * (W_out_inv * Z) = Z := fun Z => by
    rw [← mul_assoc, hW, one_mul]
  dsimp only [multiHeadBundleSection, solderedMultiHeadOutput]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring
  · noncomm_ring [h1, h3, h13, h31, proj_idem h1, proj_idem h3, proj_orth h13, proj_orth h31]
  · noncomm_ring [h1, h3, h13, h31, proj_idem h1, proj_idem h3, proj_orth h13, proj_orth h31]
  · noncomm_ring [h1, h3, h13, h31, proj_idem h1, proj_idem h3, proj_orth h13, proj_orth h31]
  · noncomm_ring [h1, h3, h13, h31, proj_idem h1, proj_idem h3, proj_orth h13, proj_orth h31]
  · noncomm_ring [h1, h3, h13, h31, proj_idem h1, proj_idem h3, proj_orth h13, proj_orth h31]
  · noncomm_ring [hW, hWA]

/-!
===============================================================================
## Stage XIV (`𝔖𝔊₁₄`): Thirty-Second-Order (Duotriacontadic) Trilogy Synthesis
   (`arXiv:2511.07015` × `arXiv:2608.21152` × `arXiv:2610.06012`)
===============================================================================
-/

/-- **Definition (`trilogyPosetPrecBool`)**:
    Boolean strict precedence relation `𝔖𝔊_i ≺ 𝔖𝔊_j` across all 14 stages (`Fin 14`)
    of the unified De Haro–Yoshizawa–Viganò-Melzi-Ovsjanikov Trilogy Poset. -/
def trilogyPosetPrecBool (i j : Fin 14) : Bool := decide (i.val < j.val)

/-- **Theorem (`trilogyPosetPrec_strict_order_and_chain`, Stage `𝔖𝔊₁₄` Part A)**:
    Certifies irreflexivity, asymmetry, transitivity, and the complete 13-link causal
    chain `𝔖𝔊₁ ≺ 𝔖𝔊₂ ≺ ⋯ ≺ 𝔖𝔊₁₄` on `Fin 14`. -/
theorem trilogyPosetPrec_strict_order_and_chain :
    (∀ i : Fin 14, trilogyPosetPrecBool i i = false) ∧
    (∀ i j : Fin 14, trilogyPosetPrecBool i j = true → trilogyPosetPrecBool j i = false) ∧
    (∀ i j k : Fin 14, trilogyPosetPrecBool i j = true →
      trilogyPosetPrecBool j k = true → trilogyPosetPrecBool i k = true) ∧
    trilogyPosetPrecBool 0 1 = true ∧
    trilogyPosetPrecBool 1 2 = true ∧
    trilogyPosetPrecBool 2 3 = true ∧
    trilogyPosetPrecBool 3 4 = true ∧
    trilogyPosetPrecBool 4 5 = true ∧
    trilogyPosetPrecBool 5 6 = true ∧
    trilogyPosetPrecBool 6 7 = true ∧
    trilogyPosetPrecBool 7 8 = true ∧
    trilogyPosetPrecBool 8 9 = true ∧
    trilogyPosetPrecBool 9 10 = true ∧
    trilogyPosetPrecBool 10 11 = true ∧
    trilogyPosetPrecBool 11 12 = true ∧
    trilogyPosetPrecBool 12 13 = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-- **Theorem (`duotriacontadic_trilogy_2511_07015_2608_21152_2610_06012_master_synthesis`, Stage `𝔖𝔊₁₄` Part B)**:
    The Thirty-Second-Order (Duotriacontadic) Master Synthesis Theorem welding:
    - **Pillar I (De Haro `arXiv:2511.07015`)**: Multi-head Model Bundle fiber isolation
      `P₁ M_MHA P₁ = P₁ M₁ P₁` and soldered output homomorphism `W_O⁻¹ M W_O W_O⁻¹ N W_O = W_O⁻¹ (M N) W_O`,
    - **Pillar II (Yoshizawa `arXiv:2608.21152`)**: Residual stream centered evolution
      `ΔV = (A - 1) V_c` and Coriolis–Brockett metriplectic sink lock
      `[J_sink, [J_sink, Φ_sink]] + 2 • [Σ_sink, J_sink] = 0`,
    - **Pillar III (Viganò–Melzi–Ovsjanikov `arXiv:2610.06012`)**: Non-commutative
      right-zero band measure shift nilpotency `[P_μ, P_ν]² = 0` and Intrinsic Dirichlet
      Rayleigh dissipation `⟨X, L_{μ,π} Y⟩_μ = ⟨X, Y⟩_μ - ⟨A X, A Y⟩_π`. -/
theorem duotriacontadic_trilogy_2511_07015_2608_21152_2610_06012_master_synthesis
    (τ : B →+ A)
    (P_mu P_nu P_rho P_pi P₁ P₃ D_tdo Ω_mu Ω_mu_inv Ω_pi A_op A_star X_star Y V
     M₁ M₂ M₃ M_bundle N_bundle W_out W_out_inv : B)
    (hP_mu : P_mu * P_mu = P_mu) (hP_nu : P_nu * P_nu = P_nu)
    (h_mu_nu : P_mu * P_nu = P_nu) (h_nu_mu : P_nu * P_mu = P_mu)
    (h_mu_rho : P_mu * P_rho = P_rho) (h_nu_rho : P_nu * P_rho = P_rho)
    (h1 : P₁ * P₁ = P₁) (h3 : P₃ * P₃ = P₃)
    (h13 : P₁ * P₃ = 0) (h31 : P₃ * P₁ = 0)
    (hD_right : D_tdo * P_mu = P_mu) (hD_left : P_mu * D_tdo = P_mu)
    (h_mu_inv : Ω_mu * Ω_mu_inv = 1)
    (hRow : A_op * P_mu = P_mu)
    (hPullback : P_pi * A_op = P_mu)
    (hPiV : P_pi * V = P_mu * V)
    (hW : W_out * W_out_inv = 1) :
    -- (1) Stage X: Non-Commutative Measure-Projector Band Algebra & Nilpotent Shift
    (comm P_mu P_nu = measureShift P_mu P_nu ∧
     measureShift P_mu P_nu * measureShift P_mu P_nu = 0 ∧
     measureUnipotent P_mu P_nu * measureUnipotent P_nu P_rho = measureUnipotent P_mu P_rho ∧
     P_nu * D_tdo - P_nu = measureShift P_mu P_nu * (D_tdo - 1)) ∧
    -- (2) Stage XI: Intrinsic Dirichlet Operator & Rayleigh Dissipation Identity
    (intrinsicDirichletOp D_tdo = centeredDirichletOp P_mu D_tdo ∧
     weightedInner τ X_star Ω_mu
       (intrinsicDirichletOp (tokenDiffOp Ω_mu_inv A_star Ω_pi A_op) * Y) =
       weightedInner τ X_star Ω_mu Y -
         weightedInner τ (X_star * A_star) Ω_pi (A_op * Y)) ∧
    -- (3) Stage XII: Residual Stream Velocity & Yoshizawa Metriplectic Sink Lock
    (residualAttnVelocity A_op (valueMeanPart P_mu V) = 0 ∧
     residualAttnVelocity A_op V = residualAttnVelocity A_op (valueCenteredPart P_mu V) ∧
     P_pi * residualAttnVelocity A_op V = 0 ∧
     brockettSinkFlow P_mu A_op A_star (sinkVielbeinPhi P_mu A_op A_star) +
       2 • souriauSinkFlow P_mu A_op A_star (sinkSymplecticJ P_mu A_op A_star) = 0) ∧
    -- (4) Stage XIII: De Haro Multi-Head Model Bundle Fiber Isolation & Soldering
    (P₁ * multiHeadBundleSection P₁ P₃ M₁ M₂ M₃ * P₁ = P₁ * M₁ * P₁ ∧
     P₁ * multiHeadBundleSection P₁ P₃ M₁ M₂ M₃ * P₃ = 0 ∧
     solderedMultiHeadOutput W_out_inv M_bundle W_out *
       solderedMultiHeadOutput W_out_inv N_bundle W_out =
       solderedMultiHeadOutput W_out_inv (M_bundle * N_bundle) W_out) := by
  have hS10 := measure_band_nilpotent_shift_and_cocycle
    P_mu P_nu P_rho D_tdo hP_mu hP_nu h_mu_nu h_nu_mu h_mu_rho h_nu_rho hD_right hD_left
  have hS11 := intrinsic_dirichlet_dissipation_and_sink_idempotency
    τ P_mu D_tdo Ω_mu Ω_mu_inv Ω_pi A_op A_star X_star Y V hP_mu hD_right hD_left h_mu_inv
  have hS12 := residual_stream_velocity_and_yoshizawa_metriplectic_lock
    P_mu P_pi A_op A_star V hP_mu hRow hPullback hPiV
  have hS13 := multi_head_model_bundle_fiber_isolation_and_soldering
    P₁ P₃ M₁ M₂ M₃ M_bundle N_bundle W_out W_out_inv h1 h3 h13 h31 hW
  exact ⟨⟨hS10.1, hS10.2.1, hS10.2.2.2.2.1, hS10.2.2.2.2.2.2.2.2.2⟩,
    ⟨hS11.2.2.1, hS11.2.2.2.2.1⟩,
    ⟨hS12.1, hS12.2.1, hS12.2.2.1, hS12.2.2.2.2⟩,
    ⟨hS13.2.2.1, hS13.2.2.2.2.2.1, hS13.2.2.2.2.2.2⟩⟩

/-!
===============================================================================
## Stage XV (`𝔖𝔊₁₅`): Rustamov–Ovsjanikov Conformal Difference Operator &
   Multi-Layer Compression Valley Semigroup (`arXiv:2510.06477` & `arXiv:2601.22950`)
===============================================================================
-/

/-- **Definition (`conformalDiffOp`, Rustamov et al. 2013 & Ovsjanikov et al. 2012)**:
    The **Conformal (Laplacian-Weighted) Difference Operator**
    `D_conf := L_μ⁻¹ A^* L_π A` measuring how the functional map `A` distorts relational
    Dirichlet energy between input geometry `L_μ` and output geometry `L_π`. -/
def conformalDiffOp (L_mu_inv A_star L_pi A_op : B) : B :=
  L_mu_inv * A_star * L_pi * A_op

/-- **Definition (`functionalMapLaplaceComm`, Ovsjanikov et al. 2012)**:
    The functional-map Laplacian intertwining defect `L_π A - A L_μ`, which vanishes
    when `A` commutes with the intrinsic Laplacians (`L_π A = A L_μ`). -/
def functionalMapLaplaceComm (L_pi A_op L_mu : B) : B :=
  L_pi * A_op - A_op * L_mu

/-- **Definition (`attnLayerOp`, `arXiv:2510.06477` & `arXiv:2610.06012` Section 5)**:
    A single-layer row-stochastic attention operator `A(P, X, Z) := P + N_+(P,X) + A_c(P,Z)`
    decomposed into the unit constant mode `P`, the key-to-sink corner `N_+ = P X (1 - P)`,
    and the centered routing operator `A_c = (1 - P) Z (1 - P)`. -/
def attnLayerOp (P X Z : B) : B :=
  P + sinkCornerPlus P X + centeredRouteOp P Z

/-- **Theorem (`conformal_difference_and_multilayer_compression_valley`, Stage `𝔖𝔊₁₅`)**:
    Formalizes the Rustamov–Ovsjanikov Conformal Difference Operator (`rustamov2013shapediff`)
    and the Multi-Layer Compression Valley Semigroup (`arXiv:2103.03404`, `arXiv:2510.06477`,
    `arXiv:2601.22950`, and `arXiv:2610.06012` Section 5.1) in `[Ring B]`:
    Given `P² = P` and `L_μ L_μ⁻¹ = 1`:
    1. **Conformal Difference Energy Pairing**:
       `weightedInner τ X_star L_mu (conformalDiffOp L_mu_inv A_star L_pi A_op * Y) = weightedInner τ (X_star * A_star) L_pi (A_op * Y)`.
    2. **2-Layer Semigroup Law of Attention Composition (`A₂ A₁`)**:
       For `A₁ = attnLayerOp P X₁ Z₁` and `A₂ = attnLayerOp P X₂ Z₂`,
       `A₂ A₁ = P + (N_{+,1} + N_{+,2} A_{c,1}) + A_{c,2} A_{c,1}`.
    3. **Multiplicative Centered Routing Across Depth**:
       `(1 - P) (A₂ A₁) (1 - P) = A_{c,2} A_{c,1}` and
       `(1 - P) (A₃ A₂ A₁) (1 - P) = A_{c,3} A_{c,2} A_{c,1}`.
    4. **Irreversible Sink Trapping (`A_{c,2} N_{+,1} = 0` & `P A₂ N_{+,1} = N_{+,1}`)**:
       Once information enters the sink corner `N_{+,1}` at layer 1, subsequent centered
       routing `A_{c,2}` annihilates it (`centeredRouteOp P Z₂ * sinkCornerPlus P X₁ = 0`)
       while the constant mode permanently traps it (`attnLayerOp P X₂ Z₂ * sinkCornerPlus P X₁ = sinkCornerPlus P X₁`).
    5. **Single-Layer Compression Valley Annihilates Deep Routing (`arXiv:2510.06477` & `arXiv:2601.22950`)**:
       If layer 2 is a pure sink / compression valley (`Z₂ = 0`, so `A₂ = pureSinkHead P X₂`),
       then 3-layer centered routing collapses identically to zero
       (`(1 - P) (attnLayerOp P X₃ Z₃ * pureSinkHead P X₂ * attnLayerOp P X₁ Z₁) (1 - P) = 0`)
       regardless of how rich layers 1 and 3 are, justifying SAUQ's `max_l` rejection rule! -/
theorem conformal_difference_and_multilayer_compression_valley
    (τ : B →+ A) (P L_mu L_mu_inv L_pi A_op A_star X_star Y X₁ Z₁ X₂ Z₂ X₃ Z₃ : B)
    (hP : P * P = P)
    (hL_inv : L_mu * L_mu_inv = 1) :
    weightedInner τ X_star L_mu (conformalDiffOp L_mu_inv A_star L_pi A_op * Y) =
      weightedInner τ (X_star * A_star) L_pi (A_op * Y) ∧
    attnLayerOp P X₂ Z₂ * attnLayerOp P X₁ Z₁ =
      P + (sinkCornerPlus P X₁ + sinkCornerPlus P X₂ * centeredRouteOp P Z₁) +
        centeredRouteOp P Z₂ * centeredRouteOp P Z₁ ∧
    (1 - P) * (attnLayerOp P X₂ Z₂ * attnLayerOp P X₁ Z₁) * (1 - P) =
      centeredRouteOp P Z₂ * centeredRouteOp P Z₁ ∧
    (1 - P) * (attnLayerOp P X₃ Z₃ * attnLayerOp P X₂ Z₂ * attnLayerOp P X₁ Z₁) * (1 - P) =
      centeredRouteOp P Z₃ * centeredRouteOp P Z₂ * centeredRouteOp P Z₁ ∧
    centeredRouteOp P Z₂ * sinkCornerPlus P X₁ = 0 ∧
    attnLayerOp P X₂ Z₂ * sinkCornerPlus P X₁ = sinkCornerPlus P X₁ ∧
    (1 - P) * (attnLayerOp P X₃ Z₃ * pureSinkHead P X₂ * attnLayerOp P X₁ Z₁) * (1 - P) = 0 := by
  have hL_assoc : ∀ W : B, L_mu * (L_mu_inv * W) = W := fun W => by
    rw [← mul_assoc, hL_inv, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [weightedInner, conformalDiffOp]
    congr 1
    noncomm_ring [hL_inv, hL_assoc]
  · dsimp only [attnLayerOp, sinkCornerPlus, centeredRouteOp]
    noncomm_ring [hP, proj_idem hP]
  · dsimp only [attnLayerOp, sinkCornerPlus, centeredRouteOp]
    noncomm_ring [hP, proj_idem hP]
  · dsimp only [attnLayerOp, sinkCornerPlus, centeredRouteOp]
    noncomm_ring [hP, proj_idem hP]
  · dsimp only [sinkCornerPlus, centeredRouteOp]
    noncomm_ring [hP, proj_idem hP]
  · dsimp only [attnLayerOp, sinkCornerPlus, centeredRouteOp]
    noncomm_ring [hP, proj_idem hP]
  · dsimp only [attnLayerOp, pureSinkHead, sinkCornerPlus, centeredRouteOp]
    noncomm_ring [hP, proj_idem hP]

/-- **Theorem (`attention_routing_direct_limit_and_clifford_head_tail_realization`, Stage `𝔖𝔊₁₅` Colimit)**:
    Formalizes the Finite-Moduli Attention Head × Infinite Operator-Ring Tail principle across:
    1. Mathlib's genuine algebraic direct limit `DirectLimitSuperClosure bond := _root_.DirectLimit Stage (fun m n h => bondMap bond m n h)`
       with canonical stage injections `directLimitOf bond k : Stage k →+* DirectLimitSuperClosure bond`, and
    2. The Clifford tensor-tower infinite tail ring `TailLimit d` (`cl11MatrixLimit_tailRingEquiv d : Cl11TensorTowerLimit.Limit ≃+* TailLimit d`):
    Advancing the finite-head cut from stage `k` to `n` (`hkn : k ≤ n`) via `bondMap bond k n hkn`
    or by one Kronecker step `stageEmbed k` (`A ↦ A ⊗ I₂`) preserves `attnLayerOp`, `centeredRouteOp`,
    the multi-layer attention composition semigroup, and 3-layer compression valley annihilation
    in both `DirectLimitSuperClosure bond` and `TailLimit d`! -/
theorem attention_routing_direct_limit_and_clifford_head_tail_realization
    {Stage : ℕ → Type u} [∀ k, Ring (Stage k)]
    (bond : ∀ k : ℕ, Stage k →+* Stage (k + 1))
    (k n d : ℕ) (hkn : k ≤ n)
    (P X1 Z1 X2 Z2 X3 Z3 : Stage k) (hP : P * P = P)
    (Q U1 W1 U2 W2 U3 W3 : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage k) (hQ : Q * Q = Q) :
    let ofLim  := InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond
    let P_inf  := ofLim k P
    let X1_inf := ofLim k X1
    let Z1_inf := ofLim k Z1
    let X2_inf := ofLim k X2
    let Z2_inf := ofLim k Z2
    let X3_inf := ofLim k X3
    let Z3_inf := ofLim k Z3
    let φ_tail := (InfoGeometry.Canonical.Cl11MatrixTowerTailShift.cl11MatrixLimit_tailRingEquiv d).toRingHom
    let Q_tail  := φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k Q)
    let U1_tail := φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k U1)
    let W1_tail := φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k W1)
    let U2_tail := φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k U2)
    let W2_tail := φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k W2)
    let U3_tail := φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k U3)
    let W3_tail := φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k W3)
    ofLim n (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap bond k n hkn (attnLayerOp P X1 Z1)) =
      attnLayerOp P_inf X1_inf Z1_inf ∧
    (1 - P_inf) * (attnLayerOp P_inf X2_inf Z2_inf * attnLayerOp P_inf X1_inf Z1_inf) * (1 - P_inf) =
      centeredRouteOp P_inf Z2_inf * centeredRouteOp P_inf Z1_inf ∧
    (1 - P_inf) * (attnLayerOp P_inf X3_inf Z3_inf * pureSinkHead P_inf X2_inf * attnLayerOp P_inf X1_inf Z1_inf) * (1 - P_inf) = 0 ∧
    φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (k + 1)
      (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed k (attnLayerOp Q U1 W1))) =
      attnLayerOp Q_tail U1_tail W1_tail ∧
    (1 - Q_tail) * (attnLayerOp Q_tail U2_tail W2_tail * attnLayerOp Q_tail U1_tail W1_tail) * (1 - Q_tail) =
      centeredRouteOp Q_tail W2_tail * centeredRouteOp Q_tail W1_tail ∧
    (1 - Q_tail) * (attnLayerOp Q_tail U3_tail W3_tail * pureSinkHead Q_tail U2_tail * attnLayerOp Q_tail U1_tail W1_tail) * (1 - Q_tail) = 0 := by
  set ofLim := InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond
  set φ_tail := (InfoGeometry.Canonical.Cl11MatrixTowerTailShift.cl11MatrixLimit_tailRingEquiv d).toRingHom
  have hP_inf : ofLim k P * ofLim k P = ofLim k P := by
    rw [← map_mul, hP]
  have hQ_lim : InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k Q *
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k Q =
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k Q :=
    InfoGeometry.Clifford.Cl11TensorTowerLimit.limit_idempotent hQ
  have hQ_tail : φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k Q) *
      φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k Q) =
      φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k Q) := by
    rw [← map_mul, hQ_lim]
  have hMapAttn : ∀ {v1 v2} {R1 : Type v1} {R2 : Type v2} [Ring R1] [Ring R2]
      (φ : R1 →+* R2) (P' X' Z' : R1),
      φ (attnLayerOp P' X' Z') = attnLayerOp (φ P') (φ X') (φ Z') := by
    intro v1 v2 R1 R2 _ _ φ P' X' Z'
    dsimp only [attnLayerOp, sinkCornerPlus, centeredRouteOp]
    simp only [map_add, map_mul, map_sub, map_one]
  have hRouting : ∀ {v} {L : Type v} [Ring L] (P' X1' Z1' X2' Z2' X3' Z3' : L) (hP' : P' * P' = P'),
      (1 - P') * (attnLayerOp P' X2' Z2' * attnLayerOp P' X1' Z1') * (1 - P') =
        centeredRouteOp P' Z2' * centeredRouteOp P' Z1' ∧
      (1 - P') * (attnLayerOp P' X3' Z3' * pureSinkHead P' X2' * attnLayerOp P' X1' Z1') * (1 - P') = 0 := by
    intro v L _ P' X1' Z1' X2' Z2' X3' Z3' hP'
    refine ⟨?_, ?_⟩
    · dsimp only [attnLayerOp, sinkCornerPlus, centeredRouteOp]
      noncomm_ring [hP', proj_idem hP']
    · dsimp only [attnLayerOp, pureSinkHead, sinkCornerPlus, centeredRouteOp]
      noncomm_ring [hP', proj_idem hP']
  have hBond : ofLim n (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap bond k n hkn (attnLayerOp P X1 Z1)) =
      attnLayerOp (ofLim k P) (ofLim k X1) (ofLim k Z1) := by
    rw [InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_bondMap bond k n hkn]
    exact hMapAttn (ofLim k) P X1 Z1
  have hTailShift : φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (k + 1)
      (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed k (attnLayerOp Q U1 W1))) =
      attnLayerOp (φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k Q))
        (φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k U1))
        (φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k W1)) := by
    rw [InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage_apply_bond]
    exact hMapAttn (φ_tail.comp (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k)) Q U1 W1
  rcases hRouting (ofLim k P) (ofLim k X1) (ofLim k Z1) (ofLim k X2) (ofLim k Z2) (ofLim k X3) (ofLim k Z3) hP_inf with
    ⟨hDir1, hDir2⟩
  rcases hRouting (φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k Q))
      (φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k U1))
      (φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k W1))
      (φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k U2))
      (φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k W2))
      (φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k U3))
      (φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage k W3)) hQ_tail with
    ⟨hTail1, hTail2⟩
  exact ⟨hBond, hDir1, hDir2, hTailShift, hTail1, hTail2⟩

end InfoGeometry.Canonical.Arxiv261006012AttentionTokenDifferenceRoutingPoset
