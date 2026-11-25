# Epistemic compilation: positional encodings as representations of translation

## Scope and source

This note compiles a user-provided podcast/interview transcript on positional
encodings, representation theory, RoPE, linear attention, ALiBi, matrix
exponentials, and Jordan blocks. The transcript is exposition, not Lean
authority. It is classified as **upstream theorem-factory material** with a
strong algebraic core and several engineering/modeling choices that are not
theorems.

No new Lean theorem is promoted here: the transcript's algebraic spine is
already kernel-checked in `info-geometry-lean`. This note records the exact
owner map, the claim ledger, and the remaining open debts.

## Fundamental cut

- **Representation-theoretic core:** a translation-covariant, normalized,
  linear query/key modifier determines a one-parameter group
  `A(s+t) = A(s) * A(t)`, and differentiability at zero forces `A(t)` to be
  the operator exponential of its generator. This is theorem-backed.
- **Concrete normal modes:** two-dimensional elliptic (rotation), hyperbolic
  (real exponential/Chebyshev-type), and parabolic (square-zero Jordan) flows
  are theorem-backed as separate owners. A general diagonalization theorem
  decomposing an arbitrary generator into these modes is **not** promoted.
- **ML instantiation:** RoPE is the elliptic stack; ALiBi is the square-zero
  parabolic score penalty. Linear attention's exponential suppression is a
  model-level decay intent, not by itself a theorem about all linear attention.
- **Engineering choices:** per-token modification instead of per-pair
  modification, linearity, equal-time normalization, real-valued carriers,
  geometric frequency spacing, and continuous-time framing are assumptions or
  design decisions. They are not forced by the transcript's own algebra.

## Four relational layers

1. **Internal consistency:** scores are bilinear; modifying `q` by `F(t)` and
   `k` by `G(s)` rewrites the score through the relative operator
   `F(t)ᵀ * G(s)`. This is exact matrix algebra.
2. **Outward projection:** simultaneous translation invariance collapses the
   two-time operator to a function of `t - s`; normalization at equal times
   makes the factors inverse and yields a one-parameter group law.
3. **Inward perturbation:** differentiability at zero turns the group law into
   the differential equation `A' = A * X`, solved by the operator exponential.
4. **Unexamined boundary:** the normal-mode story uses diagonalizability and
   small Jordan blocks; nonlinear modifiers, pairwise `n²` modifiers, optimal
   frequency schedules, and empirical claims are outside the Lean spine.

## Integrative bridge and exact aporia

The exact bridge is:

```text
linear per-token modifiers
  → relative score operator F(t)ᵀ G(s)
  → translation covariance => A(t-s)
  → A(0)=1 => F(t)ᵀ = G(t)⁻¹
  → A(s+t)=A(s)A(t)
  → differentiable => A(t)=exp(tX)
  → elliptic / hyperbolic / parabolic normal modes
  → RoPE / ALiBi instantiations
```

The aporia: the derivation is conditional on assumptions that are reasonable
but not mathematically inevitable. The transcript itself admits this for the
linearity and per-token-modification assumptions. The algebra classifies the
consequences of a chosen regime; it does not prove that every practical
positional encoding must belong to it, nor that unseen encoding families are
impossible.

## Seven-node dependency order

```text
L1 bilinear attention score and linear modifiers
  → L2 relative score operator F(t)ᵀ G(s)
  → L3 translation covariance and A(t-s)
  → L4 normalization A(0)=1 and inverse factors
  → L5 one-parameter group law A(s+t)=A(s)A(t)
  → L6 differentiable => exponential of generator
  → L7 elliptic/hyperbolic/parabolic modes, RoPE and ALiBi
```

Nodes `L1`–`L7` are owner-backed across
[`PositionalEncodingRepresentation.lean`](../lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean)
and [`PositionalEncodingClassification.lean`](../lean/InfoGeometry/LLM/PositionalEncodingClassification.lean)
for all finite-dimensional diagonalizable, `2 × 2` real complex-pair (`realComplexBlock`),
arbitrary `k × k` Jordan block (`jordanBlock`), decaying linear-attention (`decayFlow`,
`linearAttentionState`), multi-dimensional `(ℝ^d, +)` commuting generators
(`MultiDimTranslationCovariantModifiers`), and 2D RoPE (`rope2DModifiers`) regimes.
Remaining external open debts are only non-linearized / general abstract
canonical-form existence over `ℝ`, geometric frequency-schedule optimality, and
empirical performance claims.

## Repository owner map

| Transcript primitive | Repo-owned source | Exact scope |
|---|---|---|
| attention score as dot product | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:47` (`attentionScore`) | finite-index bilinear score |
| linear modifiers transport through `FᵀG` | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:53` (`transformed_attentionScore_eq_relative`) | exact matrix identity |
| score depends only on `t - s` | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:66` (`transformed_attentionScore_depends_only_on_difference`) | conditional on `F(t)ᵀG(s)=A(t-s)` |
| normalized invertible factorization | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:87` (`TranslationCovariantModifiers`) | stored `Units`, shift-invariant, equal-time normalized |
| `A(0)=I` and inverse factors | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:102` (`keyFactor_eq_inv_queryFactor`), `:129` (`relativeUnit_zero`) | derived from normalization |
| group law `A(s+t)=A(s)A(t)` | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:135` (`relativeUnit_add`) | derived from shift invariance + normalization |
| monoid hom / one-parameter flow | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:157` (`relativeHom`), `:166` (`toRealOneParameterFlow`); `lean/InfoGeometry/Canonical/HypercomplexOneParameterFlows.lean:57` (`RealOneParameterFlow`) | native representation carriers |
| differentiability forces exponential | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:307` (`eval_eq_exponential_of_hasDerivAt_zero`) | Banach-space bounded-operator flow |
| additive-position representation / relative value | `lean/InfoGeometry/Canonical/PositionalDynamicsRegimeBridge.lean:29` (`AdditivePositionRepresentation`), `:26` (`relativeValue_eq_value_sub`) | additive group action and relative composition |
| basis conjugation & diagonal decoupling | `lean/InfoGeometry/LLM/PositionalEncodingClassification.lean:64` (`exp_smul_units_conj`), `:87` (`attentionScore_conj_change_of_basis`), `:99` (`exp_smul_diagonal`), `:135` (`attentionScore_diagonalizable_exp`) | change of basis `(P⁻¹ A P)` and diagonalizable decoupling |
| non-commutativity of matrix generators | `lean/InfoGeometry/LLM/PositionalEncodingClassification.lean:178` (`exists_noncomm_mat2_real`) | explicit `2 × 2` real witness (`rotGen2` vs shift) |
| `2 × 2` real complex-pair normal mode | `lean/InfoGeometry/LLM/PositionalEncodingClassification.lean:157` (`realComplexBlock`), `:233` (`complexToMat2`), `:272` (`exp_smul_realComplexBlock`), `:298` (`exp_smul_rotGen2`) | `exp(t (aI + bJ)) = e^(at) rot2(bt)` |
| block-diagonal stack & continuous RoPE | `lean/InfoGeometry/LLM/PositionalEncodingClassification.lean:326` (`exp_smul_blockDiagonal'`), `:357` (`ropeStackGenerator`), `:402` (`ropeStack_relative_attentionScore`) | decoupled `2 × 2` rotation planes (`ropeStack_relative_attentionScore`) |
| cube-zero 3×3 Jordan polynomial flow | `lean/InfoGeometry/Canonical/PositionalDynamicsRegimeBridge.lean:658` (`N3`), `:662` (`N3_sq_ne_zero`), `:669` (`N3_cube`), `:676` (`expJordanPoly3`), `:686` (`expJordanPoly3_mul`), `:693` (`expJordanPoly3_neg_mul`), `:697` (`expJordanPoly3_mul_neg`) | concrete `N³=0` cell with exact quadratic exponential, group law and inverse laws |
| arbitrary `k × k` Jordan block & kinematics | `lean/InfoGeometry/LLM/PositionalEncodingClassification.lean:442` (`jordanBlock`), `:516` (`exp_smul_jordanBlock`), `:540` (`exp_smul_jordanBlock_apply`), `:570` (`jordanBlock_kinematic_3x3`) | `exp(t(λI+N)) = e^(λt) ∑ (t^m/m!) N^m` and `3 × 3` kinematics |
| degree-`(k-1)` polynomial biases & ALiBi | `lean/InfoGeometry/LLM/PositionalEncodingClassification.lean:590` (`polynomialRelativePenalty_from_jordanBlock`), `:615` (`alibi_recovered_from_jordanBlock_deg1`); `lean/InfoGeometry/LLM/ALiBi.lean:13` (`alibiScore`) | exact `k`-block polynomial penalty; `k = 2` recovers `-p(t - s)` |
| real stability trichotomy & linear attention | `lean/InfoGeometry/LLM/PositionalEncodingClassification.lean:629` (`real_exp_decay_tendsto_zero`), `:666` (`decayFlow`), `:722` (`multiChannelDecayFlow`), `:753` (`linearAttentionState`), `:792` (`linearAttentionReadout_eq_pairwise_sum`) | scalar/multi-channel exponential decay & causal RNN/pairwise sum equivalence |
| multi-dimensional `(ℝ^d, +)` & 2D RoPE | `lean/InfoGeometry/LLM/PositionalEncodingClassification.lean:831` (`MultiDimTranslationCovariantModifiers`), `:942` (`multiDim_generators_commute_and_exp`), `:1114` (`rope2DModifiers`), `:1151` (`rope2D_relative_attentionScore`) | abelian commuting generators and 2D spatial RoPE |
| Cl(5,5) & Drazin–Riesz bridge | `lean/InfoGeometry/LLM/PositionalEncodingClassification.lean:1182` (`rot2InvariantRotorPairing`), `:1195` (`jordanShift_isDrazinInverse_zero`), `:1213` (`jordanShift_constructiveRieszDecompositionAtZero`); `lean/InfoGeometry/Clifford/Cl55RoPEAttentionPairing.lean:85` (`attentionScore`) | bridges planar rotation to `InvariantRotorPairing` and Jordan nilpotent to Drazin–Riesz |
| square-zero parabolic flow `1+tN` | `lean/InfoGeometry/Canonical/HypercomplexOneParameterFlows.lean:88` (`parabolicMat`), `:95` (`parabolicMat_mul`), `:159` (`parabolicFlow_of_sq_eq_zero`) | exact algebraic unipotent flow |
| elliptic rotation flow | `lean/InfoGeometry/Canonical/HypercomplexOneParameterFlows.lean:272` (`ellipticMat`), `:279` (`ellipticMat_mul`), `:371` (`ellipticFlow_of_sq_eq_neg_one`) | `J²=-1` rotation subgroup |
| hyperbolic flow | `lean/InfoGeometry/Canonical/HypercomplexOneParameterFlows.lean:166` (`hyperbolicMat`), `:173` (`hyperbolicMat_mul`) | `H²=1` split flow |
| square-law eigenmode classification | `lean/InfoGeometry/Canonical/HypercomplexOneParameterFlows.lean:419` (`eigenvalue_sq_of_sq_eq_smul`), `:445` (`hyperbolic_eigenvalue_eq_one_or_neg_one`), `:454` (`parabolic_eigenvalue_eq_zero`), `:464` (`elliptic_eigenvalue_eq_I_or_neg_I`), `:494` (`hyperbolicMat_growth`), `:502` (`hyperbolicMat_decay`), `:527` (`ellipticMat_rotation_pos`), `:536` (`ellipticMat_rotation_neg`), `:550` (`ellipticMat_rotation_norm`), `:564` (`parabolicMat_mulVec_jordan`) | `H²=1` gives ±1 growth/decay, `J²=-1` gives ±i unit rotation, `N²=0` gives zero mode and affine Jordan shear |
| Jordan-cell exponential/additivity | `lean/InfoGeometry/Canonical/PositionalDynamicsRegimeBridge.lean:309` (`expJordanCell_add`), `:439` (`expJordanCell_functionRepresentation`) | finite 2×2 parabolic carrier |
| complex characters / Fourier position representation | `lean/InfoGeometry/Canonical/FourierCharacterRepresentationBridge.lean:14` (`toPositionRepresentation`), `:36` (`relative_kernel`) | additive character representation |
| continuous and discrete RoPE relative scores | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:369` (`continuousRopeLayer`), `:375` (`continuousRopeLayer_relative_attentionScore`), `:392` (`discreteRopeLayer`), `:399` (`discreteRopeLayer_relative_attentionScore`) | relative-position attention identity |
| Clifford RoPE pairing | `lean/InfoGeometry/Clifford/Cl55RoPEAttentionPairing.lean:85` (`attentionScore`), `:92` (`attentionScore_eq_relative`), `:112` (`grand_rope_attention_pairing_synthesis`) | Cl(5,5) rotor pairing |
| ALiBi score kernel | `lean/InfoGeometry/LLM/ALiBi.lean:13` (`alibiScore`), `:17` (`alibiScore_translation_invariant`), `:22` (`alibiScore_same_time`) | score-level relative bias |
| ALiBi from a square-zero Jordan block | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:419` (`alibiRelativeFlow`), `:445` (`alibi_parabolic_bias`), `:463` (`alibiAugmentedScore_eq`) | exact `-p t` penalty |
| score-level ALiBi regime | `lean/InfoGeometry/Canonical/UnifiedPositionalRegime.lean:66` (`ScorePositionalRegime`), `:71` (`alibiScorePositionalRegime`) | translation-invariant score carrier |
| scalar exponential decay flow | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:519` (`scalarDecayFlow`), `:535` (`scalarDecayFlow_eval`), `:575` (`scalarDecayFlow_eq_exponential`) | `ℝ` carrier, generator `c • id`, value `exp(c*t)`, identified with the canonical Banach exponential flow |
| concrete exponential relative score | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:590` (`exponentialDecayScore`), `:595` (`exponentialDecayScore_translation_invariant`), `:604` (`exponentialDecayScore_same_time`), `:611` (`exponentialDecayScore_eq_scalarDecayFlow`) | `exp(c*(t-s))*dot q k`, shift-invariant, equal-time normalization, exact scalar-flow readout |

## Claim ledger

| Transcript claim | Disposition |
|---|---|
| Per-token linear modification `F(t)q`, `G(s)k` | Assumed; induced score rewrite is owner-backed |
| `F(t)ᵀG(s)` depends only on `t-s` | Owner-backed conditional theorem |
| `A(0)=I` is harmless normalization | Owner-backed via `normalized` and factor inversion |
| `A(s+t)=A(s)A(t)` | Owner-backed theorem |
| Differentiable `A` is `exp(tX)` | Owner-backed for bounded operators |
| Diagonalizable change of basis decouples modes | Owner-backed (`attentionScore_conj_change_of_basis`, `attentionScore_diagonalizable_exp`) |
| Complex conjugate pairs produce 2×2 real rotation-scaling | Owner-backed (`exp_smul_realComplexBlock`, `ellipticMat_rotation_pos`, `ellipticMat_rotation_neg`) |
| Square-law generators force growth/decay, rotation, or zero modes | Owner-backed (`eigenvalue_sq_of_sq_eq_smul`, `hyperbolicMat_growth`, `hyperbolicMat_decay`, `ellipticMat_rotation_norm`, `parabolicMat_mulVec_jordan`) |
| Defective `k × k` Jordan blocks produce degree-`(k-1)` polynomial time | Owner-backed (`exp_smul_jordanBlock`, `polynomialRelativePenalty_from_jordanBlock`) |
| RoPE is a stack of planar rotations | Owner-backed (`continuousRopeLayer`, `ropeStack_relative_attentionScore`) |
| RoPE geometric frequency schedule | Engineering choice, not a uniqueness theorem |
| ALiBi is recovered from a defective generator | Owner-backed (`alibi_parabolic_bias`, `alibi_recovered_from_jordanBlock_deg1`) |
| Linear attention exponentially suppresses old values & dual RNN/pairwise forms | Owner-backed (`scalarDecayFlow`, `exponentialDecayScore`, `decayFlow`, `multiChannelDecayFlow`, `linearAttentionReadout_eq_pairwise_sum`) |
| Multi-dimensional `(ℝ^d, +)` forces commuting generators & gives 2D RoPE | Owner-backed (`MultiDimTranslationCovariantModifiers`, `multiDim_generators_commute_and_exp`, `rope2D_relative_attentionScore`) |
| Nonlinear modifiers and pairwise `n²` modifiers excluded | Explicit modeling assumptions; not refuted, not formalized |

## Formalization boundary

The algebraic and classification spine for finite-dimensional positional
modifiers is now kernel-checked across
[`PositionalEncodingRepresentation.lean`](../lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean)
and [`PositionalEncodingClassification.lean`](../lean/InfoGeometry/LLM/PositionalEncodingClassification.lean)
(`8992` Lake build jobs, `axiom_check.lean` PASS over `202` declarations,
`opengauss_screener.py` 0 traps, and `proof_proxy_staged_gate.py` ok).
The square-law eigenmode classification and the explicit cube-zero 3×3 Jordan
polynomial flow are now kernel-checked in
[`HypercomplexOneParameterFlows.lean`](../lean/InfoGeometry/Canonical/HypercomplexOneParameterFlows.lean)
and [`PositionalDynamicsRegimeBridge.lean`](../lean/InfoGeometry/Canonical/PositionalDynamicsRegimeBridge.lean).
External open debts outside this spine are: general abstract existence of a real
Jordan canonical basis for an arbitrary operator (beyond the proved normal-form
behaviors and basis-conjugation bridge), RoPE frequency-schedule optimality,
nonlinear or pairwise `n²` modifiers, and empirical benchmarks. None of these is
claimed by this epistemic note.
