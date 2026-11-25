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

Nodes `L1`–`L6` are owner-backed. `L7` is owner-backed only for the concrete
low-dimensional elliptic, hyperbolic, parabolic, RoPE, and ALiBi carriers; the
general diagonalization classification remains open debt.

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
| square-zero parabolic flow `1+tN` | `lean/InfoGeometry/Canonical/HypercomplexOneParameterFlows.lean:88` (`parabolicMat`), `:95` (`parabolicMat_mul`), `:159` (`parabolicFlow_of_sq_eq_zero`) | exact algebraic unipotent flow |
| elliptic rotation flow | `lean/InfoGeometry/Canonical/HypercomplexOneParameterFlows.lean:272` (`ellipticMat`), `:279` (`ellipticMat_mul`), `:371` (`ellipticFlow_of_sq_eq_neg_one`) | `J²=-1` rotation subgroup |
| hyperbolic flow | `lean/InfoGeometry/Canonical/HypercomplexOneParameterFlows.lean:166` (`hyperbolicMat`), `:173` (`hyperbolicMat_mul`) | `H²=1` split flow |
| Jordan-cell exponential/additivity | `lean/InfoGeometry/Canonical/PositionalDynamicsRegimeBridge.lean:309` (`expJordanCell_add`), `:439` (`expJordanCell_functionRepresentation`) | finite 2×2 parabolic carrier |
| complex characters / Fourier position representation | `lean/InfoGeometry/Canonical/FourierCharacterRepresentationBridge.lean:14` (`toPositionRepresentation`), `:36` (`relative_kernel`) | additive character representation |
| continuous and discrete RoPE relative scores | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:369` (`continuousRopeLayer`), `:375` (`continuousRopeLayer_relative_attentionScore`), `:392` (`discreteRopeLayer`), `:399` (`discreteRopeLayer_relative_attentionScore`) | relative-position attention identity |
| Clifford RoPE pairing | `lean/InfoGeometry/Clifford/Cl55RoPEAttentionPairing.lean:85` (`attentionScore`), `:92` (`attentionScore_eq_relative`), `:112` (`grand_rope_attention_pairing_synthesis`) | Cl(5,5) rotor pairing |
| ALiBi score kernel | `lean/InfoGeometry/LLM/ALiBi.lean:13` (`alibiScore`), `:17` (`alibiScore_translation_invariant`), `:22` (`alibiScore_same_time`) | score-level relative bias |
| ALiBi from a square-zero Jordan block | `lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean:419` (`alibiRelativeFlow`), `:445` (`alibi_parabolic_bias`), `:463` (`alibiAugmentedScore_eq`) | exact `-p t` penalty |
| unified score-regime interface | `lean/InfoGeometry/Canonical/UnifiedPositionalRegime.lean:66` (`ScorePositionalRegime`), `:71` (`alibiScorePositionalRegime`) | translation-invariant score carrier |

## Claim ledger

| Transcript claim | Disposition |
|---|---|
| Per-token linear modification `F(t)q`, `G(s)k` | Assumed; induced score rewrite is owner-backed |
| `F(t)ᵀG(s)` depends only on `t-s` | Owner-backed conditional theorem |
| `A(0)=I` is harmless normalization | Owner-backed via `normalized` and factor inversion |
| `A(s+t)=A(s)A(t)` | Owner-backed theorem, not a new claim here |
| Differentiable `A` is `exp(tX)` | Owner-backed for bounded operators |
| Real positive/negative/zero generator modes | Concrete hyperbolic/exponential owners; general classification open |
| Complex generator pairs give rotations | Concrete elliptic owner and complex character owner; general diagonalization open |
| Non-diagonalizable generators give polynomial time | Square-zero parabolic owner and Jordan-cell owner; larger Jordan blocks open |
| RoPE is a stack of planar rotations | Owner-backed continuous/discrete RoPE relative scores |
| RoPE geometric frequency schedule | Engineering choice, not theorem |
| ALiBi is recovered from a defective generator | Owner-backed exact `-p t` realization |
| Linear attention exponentially suppresses old values | Model-level intent; generic exponential flow owner exists, but a specific linear-attention decay theorem is open debt |
| Nonlinear modifiers and pairwise `n²` modifiers excluded | Explicit modeling assumptions; not refuted, not formalized |

## Formalization boundary

The algebraic spine is already kernel-checked. Remaining debts are:
a general diagonalizable-generator decomposition theorem; larger Jordan blocks;
a concrete scalar negative-generator decay theorem tied to a named
linear-attention carrier; frequency-schedule optimality; and any empirical or
practical-universality claim. None of these is closed by this epistemic note.
