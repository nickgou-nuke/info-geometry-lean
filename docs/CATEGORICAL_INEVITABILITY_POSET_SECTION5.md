# Section 5 — Five Algebraic Corridors and the Rising Sea Colimit Synthesis

**Owner module.** `lean/InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesis.lean`
**Audit companion.** `lean/InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesisAudit.lean`
**Last committed baseline.** `ab7465926` (`docs(synthesis): constrain theorem claims`, 2026-10-18).
The working tree documented here includes staged changes beyond that baseline.
Earlier citations of `4e05a39d2` are stale: that commit only wired the module into the
root entrypoint. `62f8324ba` later grew the original synthesis to 84 declarations.
One later conjunction-only package has now been removed; the correspondence
table retains substantive entries and is followed by a scope note.

## Verification status

| Check | Result |
|---|---|
| Public declarations parsed in owner | **103** (0 unparsed declaration-shaped lines) |
| `#print axioms` entries in synthesis companion | **103** |
| `#print axioms` entries in causal-poset companion | **28** |
| Entries resolving in `.trace` | All audited declarations resolved in the owner trace during Gate 4 |
| `sorry` / `admit` / `axiom` / `unsafe` / `native_decide` | No prohibited proof placeholders in the audited owner and companions |
| `sorryAx` in trace | None reported by the Gate 4 kernel audit |
| Axiom footprint | Standard Lean axioms only in the Gate 4 audit |
| OpenGauss Gate 4 `--verify-kernel` | Passed on the owner after the audit-parser correction |
| Screener `--strict` | Passed for the staged Lean source snapshot (0 traps) |

> **Certification-tooling correction.** The audit generator now handles Lean’s
> `noncomputable section` form and fails closed when it cannot parse a declaration.
> Gate 4 passed with 0 unparsed declarations and no rejected axioms. The strict
> screener passed with 0 traps. The test suite was not run.

---

## 5.0 Scope, and what "inevitability" does and does not mean here

The five stages are **linear-algebraic and algebraic** results. The word
"inevitability" is used in the narrative sense *only*: each stage is a
consequence of the hypotheses stated at that stage, with no appeal to physics.
Concretely, the following names from earlier drafts of this section are
**narrative labels, not formalised physics**, and have been removed:

- The Lean module contains **no** Bisognano–Wichmann theory. `lean/InfoGeometry/Dynamics/BisognanoWichmann.lean:19`
  explicitly disclaims the analytic theorem, and `RindlerWedge.lean:18` repeats the disclaimer.
  `inducedComplexStructure_sq_eq_neg_id` is a four-line consequence of `C² = id`,
  `C ∘ K = -(K ∘ C)` and `K² = id`.
- There is **no** orientifold, no CPT operator, and no hyperbolic-plane Möbius
  transformation anywhere in this module. `IsMobiusTwist K M` is the algebraic
  predicate `M ∘ K = -(K ∘ M)`.
- The Chentsov scale `c` is unique **for a fixed** `F`. It is *not* a universal
  constant independent of `F`. The Lean docstring was corrected to say exactly
  this in `ab7465926`.

Section headers below follow the current Lean docstrings.

---

## 5.1 Stage I — Metric

Let `β` be a finite type with `[Fintype β] [DecidableEq β]`. The open simplex
`ProbInterior β` (`ChentsovMetricInvariance.lean:51-54`) consists of
`p : β → ℝ` with `∀ a, 0 < p a` and `∑ a, p a = 1`. The Fisher metric is

```
fisherMetric P u v = ∑ a, (u a * v a) / P.p a        -- ChentsovMetricInvariance.lean:92-94
```

and the tangent hyperplane is `T_P Δ(β) = { w | ∑ a, w a = 0 }`. For a scalar
`c`, `scaledFisherFamily c` has `g := fun _ _ P u v => c * fisherMetric P u v`
(`ChentsovUniqueness.lean:183-184`), so `g_P^(c) = c · g_Fisher,P`.

**Lemma 5.1 (`fisherMetric_smul_left`).** `g_Fisher,P (c • u, v) = c · g_Fisher,P (u, v)`.
`[repo-owned: InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesis#fisherMetric_smul_left]`

**Theorem 5.2 (`scaledFisher_represents_covector_iff`).** For `c ≠ 0` and

`∑ a, n a = 0`:

  (∀ w, ∑ a, w a = 0 → (scaledFisherFamily c).g α P n w = ∑ a, ℓ a * w a)  ↔  n = c⁻¹ • fisherNaturalGradient P ℓ
`[repo-owned: InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesis#scaledFisher_represents_covector_iff]`

**Theorem 5.3 (`chentsov_unique_scale_and_steepest_ascent`).** For

`F : InvariantMetricFamily` with `hF : SeqContinuous F`, there is `∃! c : ℝ` such that

1. for **every** finite `β`, **every** `P`, **every** `u, v` with zero sums,
   `F.g β P u v = (scaledFisherFamily c).g β P u v`; and
2. for `c ≠ 0`, covector representation under `F.g` is equivalent to `n = c⁻¹ • fisherNaturalGradient P ℓ`.

Note that (1) is a **pointwise-universal** statement over `β`, not a
function-level equality `F = g^(c)`. State it that way.

*Proof.* Existence and uniqueness of `c` come from
`chentsov_classification_of_seqContinuous F hF`. For `c ≠ 0`, substitute
`F.g(n,w) = c · g_Fisher,P(n,w) = g_Fisher,P(c • n, w)` via Lemma 5.1 and apply
`fisherNaturalGradient_unique P ℓ (c • n)`, obtaining `c • n = ∇_P^nat ℓ`,
hence `n = c⁻¹ ∇_P^nat ℓ`. ∎

*Non-vacuity.* `fisherMetric_pos_of_ne_zero` (`ChentsovMetricInvariance.lean:158`)
rules out `fisherMetric ≡ 0`, so Theorem 5.2 is not vacuously true.

---

## 5.2 Stage II — Universal `CliffordAlgebra q11Form` nilpotent ladder

Let `q11Form : ℝ² → ℝ` be the split form and `Cl(q_{1,1}) = CliffordAlgebra q11Form`
with canonical embedding `ι`.
`[repo-owned: InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesis#chentsov_unique_scale_and_steepest_ascent]`

**Definition 5.4.** `abstractNullPlus = ½ • (ι (1,0) + ι (0,1))` and

`abstractNullMinus = ½ • (ι (1,0) − ι (0,1))`. By linearity of `ι` these equal
the Witt null basis `½ • ι (1, ±1)`
(`abstractNullPlus_eq_abstractWittPlus`, `abstractNullMinus_eq_abstractWittMinus`).
`[repo-owned: InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesis#abstractNullPlus]`

**Theorem 5.5.** Under `Φ = cl11MatrixAlgEquiv : Cl(q_{1,1}) ≃ₐ[ℝ] M₂(ℝ)`:

- `Φ (abstractNullPlus) = !![0, 1; 0, 0] = E₀₁` and `Φ (abstractNullMinus) = !![0, 0; 1, 0] = E₁₀`;
- pulling back through `Φ.injective`: `n₊² = 0`, `n₋² = 0`, `n₊n₋ + n₋n₊ = 1`;
- `n₊ + n₋ = ι (1,0)` and `n₊ − n₋ = ι (0,1)`;
- further, the chiral volume `ω` anticommutes with both `n₊` and `n₋`
  (`abstractChiralVolume_anticomm_abstractNull{Plus,Minus}`, plus the two
  mixed-product identities), and the two projectors
  `abstractVacProj := n₊ * n₋` and `abstractOccProj := n₋ * n₊` are complementary
  idempotents (`abstractVacProj_idempotent`, `abstractOccProj_idempotent`,
  `abstractVacProj_mul_abstractOccProj_zero`, `abstractOccProj_mul_abstractVacProj_zero`,
  `abstractVacProj_add_abstractOccProj_eq_one`), with
  `abstractOccProj − abstractVacProj = ω`
  (`abstractOccProj_sub_abstractVacProj_eq_chiralVolume`).

Note the naming: `abstractVacProj` is `n₊n₋` (not `½(1−ω)`), and the chiral volume
is `abstractOccProj − abstractVacProj` rather than a separately postulated element.

These extra statements are the ones added in `62f8324ba` and were absent from
earlier drafts of this section.

---

## 5.3 Stage III — Para-Kähler null-sheet identities

Let `V` be a real module with a para-complex structure `K` (`K² = id`) and a
`ParaKahlerStructure g omega K` (`SuperGrassmannianManifold.lean:73-81`):

```
g_symm        : ∀ v w, g v w = g w v
omega_skew    : ∀ v w, omega v w = -omega w v
compatibility : ∀ v w, g v w = omega v (K w)
omega_anti_inv: ∀ v w, omega (K v) (K w) = -omega v w
```

Spectral projectors: `P⁺ = ½ (id + K)`, `P⁻ = ½ (id − K)`, `P⁺ + P⁻ = id`, `K = P⁺ − P⁻`.

> ### ⚠ Corrected compatibility relation
>
> Earlier drafts of this section stated `ω(u,v) = g(Ku,v) = g(u,Kv)`.
> **The first equality is false.** The Lean field reads `g v w = omega v (K w)`,
> which rearranges to
>
> $$\omega(u,v) = g(u, Kv) = -\,g(Ku, v).$$
>
> The second equality is also not an identity but a consequence of
> `metric_anti_invariance`: substituting `u := u`, `w := Kv` and using `K² = id`
> gives `g(Ku,v) = −g(u,Kv)`.
> The module proves the correct form as `omega_eq_g_comp_K : omega v w = g v (K w)`.
> Checked numerically on the `Fin 2` witness `(swapG, swapOmega, swapK)`:
> `g(Ku,v) = u₁v₀ − u₀v₁` while `ω(u,v) = u₀v₁ − u₁v₀`.
`[repo-owned: InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesis#abstractNullPlus_sq_zero]`

**Theorem 5.6.**

1. `g (P⁺v, P⁺w) = 0` and `g (P⁻v, P⁻w) = 0`
   (`paraKahler_projPlus_projPlus_zero`, `paraKahler_projMinus_projMinus_zero`).
2. `g(v,w) = g(P⁺v, P⁻w) + g(P⁻v, P⁺w)`; `g(v,v) = 2 · g(P⁺v, P⁻v)`.
3. `ω(v,w) = g(P⁻v, P⁺w) − g(P⁺v, P⁻w)`.

*Proof.* For (1), `P⁺v ∈ T⁺` so `K(P⁺v) = P⁺v`; applying `metric_anti_invariance`
gives `g(P⁺v,P⁺w) = −g(P⁺v,P⁺w)`, hence `0`. For (2) expand `v = P⁺v + P⁻v`,
`w = P⁺w + P⁻w` and annihilate the diagonal terms. For (3) substitute
`ω(v,w) = g(v, Kw)` (`omega_eq_g_comp_K`) and `Kw = P⁺w − P⁻w`
(`apply_eq_paraProjectorPlus_sub_paraProjectorMinus`). ∎

*Non-vacuity.* `swapParaKahler` (`ParaKahlerLagrangianDimension.lean:221`) inhabits
the hypotheses, and `swapInducedComplex_symplectic_invariant` instantiates them with
no free assumptions.

---

## 5.4 Stage IV — Linear sheet-swap identities and a set-level involution quotient
`[repo-owned: InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesis#paraKahler_metric_eq_offDiagonal_pairing]`

**Definition 5.7.** `IsMobiusTwist K M : Prop := M.comp K = -(K.comp M)`.

`IsSheetSwapInvolution K C := C.comp C = id ∧ IsMobiusTwist K C`.
`[repo-owned: InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesis#IsMobiusTwist]`

**Theorem 5.8.**

1. Every Möbius twist maps `T⁺ → T⁻` and `T⁻ → T⁺`, and intertwines the
   projectors: `P⁻ ∘ M = M ∘ P⁺`, `P⁺ ∘ M = M ∘ P⁻`.
2. For a sheet-swapping involution `C`, `J := C ∘ K` is itself a Möbius twist and
   `J ∘ J = -id_V`. Indeed `C K C K = C (KC) K = C(−CK) K = −C²K² = −id`.
3. If `C` is `g`-isometric, then `g(Jv, Jw) = −g(v,w)` and `ω(Jv, Jw) = ω(v,w)`.
   Since `K(Jw) = K(C(Kw)) = −Cw`,
   `ω(Jv,Jw) = g(C(Kv), C(−w)) = −g(Kv,w) = g(v,Kw)`.
4. **Set-level quotient (added in `62f8324ba`):** `mobiusInvolutionRel` is an
   equivalence relation (`_refl`, `_symm`, `_trans`), hence `mobiusInvolutionSetoid`
   and `MobiusInvolutionQuotient`. In that quotient `P⁺` and `P⁻` become equal
   (`paraProjectorPlus_eq_paraProjectorMinus_in_mobiusQuotient`), the quadratic form
   descends (`mobiusQuotientQuadratic`), and `g(v,v)` is invariant on the relation.
   This is the **set-level \(\mathbb{Z}_2\) orbit quotient**; no topology, smooth
   structure, or stack structure is defined on it.
5. **Concrete witness.** On `Fin 2 → ℝ` with `(swapG, swapOmega, swapK)`,
   `swapSheetInvolution (v₀,v₁) = (v₀,−v₁)` satisfies `IsSheetSwapInvolution`,
   is `swapG`-isometric, and induces `J² = −id` with `swapOmega`-invariance.

---

## 5.5 Stage V — The Rising Sea colimit synthesis

`CuntzMatrixAlgebraicStarColimit.Carrier` is the inductive algebraic `⋆`-colimit of
`M_{2^k}(ℂ)`. The bonding map is `rawMap h = concreteMap h`, obtained by iterating

```
concreteStep n A = (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)) (A ⊗ₖ (1 : M₂(ℂ)))
```

(`CuntzMatrixTraceTower.lean:41-44`) — i.e. genuinely block-diagonal
`A ↦ A ⊗ I_{2^{n−k}}`.

For stage `k`, `ρ_k = attentionDensityMatrix logits β` and
`attentionState logits β A = Matrix.trace (ρ_k · A) = Tr(ρ_k A)`
(`AttentionKMSState.lean:116-118`).
`[repo-owned: InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesis#inducedComplexStructure_sq_eq_neg_id]`

**Theorem 5.9.**

1. `ω^(k)_colim (ι_k (σ_t(A))) = ω_k(A) = Tr(ρ_k A)`.
2. `ω^(k)_colim (ι_k (σ_t (A · (ρ_k B ρ_k^{-1})))) = ω^(k)_colim (ι_k (B·A))`.
3. For `h : k ≤ n`, the same identity with `ι_n (rawMap h (…))` on the left.

The conjugation is computed in `ℝ` and then complexified. This is equivalent to
complexifying first because `complexifyRealMatrix_mul` holds
(`ColimitAttentionTomitaFlow.lean:466`).

**Stage-V algebra (added in `62f8324ba`).** `complexifyRealMatrix` on `0, 1, +`
and unary `-`; colimit creation/annihilation operators `colimitJWCreation k i`,
`colimitJWAnnihilation k i` with `colimitJWCreation_sq_zero`,
`colimitJWAnnihilation_sq_zero`, the same-site canonical anticommutation law
`colimitJW_car_same_site : c_i a_i + a_i c_i = 1`, and a global chirality
`colimitGlobalChirality k` satisfying `colimitGlobalChirality_sq_one` together with
the two conjugation laws `colimitGlobalChirality_conj_jwCreation` and
`colimitGlobalChirality_conj_jwAnnihilation`. All three operators are
`stageInjection k` of the corresponding `TowerMatrix` element, so they live in the
colimit `Carrier` itself.

**Section-6 mixed CAR completion.** The all-site creation/creation and
annihilation/annihilation anticommutators are lifted to `Carrier` by
`colimitJW_anticomm_creation_all` and `colimitJW_anticomm_annihilation_all`.
`colimitJW_annihilation_creation_anticomm_all` lifts the mixed relation for
every pair of sites, with value `if i = j then 1 else 0`. Together with
nilpotency, these state the full finite-stage CAR family for the embedded
Jordan–Wigner operators.

The owner keeps the colimit CAR/parity results, the Möbius quotient identity, and the
cross-stage modular-KMS readout as separate theorems on their respective carriers. No
combined theorem asserts a map or compatibility between the quotient and KMS carriers.

> **Precision limit on Theorem 5.9(3).** The stage-`k` functional
> `selectedStageColimitFunctional k …` is *pinned to stage `k` on both sides*. The
> theorem shows that this functional's value is unchanged when the operator is
> pushed forward along `rawMap` and re-injected at stage `n`. It does **not**
> assert that the colimit state is invariant under refinement in general, and no
> such statement follows.

---

## 5.6 Correspondence table — retained declarations from the original inventory

Statements below are extracted verbatim from the Lean source.

The table preserves the retained entries from the original inventory; its
former final row was removed because it only conjoined unrelated results. The current owner
has additional Section 6 declarations summarized here: Fisher natural-gradient
variance/rate identities; matrix action identities on the concrete `Fin 2`
carrier; cross-sheet pairing and quotient descent; cross-site CAR and pruned
colimit lower bounds. The separate `CategoricalInevitabilityCausalPoset` module
records selected representation and propagation bridges, including the
Möbius quotient pairing descent, all-site mixed colimit CAR, and pruned
cross-stage sink lower bound. It leaves branches without a proved bridge
incomparable and does not identify the quotient carrier with the UHF carrier.

#### Stage I. Metric (3 declarations)

| # | Declaration | Kind | Lean statement (verbatim) |
|---|---|---|---|
| 1 | `fisherMetric_smul_left` | theorem | `(P : ProbInterior α) (c : ℝ) (u v : α → ℝ) : fisherMetric P (c • u) v = c * fisherMetric P u v` |
| 2 | `scaledFisher_represents_covector_iff` | theorem | `(P : ProbInterior α) (ℓ n : α → ℝ) (hn : ∑ a, n a = 0) (c : ℝ) (hc : c ≠ 0) : (∀ w : α → ℝ, ∑ a, w a = 0 → (scaledFisherFamily c).g α P n w = ∑ a, ℓ a * w a) ↔ n = c⁻¹ • fisherNaturalGradient P ℓ` |
| 3 | `chentsov_unique_scale_and_steepest_ascent` | theorem | `(F : InvariantMetricFamily) (hF : SeqContinuous F) : ∃! c : ℝ, (∀ (β : Type) [Fintype β] [DecidableEq β] (P : ProbInterior β) (u v : β → ℝ), ∑ i, u i = 0 → ∑ i, v i = 0 → F.g β P u v = (scaledFisherFamily c).g β P u v) ∧ (c ≠ 0 → ∀ (β : Type) [Fintype β] [DecidableEq β] (P : ProbInterior β) (ℓ n : β → ℝ), ∑ a, n a = 0 → ((∀ w : β → ℝ, ∑ a, w a = 0 → F.g β P n w = ∑ a, ℓ a * w a) ↔ n = c⁻¹ • fisherNaturalGradient P ℓ))` |

#### Stage II. Cell (26 declarations)

| # | Declaration | Kind | Lean statement (verbatim) |
|---|---|---|---|
| 4 | `abstractNullPlus` | def | `noncomputable def abstractNullPlus : CliffordAlgebra q11Form` |
| 5 | `abstractNullMinus` | def | `noncomputable def abstractNullMinus : CliffordAlgebra q11Form` |
| 6 | `abstractNullPlus_eq_abstractWittPlus` | theorem | `: abstractNullPlus = abstractWittPlus` |
| 7 | `abstractNullMinus_eq_abstractWittMinus` | theorem | `: abstractNullMinus = abstractWittMinus` |
| 8 | `cl11MatrixAlgEquiv_abstractNullPlus` | theorem | `: cl11MatrixAlgEquiv abstractNullPlus = !![(0 : ℝ), 1; 0, 0]` |
| 9 | `cl11MatrixAlgEquiv_abstractNullMinus` | theorem | `: cl11MatrixAlgEquiv abstractNullMinus = !![(0 : ℝ), 0; 1, 0]` |
| 10 | `cl11MatrixAlgEquiv_chiralVolume` | theorem | `: cl11MatrixAlgEquiv abstractChiralVolume = !![(-1 : ℝ), 0; 0, 1]` |
| 11 | `abstractNullPlus_sq_zero` | theorem | `: abstractNullPlus * abstractNullPlus = 0` |
| 12 | `abstractNullMinus_sq_zero` | theorem | `: abstractNullMinus * abstractNullMinus = 0` |
| 13 | `abstractNullPlus_anticomm_abstractNullMinus` | theorem | `: abstractNullPlus * abstractNullMinus + abstractNullMinus * abstractNullPlus = 1` |
| 14 | `abstractNullPlus_sub_abstractNullMinus_eq_ι_eMinus` | theorem | `: abstractNullPlus - abstractNullMinus = CliffordAlgebra.ι q11Form (0, 1)` |
| 15 | `abstractNullPlus_add_abstractNullMinus_eq_ι_ePlus` | theorem | `: abstractNullPlus + abstractNullMinus = CliffordAlgebra.ι q11Form (1, 0)` |
| 16 | `abstractChiralVolume_mul_abstractNullPlus` | theorem | `: abstractChiralVolume * abstractNullPlus = -abstractNullPlus` |
| 17 | `abstractNullPlus_mul_abstractChiralVolume` | theorem | `: abstractNullPlus * abstractChiralVolume = abstractNullPlus` |
| 18 | `abstractChiralVolume_mul_abstractNullMinus` | theorem | `: abstractChiralVolume * abstractNullMinus = abstractNullMinus` |
| 19 | `abstractNullMinus_mul_abstractChiralVolume` | theorem | `: abstractNullMinus * abstractChiralVolume = -abstractNullMinus` |
| 20 | `abstractChiralVolume_anticomm_abstractNullPlus` | theorem | `: abstractChiralVolume * abstractNullPlus + abstractNullPlus * abstractChiralVolume = 0` |
| 21 | `abstractChiralVolume_anticomm_abstractNullMinus` | theorem | `: abstractChiralVolume * abstractNullMinus + abstractNullMinus * abstractChiralVolume = 0` |
| 22 | `abstractVacProj` | def | `noncomputable def abstractVacProj : CliffordAlgebra q11Form` |
| 23 | `abstractOccProj` | def | `noncomputable def abstractOccProj : CliffordAlgebra q11Form` |
| 24 | `abstractVacProj_idempotent` | theorem | `: abstractVacProj * abstractVacProj = abstractVacProj` |
| 25 | `abstractOccProj_idempotent` | theorem | `: abstractOccProj * abstractOccProj = abstractOccProj` |
| 26 | `abstractVacProj_mul_abstractOccProj_zero` | theorem | `: abstractVacProj * abstractOccProj = 0` |
| 27 | `abstractOccProj_mul_abstractVacProj_zero` | theorem | `: abstractOccProj * abstractVacProj = 0` |
| 28 | `abstractVacProj_add_abstractOccProj_eq_one` | theorem | `: abstractVacProj + abstractOccProj = 1` |
| 29 | `abstractOccProj_sub_abstractVacProj_eq_chiralVolume` | theorem | `: abstractOccProj - abstractVacProj = abstractChiralVolume` |

#### Stage III. Null sheets (7 declarations)

| # | Declaration | Kind | Lean statement (verbatim) |
|---|---|---|---|
| 30 | `paraKahler_projPlus_projPlus_zero` | theorem | `{g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V} (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v w : V) : g (paraProjectorPlus K v) (paraProjectorPlus K w) = 0` |
| 31 | `paraKahler_projMinus_projMinus_zero` | theorem | `{g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V} (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v w : V) : g (paraProjectorMinus K v) (paraProjectorMinus K w) = 0` |
| 32 | `paraKahler_metric_eq_offDiagonal_pairing` | theorem | `{g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V} (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v w : V) : g v w = g (paraProjectorPlus K v) (paraProjectorMinus K w) + g (paraProjectorMinus K v) (paraProjectorPlus K w)` |
| 33 | `paraKahler_self_metric_eq_two_mul_cross_sheet` | theorem | `{g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V} (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v : V) : g v v = 2 * g (paraProjectorPlus K v) (paraProjectorMinus K v)` |
| 34 | `apply_eq_paraProjectorPlus_sub_paraProjectorMinus` | theorem | `(K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (w : V) : K w = paraProjectorPlus K w - paraProjectorMinus K w` |
| 35 | `omega_eq_g_comp_K` | theorem | `{g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V} (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v w : V) : omega v w = g v (K w)` |
| 36 | `paraKahler_symplectic_eq_offDiagonal_pairing` | theorem | `{g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V} (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v w : V) : omega v w = g (paraProjectorMinus K v) (paraProjectorPlus K w) - g (paraProjectorPlus K v) (paraProjectorMinus K w)` |

#### Stage IV. Sheet swap (31 declarations)

| # | Declaration | Kind | Lean statement (verbatim) |
|---|---|---|---|
| 37 | `IsMobiusTwist` | def | `(K M : V →ₗ[ℝ] V) : Prop` |
| 38 | `mobiusTwist_apply_comm` | theorem | `(K M : V →ₗ[ℝ] V) (hM : IsMobiusTwist K M) (v : V) : K (M v) = -M (K v)` |
| 39 | `mobiusTwist_maps_tplus_to_tminus` | theorem | `(K M : V →ₗ[ℝ] V) (hM : IsMobiusTwist K M) {v : V} (hv : InTPlus K v) : InTMinus K (M v)` |
| 40 | `mobiusTwist_maps_tminus_to_tplus` | theorem | `(K M : V →ₗ[ℝ] V) (hM : IsMobiusTwist K M) {v : V} (hv : InTMinus K v) : InTPlus K (M v)` |
| 41 | `mobiusTwist_intertwines_paraProjectorPlus` | theorem | `(K M : V →ₗ[ℝ] V) (hM : IsMobiusTwist K M) (v : V) : paraProjectorMinus K (M v) = M (paraProjectorPlus K v)` |
| 42 | `mobiusTwist_intertwines_paraProjectorMinus` | theorem | `(K M : V →ₗ[ℝ] V) (hM : IsMobiusTwist K M) (v : V) : paraProjectorPlus K (M v) = M (paraProjectorMinus K v)` |
| 43 | `IsSheetSwapInvolution` | def | `(K C : V →ₗ[ℝ] V) : Prop` |
| 44 | `sheetSwapInvolution_apply_sq` | theorem | `(K C : V →ₗ[ℝ] V) (hC : IsSheetSwapInvolution K C) (v : V) : C (C v) = v` |
| 45 | `inducedComplexStructure` | def | `(C K : V →ₗ[ℝ] V) : V →ₗ[ℝ] V` |
| 46 | `inducedComplexStructure_sq_eq_neg_id` | theorem | `(K C : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (hC : IsSheetSwapInvolution K C) : (inducedComplexStructure C K).comp (inducedComplexStructure C K) = -LinearMap.id` |
| 47 | `inducedComplexStructure_isMobiusTwist` | theorem | `(K C : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (hC : IsSheetSwapInvolution K C) : IsMobiusTwist K (inducedComplexStructure C K)` |
| 48 | `inducedComplexStructure_metric_neg` | theorem | `(g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v w : V) : g (inducedComplexStructure C K v) (inducedComplexStructure C K w) = -g v w` |
| 49 | `inducedComplexStructure_symplectic_invariant` | theorem | `(g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (hC : IsSheetSwapInvolution K C) (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v w : V) : omega (inducedComplexStructure C K v) (inducedComplexStructure C K w) = omega v w` |
| 50 | `mobiusInvolutionRel` | def | `(C : V →ₗ[ℝ] V) (u w : V) : Prop` |
| 51 | `mobiusInvolutionRel_refl` | theorem | `(C : V →ₗ[ℝ] V) (u : V) : mobiusInvolutionRel C u u` |
| 52 | `mobiusInvolutionRel_symm` | theorem | `{K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) {u w : V} (huw : mobiusInvolutionRel C u w) : mobiusInvolutionRel C w u` |
| 53 | `mobiusInvolutionRel_trans` | theorem | `{K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) {u v w : V} (huv : mobiusInvolutionRel C u v) (hvw : mobiusInvolutionRel C v w) : mobiusInvolutionRel C u w` |
| 54 | `mobiusInvolutionSetoid` | def | `{K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) : Setoid V where r` |
| 55 | `MobiusInvolutionQuotient` | abbrev | `{K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) : Type _` |
| 56 | `paraProjectorPlus_eq_paraProjectorMinus_in_mobiusQuotient` | theorem | `{K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) (v : V) : (Quotient.mk (mobiusInvolutionSetoid hC) (paraProjectorPlus K v) : MobiusInvolutionQuotient hC) = Quotient.mk (mobiusInvolutionSetoid hC) (paraProjectorMinus K (C v))` |
| 57 | `metric_self_eq_of_mobiusInvolutionRel` | theorem | `(g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {C : V →ₗ[ℝ] V} (hC_iso : ∀ u w, g (C u) (C w) = g u w) {u w : V} (huw : mobiusInvolutionRel C u w) : g u u = g w w` |
| 58 | `mobiusQuotientQuadratic` | def | `(g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) (hC_iso : ∀ u w, g (C u) (C w) = g u w) : MobiusInvolutionQuotient hC → ℝ` |
| 59 | `mobiusQuotientQuadratic_mk` | theorem | `(g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v : V) : mobiusQuotientQuadratic g hC hC_iso (Quotient.mk (mobiusInvolutionSetoid hC) v) = g v v` |
| 60 | `swapSheetInvolution` | def | `: (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where toFun v i` |
| 61 | `swapSheetInvolution_apply_zero` | theorem | `(v : Fin 2 → ℝ) : swapSheetInvolution v 0 = v 0` |
| 62 | `swapSheetInvolution_apply_one` | theorem | `(v : Fin 2 → ℝ) : swapSheetInvolution v 1 = -v 1` |
| 63 | `swapSheetInvolution_isMobiusTwist` | theorem | `: IsMobiusTwist swapK swapSheetInvolution` |
| 64 | `isSheetSwapInvolution_canonical` | theorem | `: IsSheetSwapInvolution swapK swapSheetInvolution` |
| 65 | `swapSheetInvolution_preserves_swapG` | theorem | `(u w : Fin 2 → ℝ) : swapG (swapSheetInvolution u) (swapSheetInvolution w) = swapG u w` |
| 66 | `swapInducedComplex_sq_eq_neg_id` | theorem | `: (inducedComplexStructure swapSheetInvolution swapK).comp (inducedComplexStructure swapSheetInvolution swapK) = -LinearMap.id` |
| 67 | `swapInducedComplex_symplectic_invariant` | theorem | `(v w : Fin 2 → ℝ) : swapOmega (inducedComplexStructure swapSheetInvolution swapK v) (inducedComplexStructure swapSheetInvolution swapK w) = swapOmega v w` |

#### Stage V. Rising Sea (17 declarations)

| # | Declaration | Kind | Lean statement (verbatim) |
|---|---|---|---|
| 68 | `complexifyRealMatrix_zero` | theorem | `{ι : Type*} [Fintype ι] [DecidableEq ι] : complexifyRealMatrix (0 : Matrix ι ι ℝ) = 0` |
| 69 | `complexifyRealMatrix_one` | theorem | `{ι : Type*} [Fintype ι] [DecidableEq ι] : complexifyRealMatrix (1 : Matrix ι ι ℝ) = 1` |
| 70 | `complexifyRealMatrix_add` | theorem | `{ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) : complexifyRealMatrix (A + B) = complexifyRealMatrix A + complexifyRealMatrix B` |
| 71 | `complexifyRealMatrix_neg` | theorem | `{ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : complexifyRealMatrix (-A) = -complexifyRealMatrix A` |
| 72 | `colimitJWCreation` | def | `noncomputable def colimitJWCreation (k : ℕ) (i : Fin k) : Carrier` |
| 73 | `colimitJWAnnihilation` | def | `noncomputable def colimitJWAnnihilation (k : ℕ) (i : Fin k) : Carrier` |
| 74 | `colimitGlobalChirality` | def | `noncomputable def colimitGlobalChirality (k : ℕ) : Carrier` |
| 75 | `colimitJWCreation_sq_zero` | theorem | `(k : ℕ) (i : Fin k) : colimitJWCreation k i * colimitJWCreation k i = 0` |
| 76 | `colimitJWAnnihilation_sq_zero` | theorem | `(k : ℕ) (i : Fin k) : colimitJWAnnihilation k i * colimitJWAnnihilation k i = 0` |
| 77 | `colimitJW_car_same_site` | theorem | `(k : ℕ) (i : Fin k) : colimitJWCreation k i * colimitJWAnnihilation k i + colimitJWAnnihilation k i * colimitJWCreation k i = 1` |
| 78 | `colimitGlobalChirality_sq_one` | theorem | `(k : ℕ) : colimitGlobalChirality k * colimitGlobalChirality k = 1` |
| 79 | `colimitGlobalChirality_conj_jwCreation` | theorem | `(k : ℕ) (i : Fin k) : colimitGlobalChirality k * colimitJWCreation k i * colimitGlobalChirality k = -colimitJWCreation k i` |
| 80 | `colimitGlobalChirality_conj_jwAnnihilation` | theorem | `(k : ℕ) (i : Fin k) : colimitGlobalChirality k * colimitJWAnnihilation k i * colimitGlobalChirality k = -colimitJWAnnihilation k i` |
| 81 | `risingSea_colimit_modularFlow_invariance` | theorem | `(k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) : selectedStageColimitFunctional k (attentionStageDensity k logits β) (stageInjection k (modularFlow logits β t (complexifyRealMatrix A))) = (attentionState logits β A : ℂ)` |
| 82 | `risingSea_colimit_modular_kms_synthesis` | theorem | `(k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) : selectedStageColimitFunctional k (attentionStageDensity k logits β) (stageInjection k (modularFlow logits β t (complexifyRealMatrix A * complexifyRealMatrix (attentionDensityMatrix logits β * B * attentionDensityMatrixInv logits β)))) = selectedStageColimitFunctional k (attentionStageDensity k logits β) (stageInjection k (complexifyRealMatrix (B * A)))` |
| 83 | `risingSea_tower_propagation_modular_kms_synthesis` | theorem | `{k n : ℕ} (h : k ≤ n) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) : selectedStageColimitFunctional k (attentionStageDensity k logits β) (stageInjection n (rawMap h (modularFlow logits β t (complexifyRealMatrix A * complexifyRealMatrix (attentionDensityMatrix logits β * B * attentionDensityMatrixInv logits β))))) = selectedStageColimitFunctional k (attentionStageDensity k logits β) (stageInjection k (complexifyRealMatrix (B * A)))` |
`[repo-owned: InfoGeometry/Synthesis/CategoricalInevitabilityPosetSynthesis#risingSea_colimit_modularFlow_invariance; InfoGeometry/QuantumContext/AttentionKMSState#attentionState]`
