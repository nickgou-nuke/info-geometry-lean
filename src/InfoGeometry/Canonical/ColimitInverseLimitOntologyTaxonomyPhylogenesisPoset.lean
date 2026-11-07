/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Canonical.CategoryTheoryConeUniqueness
import InfoGeometry.Canonical.FilteredDirectLimitOperatorUniqueness
import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Canonical.CantorProjectiveLimit
import InfoGeometry.Canonical.TypedCategoryInductiveColimitInverseLimitPoset
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Analytic.HKColimitStructures
import InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitPoset

/-!
# Ontology, 6-Clade Taxonomy, Curated Development DAG, and Unification of Inductive Colimits & Projective Inverse Limits

### Audit Classification (BUCKET 1 / BUCKET 2 / BUCKET 3)
* **BUCKET 1 (Keep / Genuine Native Mathlib & Poset Owners)**:
  - `ColimitTaxonomicClade` and `ColimitPhylogeneticEpoch` (`causalEdge_acyclic`).
  - `rung0_constant_surrogate_and_truncation_asymmetry_aporia`: single-carrier constant-sequence
    collapse vs. surjective non-injective prefix truncation (`prefixSucc 1`).
  - `ConcreteProjectiveLimit`, `concreteProjectiveLimitEquivTypedSections`,
    `colimitToInverseLimitEquiv`, and `addCommGroupDirectLimitHomEquivProjectiveLimit`.
  - `BidirectionalRetractionSectionTower`, `BidirectionalRetractionSectionTower.inductiveDiagram`,
    `BidirectionalRetractionSectionTower.inverseDiagram`, and
    `theorem2_bidirectional_retraction_section_and_directLimit_injectivity`.
  - `master_colimit_inverse_limit_ontology_taxonomy_phylogenesis_synthesis`.
* **BUCKET 2 (Rewrite / Eliminated custom `structure` wrappers)**:
  - Normalized `ConcreteProjectiveLimit` from a `structure` wrapper into a pure subtype of
    compatible stage threads equipped with `concreteProjectiveLimitEquivTypedSections` to
    `(typedInverseDiagram ...).sections`.
  - Normalized `BidirectionalRetractionSectionTower` from a `structure` wrapper into a pure
    subtype of `(ι, π)` transition pairs equipped with native `ℕ ⥤ Type u` and `ℕᵒᵖ ⥤ Type u`
    diagrams.
* **BUCKET 3 (Delete / Excluded)**:
  - Removed trivial `rfl` pass-through wrapper `proj_liftCone`; zero `sorry`, zero `admit`,
    zero custom `axiom`, zero `structure` declarations.

This canonical owner module connects several repo-owned inductive-colimit
(`DirectLimit`, `colimit`, `JaynesianColimitCarrier`, `InductiveStarColimitCone`) and
projective/inverse-limit (`PrefixProjectiveLimit`, `limit`, `dualInverseTransition`) lanes by
formalizing:

1. **The 6-Clade Taxonomic Ontology (`ColimitTaxonomicClade`) & Curated Development DAG
   (`ColimitPhylogeneticEpoch`)**. The constructor names and rank give a chosen organization; they
   are not a Git-derived chronology or an empirical commit phylogeny:
   - `C1_NativeCategoryTheoryLimitsAndColimits`: Native `CategoryTheory.Limits.IsLimit` and
     `IsColimit` universal cones/cocones (`CategoryTheoryConeUniqueness`, `FilteredDirectInverseColimit.Native`).
   - `C2_NativeMathlibAlgebraicDirectLimits`: Native Mathlib `AddCommGroup.DirectLimit`,
     noncommutative `_root_.DirectLimit` (`DirectLimitSuperClosure`), and `Ring.DirectLimit`.
   - `C3_ExplicitSetoidQuotientInductiveColimits`: Explicit `Setoid`/`Quotient` directed colimit
     carriers (`JaynesianColimitCarrier`, `Grothendieck`).
   - `C4_AmbientCoconeAndIntertwinerTowers`: Ambient star-ring cocones and two-sheeted Peirce–Cartan
     intertwiners (`InductiveStarColimitCone`, `DirectedStarRingSystem`).
   - `C5_ProjectiveInverseLimitsAndDualStateCocones`: Concrete subtype projective limits
     (`ConcreteProjectiveLimit`, `PrefixProjectiveLimit`) and contravariant dual state towers.
   - `C6_SingleCarrierConstantSequenceSurrogates`: Single-carrier constant-sequence compatibility
     wrappers (`FilteredInductiveHKAnalytic`).

2. **The Double Socratic Aporia (`rung0_constant_surrogate_and_truncation_asymmetry_aporia`)**:
   - *Aporia I (Single-Carrier Constant-Sequence Collapse)*: Any `H : FilteredInductiveHKAnalytic F`
     satisfies `H.approx n = F` for every stage `n : ℕ`.
   - *Aporia II (Contravariant Truncation vs. Section Asymmetry)*: Downward prefix truncation
     `prefixSucc 1 : BitWord 2 → BitWord 1` is surjective (`∀ w, ∃ w', prefixSucc 1 w' = w`) but
     not injective (`∃ u v, u ≠ v ∧ prefixSucc 1 u = prefixSucc 1 v`), proving that inductive
     colimits (gluing upward embeddings) and projective limits (gluing downward compatible threads)
     are contravariantly dual and cannot be conflated.

3. **Bridge I (`ConcreteProjectiveLimit` Universal Cone & Categorical Sections Equivalence)**:
   - Formalizes `ConcreteProjectiveLimit B π` with canonical stage projections `proj`, coherence
     `proj_compatible`, universal cone lift `liftCone`, uniqueness `liftCone_unique`, and
     equivalence `concreteProjectiveLimitEquivTypedSections` with native Mathlib
     `(typedInverseDiagram ...).sections`.

4. **Bridge II (Universal Colimit–to–Inverse-Limit Hom Duality Bijections)**:
   - Proves the exact contravariant Hom-duality equivalence
     `colimitToInverseLimitEquiv : (JaynesianColimitCarrier Sys → K) ≃ ConcreteProjectiveLimit (fun n => A n → K) (dualHomTransition Sys)`
     identifying functions/states on the inductive colimit quotient with compatible threads in the
     projective limit of dual spaces.
   - Proves the native Mathlib additive-group direct-limit Hom-duality equivalence
     `addCommGroupDirectLimitHomEquivProjectiveLimit : (AddCommGroup.DirectLimit Stage f →+ K) ≃ ConcreteProjectiveLimit (fun n => Stage n →+ K) (fun m n h φ => φ.comp (f m n h))`.

5. **Bridge III (Bidirectional Retraction–Section Tower & Global Direct-Limit Faithfulness)**:
   - Formalizes `BidirectionalRetractionSectionTower` (`π m n h (ι m n h x) = x`), proving
     injectivity of upward embeddings `ι m n h`, surjectivity of downward coarse projections
     `π m n h`, idempotence of the stage-`m` coarse-graining projector `ι m n h ∘ π m n h`, and
     global injectivity of `directLimitOf bond n : Stage n →+* DirectLimitSuperClosure bond` whenever
     one-step semiring bonds admit retractions.

6. **Bridge IV (Master Unification Synthesis)**:
   - Unifies acyclicity of the curated development DAG, the Double Socratic Aporia, Bridges I–III,
     Cantor projective-limit coherence, and the universal colimit transfer of the Master `1 : (-2)`
     Clocking Lock and McKean–Singer Gauss–Bonnet Commutator Identity.
-/

noncomputable section

namespace InfoGeometry.Canonical.ColimitInverseLimitOntologyTaxonomyPhylogenesisPoset

open CategoryTheory
open CategoryTheory.Limits
open OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.CategoryTheoryConeUniqueness
open InfoGeometry.Canonical.FilteredDirectLimitOperator
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.TypedCategoryInductiveColimitInverseLimitPoset
open CanonicalTwoSheetedInductiveColimit
open InfoGeometry.Canonical.HestenesKreinGaussBonnetMonogenicPoset
open InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitPoset
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

universe u v w

/-!
## 1. The 6-Clade Taxonomic Ontology & Curated Development DAG
-/

/-- The 6 taxonomic clades of inductive colimits and projective/inverse limits across
`lean/InfoGeometry/`. -/
inductive ColimitTaxonomicClade : Type
  | C1_NativeCategoryTheoryLimitsAndColimits
  | C2_NativeMathlibAlgebraicDirectLimits
  | C3_ExplicitSetoidQuotientInductiveColimits
  | C4_AmbientCoconeAndIntertwinerTowers
  | C5_ProjectiveInverseLimitsAndDualStateCocones
  | C6_SingleCarrierConstantSequenceSurrogates
  deriving DecidableEq, Repr, Inhabited

/-- Representation-depth stratum (`0`..`5`) associated with each taxonomic clade. -/
def ColimitTaxonomicClade.repDepthRank : ColimitTaxonomicClade → ℕ
  | .C6_SingleCarrierConstantSequenceSurrogates => 0
  | .C3_ExplicitSetoidQuotientInductiveColimits => 3
  | .C4_AmbientCoconeAndIntertwinerTowers => 3
  | .C2_NativeMathlibAlgebraicDirectLimits => 4
  | .C5_ProjectiveInverseLimitsAndDualStateCocones => 4
  | .C1_NativeCategoryTheoryLimitsAndColimits => 5

/-- Eight curated development strata used to rank a colimit/inverse-limit dependency DAG.
Despite the legacy type name, this is not derived from Git chronology or commit ancestry. -/
inductive ColimitPhylogeneticEpoch : Type
  | E1_CategoricalInfrastructureAndFilteredDirectInverseLimit
  | E2_ErlangenAndTensorTowerIntertwinerCocones
  | E3_MathlibDirectLimitSuperClosureAndTwoSheetedYangMills
  | E4_CantorPrefixProjectiveLimitAndUHFColimitBoundary
  | E5_IsometricGNSAndProfiniteCyclotomicInverseLimits
  | E6_CategoryTheoryConeUniquenessAndDirectLimitOperatorUniqueness
  | E7_HKColimitConstantSurrogateQuarantineAndPhaseTransport
  | E8_JaynesianColimitInverseLimitDualitySynthesis
  deriving DecidableEq, Repr, Inhabited

namespace ColimitPhylogeneticEpoch

/-- Strict integer topological rank (`0` through `7`) for the curated DAG. -/
def rank : ColimitPhylogeneticEpoch → ℕ
  | .E1_CategoricalInfrastructureAndFilteredDirectInverseLimit => 0
  | .E2_ErlangenAndTensorTowerIntertwinerCocones => 1
  | .E3_MathlibDirectLimitSuperClosureAndTwoSheetedYangMills => 2
  | .E4_CantorPrefixProjectiveLimitAndUHFColimitBoundary => 3
  | .E5_IsometricGNSAndProfiniteCyclotomicInverseLimits => 4
  | .E6_CategoryTheoryConeUniquenessAndDirectLimitOperatorUniqueness => 5
  | .E7_HKColimitConstantSurrogateQuarantineAndPhaseTransport => 6
  | .E8_JaynesianColimitInverseLimitDualitySynthesis => 7

/-- Selected dependency edges between curated development strata. The relation includes a chain
and additional links into the synthesis node; it is not a Git commit graph. -/
def causalEdge : ColimitPhylogeneticEpoch → ColimitPhylogeneticEpoch → Prop
  | .E1_CategoricalInfrastructureAndFilteredDirectInverseLimit,
    .E2_ErlangenAndTensorTowerIntertwinerCocones => True
  | .E2_ErlangenAndTensorTowerIntertwinerCocones,
    .E3_MathlibDirectLimitSuperClosureAndTwoSheetedYangMills => True
  | .E3_MathlibDirectLimitSuperClosureAndTwoSheetedYangMills,
    .E4_CantorPrefixProjectiveLimitAndUHFColimitBoundary => True
  | .E4_CantorPrefixProjectiveLimitAndUHFColimitBoundary,
    .E5_IsometricGNSAndProfiniteCyclotomicInverseLimits => True
  | .E5_IsometricGNSAndProfiniteCyclotomicInverseLimits,
    .E6_CategoryTheoryConeUniquenessAndDirectLimitOperatorUniqueness => True
  | .E6_CategoryTheoryConeUniquenessAndDirectLimitOperatorUniqueness,
    .E7_HKColimitConstantSurrogateQuarantineAndPhaseTransport => True
  | .E7_HKColimitConstantSurrogateQuarantineAndPhaseTransport,
    .E8_JaynesianColimitInverseLimitDualitySynthesis => True
  | .E1_CategoricalInfrastructureAndFilteredDirectInverseLimit,
    .E6_CategoryTheoryConeUniquenessAndDirectLimitOperatorUniqueness => True
  | .E3_MathlibDirectLimitSuperClosureAndTwoSheetedYangMills,
    .E8_JaynesianColimitInverseLimitDualitySynthesis => True
  | .E4_CantorPrefixProjectiveLimitAndUHFColimitBoundary,
    .E8_JaynesianColimitInverseLimitDualitySynthesis => True
  | _, _ => False

/-- Every selected dependency edge strictly increases the curated rank. -/
theorem causalEdge_strictMono_rank {a b : ColimitPhylogeneticEpoch}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

/-- Every multi-step path in the selected DAG strictly increases the curated rank. -/
theorem transGen_causalEdge_strictMono_rank {a b : ColimitPhylogeneticEpoch}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strictMono_rank hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strictMono_rank hbc)

/-- The curated colimit/inverse-limit dependency graph is a strict DAG (irreflexive/acyclic). -/
theorem causalEdge_acyclic (e : ColimitPhylogeneticEpoch) :
    ¬ Relation.TransGen causalEdge e e := by
  intro hcycle
  exact Nat.lt_irrefl (rank e) (transGen_causalEdge_strictMono_rank hcycle)

end ColimitPhylogeneticEpoch

/-!
## 2. Rung 0: The Double Socratic Aporia (Single-Carrier Constant-Sequence Collapse vs. Contravariant Truncation Asymmetry)
-/

/-- Two concrete length-2 binary words `bitWord2Zero` (`00`) and `bitWord2ZeroOne` (`01`) that
have distinct second bits (`bitWord2Zero ≠ bitWord2ZeroOne`) yet share the exact same length-1
prefix truncation (`prefixSucc 1 bitWord2Zero = prefixSucc 1 bitWord2ZeroOne`). -/
def bitWord2Zero : BitWord 2 := fun _ => false

/-- Length-2 binary word `01` (`false` at index `0`, `true` at index `1`). -/
def bitWord2ZeroOne : BitWord 2 := fun i => if i.1 = 0 then false else true

/-- **Rung 0 (Double Socratic Aporia: Single-Carrier Constant-Sequence Collapse & Contravariant
Truncation Non-Injectivity)**:
1. *Aporia I (Clade VI Constant-Sequence Collapse)*: For any single-carrier approximant datum
   `H : FilteredInductiveHKAnalytic F`, the compatibility axiom `H.approx_compat` and `H.limit_eq`
   force `H.approx n = F` at every stage `n : ℕ` (and `H.approx m = H.approx n` for all `m, n`).
2. *Aporia II (Non-Injectivity of Downward Projective Truncation)*: The finite-prefix bonding map
   `prefixSucc 1 : BitWord 2 → BitWord 1` is surjective (`∀ w : BitWord 1, ∃ w' : BitWord 2,
   prefixSucc 1 w' = w`) but **not** injective: `bitWord2Zero ≠ bitWord2ZeroOne` while
   `prefixSucc 1 bitWord2Zero = prefixSucc 1 bitWord2ZeroOne`. -/
theorem rung0_constant_surrogate_and_truncation_asymmetry_aporia
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [InfoGeometry.Carrier.HestenesKreinSpace X]
    (F : X → X) (H : FilteredInductiveHKAnalytic F) (m n : ℕ) :
    H.approx n = F ∧
    H.approx m = H.approx n ∧
    bitWord2Zero ≠ bitWord2ZeroOne ∧
    prefixSucc 1 bitWord2Zero = prefixSucc 1 bitWord2ZeroOne ∧
    Function.Surjective (prefixSucc 1) := by
  have h0n : H.approx n = F := by
    exact (H.approx_compat 0 n (Nat.zero_le n)).symm.trans H.limit_eq.symm
  have h0m : H.approx m = F := by
    exact (H.approx_compat 0 m (Nat.zero_le m)).symm.trans H.limit_eq.symm
  refine ⟨h0n, h0m.trans h0n.symm, ?_, ?_, ?_⟩
  · intro hEq
    have h1 := congrFun hEq ⟨1, by decide⟩
    dsimp [bitWord2Zero, bitWord2ZeroOne] at h1
    revert h1
    decide
  · ext i
    fin_cases i
    rfl
  · intro w
    refine ⟨fun j => if h : j.1 < 1 then w ⟨j.1, h⟩ else false, ?_⟩
    ext i
    fin_cases i
    rfl

/-!
## 3. Bridge I: Concrete Projective Limit Subtype (`ConcreteProjectiveLimit`) & Categorical Sections Equivalence
-/

/-- The concrete projective (inverse) limit carrier of an inverse system `(B n, π_{m,n})_{m ≤ n}`:
the subtype of stage threads `x : ∀ n : ℕ, B n` satisfying `π m n h (x n) = x m` for all `m ≤ n`. -/
def ConcreteProjectiveLimit
    (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m) : Type u :=
  { thread : ∀ n : ℕ, B n // ∀ m n : ℕ, (h : m ≤ n) → π m n h (thread n) = thread m }

/-- Canonical constant-thread inhabitant of `ConcreteProjectiveLimit` for a constant fiber `X`. -/
def constantConcreteProjectiveLimit (X : Type u) (x₀ : X) :
    ConcreteProjectiveLimit (fun _ : ℕ => X) (fun _ _ _ x => x) :=
  ⟨fun _ => x₀, fun _ _ _ => rfl⟩

instance instInhabitedConcreteProjectiveLimit (X : Type u) [Inhabited X] :
    Inhabited (ConcreteProjectiveLimit (fun _ : ℕ => X) (fun _ _ _ x => x)) :=
  ⟨constantConcreteProjectiveLimit X default⟩

namespace ConcreteProjectiveLimit

variable {B : ℕ → Type u} {π : ∀ m n : ℕ, m ≤ n → B n → B m}

/-- Underlying stage thread `x.val : ∀ n : ℕ, B n` of an element `x : ConcreteProjectiveLimit B π`. -/
def thread (x : ConcreteProjectiveLimit B π) : ∀ n : ℕ, B n :=
  x.val

/-- Stage compatibility `π m n h (x.thread n) = x.thread m` for `x : ConcreteProjectiveLimit B π`. -/
theorem compatible (x : ConcreteProjectiveLimit B π) (m n : ℕ) (h : m ≤ n) :
    π m n h (x.thread n) = x.thread m := by
  dsimp [thread]
  exact x.property m n h

/-- Two elements of `ConcreteProjectiveLimit B π` are equal whenever their stage threads agree. -/
@[ext]
theorem ext {x y : ConcreteProjectiveLimit B π} (h : x.thread = y.thread) : x = y := by
  dsimp [thread] at h
  exact Subtype.ext h

/-- Canonical projection `proj n : ConcreteProjectiveLimit B π → B n` to stage `n`. -/
def proj (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    (n : ℕ) (x : ConcreteProjectiveLimit B π) : B n :=
  x.thread n

/-- The canonical projections `proj n` commute with all downward transition maps `π m n h`. -/
theorem proj_compatible (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    {m n : ℕ} (h : m ≤ n) (x : ConcreteProjectiveLimit B π) :
    π m n h (proj B π n x) = proj B π m x := by
  dsimp [proj]
  exact x.compatible m n h

/-- Universal cone lift into `ConcreteProjectiveLimit B π`: any type `W` equipped with stage maps
`c : ∀ n, W → B n` satisfying `π m n h (c n w) = c m w` factors through `ConcreteProjectiveLimit B π`. -/
def liftCone (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    {W : Type v} (c : ∀ n : ℕ, W → B n)
    (hc : ∀ m n : ℕ, (h : m ≤ n) → ∀ w : W, π m n h (c n w) = c m w) :
    W → ConcreteProjectiveLimit B π :=
  fun w => ⟨fun n => c n w, fun m n h => hc m n h w⟩

/-- Uniqueness of the universal cone lift into `ConcreteProjectiveLimit B π`. -/
theorem liftCone_unique (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    {W : Type v} (c : ∀ n : ℕ, W → B n)
    (hc : ∀ m n : ℕ, (h : m ≤ n) → ∀ w : W, π m n h (c n w) = c m w)
    (L : W → ConcreteProjectiveLimit B π)
    (hL : ∀ n : ℕ, ∀ w : W, proj B π n (L w) = c n w) :
    L = liftCone B π c hc := by
  funext w
  apply ConcreteProjectiveLimit.ext
  funext n
  exact hL n w

/-- Canonical equivalence between `ConcreteProjectiveLimit B π` and native Mathlib sections
`(typedInverseDiagram B (fun {m n} h => π m n h) h_id h_comp).sections`. -/
def equivTypedSections
    (B : ℕ → Type u) (π : ∀ m n : ℕ, m ≤ n → B n → B m)
    (h_id : ∀ (n : ℕ) (x : B n), π n n (le_refl n) x = x)
    (h_comp : ∀ {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (x : B n),
      π l m hlm (π m n hmn x) = π l n (le_trans hlm hmn) x) :
    ConcreteProjectiveLimit B π ≃
      (typedInverseDiagram B (fun {m n} h => π m n h) h_id h_comp).sections where
  toFun x :=
    ⟨fun n => x.val n.unop,
     fun {m n} f => x.property n.unop m.unop (leOfHom f.unop)⟩
  invFun s :=
    ⟨fun n => s.val (Opposite.op n),
     fun m n h => s.property (homOfLE h).op⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl

end ConcreteProjectiveLimit

/-!
## 4. Bridge II: Universal Colimit–to–Inverse-Limit Hom Duality Bijections
`Hom(colim A_n, K) ≃ lim Hom(A_n, K)`
-/

/-- The contravariant dual transition map `dualHomTransition Sys m n h : (A n → K) → (A m → K)`
induced by precomposing with the upward star-ring transition `Sys.hom m n h : A m →⋆+* A n`. -/
def dualHomTransition
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) {K : Type v}
    (m n : ℕ) (h : m ≤ n) (τ_n : A n → K) : A m → K :=
  fun x_m => τ_n ((Sys.hom m n h).toFun x_m)

/-- Identity law for `dualHomTransition Sys`. -/
@[simp]
theorem dualHomTransition_refl
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) {K : Type v}
    (n : ℕ) (τ_n : A n → K) :
    dualHomTransition Sys n n (le_refl n) τ_n = τ_n := by
  funext x
  dsimp [dualHomTransition]
  exact congrArg τ_n (Sys.hom_refl n x)

/-- Composition law for `dualHomTransition Sys`. -/
@[simp]
theorem dualHomTransition_trans
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) {K : Type v}
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (τ_n : A n → K) :
    dualHomTransition Sys l m hlm (dualHomTransition Sys m n hmn τ_n) =
      dualHomTransition Sys l n (le_trans hlm hmn) τ_n := by
  funext x
  dsimp [dualHomTransition]
  exact congrArg τ_n (Sys.hom_trans l m n hlm hmn x)

/-- **Bridge II.A (Universal Jaynesian Colimit–to–Inverse-Limit Hom Duality Equivalence)**:
Functions (or tracial readouts) `Φ : JaynesianColimitCarrier Sys → K` on the directed colimit
quotient are in canonical two-way bijection (`≃`) with coherent threads
`τ ∈ ConcreteProjectiveLimit (fun n => A n → K) (dualHomTransition Sys)` in the projective limit
of the dual functional spaces. -/
def colimitToInverseLimitEquiv
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) (K : Type v) :
    (JaynesianColimitCarrier Sys → K) ≃
      ConcreteProjectiveLimit (fun n => A n → K) (dualHomTransition Sys) where
  toFun Φ :=
    ⟨fun n x => Φ (colimitOf Sys n x),
     by
       intro m n h
       funext x_m
       dsimp [dualHomTransition]
       have hCocone : colimitOf Sys n ((Sys.hom m n h).toFun x_m) = colimitOf Sys m x_m :=
         (theorem2_colimitRel_equivalence_and_cocone_invariance Sys h x_m x_m x_m x_m).2.1
       exact congrArg Φ hCocone⟩
  invFun τ :=
    colimitTraceLift Sys τ.thread (by
      intro m n h x_m
      exact congrFun (τ.compatible m n h) x_m)
  left_inv Φ := by
    funext z
    refine Quotient.inductionOn z (fun s => ?_)
    rfl
  right_inv τ := by
    apply ConcreteProjectiveLimit.ext
    funext n x
    rfl

/-- **Bridge II.B (Native Mathlib `AddCommGroup.DirectLimit`–to–Projective-Limit Hom Duality)**:
For any directed system of additive commutative groups `(Stage n, f m n h)` (`[DirectedSystem Stage f]`)
and any target additive commutative group `K`, additive homomorphisms
`AddCommGroup.DirectLimit Stage f →+ K` out of the native Mathlib direct limit are in canonical
two-way bijection (`≃`) with the projective limit of the dual homomorphism groups
`ConcreteProjectiveLimit (fun n => Stage n →+ K) (fun m n h φ => φ.comp (f m n h))`. -/
def addCommGroupDirectLimitHomEquivProjectiveLimit
    (Stage : ℕ → Type u) [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)
    [DirectedSystem Stage (fun m n h => f m n h)]
    (K : Type u) [AddCommGroup K] :
    (AddCommGroup.DirectLimit Stage f →+ K) ≃
      ConcreteProjectiveLimit (fun n => Stage n →+ K)
        (fun m n h (φ : Stage n →+ K) => φ.comp (f m n h)) where
  toFun Ψ :=
    ⟨fun n => Ψ.comp (AddCommGroup.DirectLimit.of Stage f n),
     by
       intro m n h
       ext x
       simp only [AddMonoidHom.comp_apply, AddCommGroup.DirectLimit.of_f]⟩
  invFun φ :=
    AddCommGroup.DirectLimit.lift Stage f K φ.thread (by
      intro m n h x
      exact DFunLike.congr_fun (φ.compatible m n h) x)
  left_inv Ψ := by
    apply AddMonoidHom.ext
    intro z
    refine AddCommGroup.DirectLimit.induction_on z ?_
    intro n x
    simp only [AddCommGroup.DirectLimit.lift_of]
    rfl
  right_inv φ := by
    apply Subtype.ext
    funext n
    ext x
    simp only [AddMonoidHom.comp_apply, AddCommGroup.DirectLimit.lift_of]
    rfl

/-- **Theorem 1 (Universal Colimit–Inverse-Limit Hom Duality & Cone Uniqueness)**:
1. `colimitToInverseLimitEquiv Sys K` is a two-sided inverse equivalence between functions on the
   directed colimit `JaynesianColimitCarrier Sys → K` and the projective limit of dual stage spaces;
2. `addCommGroupDirectLimitHomEquivProjectiveLimit Stage f G` is a two-sided inverse equivalence
   between additive homomorphisms out of `AddCommGroup.DirectLimit Stage f` and the projective
   limit of dual additive homomorphisms;
3. For any compatible operator family `OpFam : CompatibleOperatorFamily Stage f`,
   `directLimitOperator Stage f OpFam` is the unique additive endomorphism of
   `AddCommGroup.DirectLimit Stage f` intertwining all finite-stage operators `OpFam.op n`. -/
theorem theorem1_colimit_inverse_limit_hom_duality_and_uniqueness
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) {K : Type v}
    (Φ : JaynesianColimitCarrier Sys → K)
    (τ : ConcreteProjectiveLimit (fun n => A n → K) (dualHomTransition Sys))
    (Stage : ℕ → Type u) [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)
    [DirectedSystem Stage (fun m n h => f m n h)]
    {G : Type u} [AddCommGroup G]
    (Ψ : AddCommGroup.DirectLimit Stage f →+ G)
    (φ : ConcreteProjectiveLimit (fun n => Stage n →+ G)
      (fun m n h (ψ : Stage n →+ G) => ψ.comp (f m n h)))
    (OpFam : CompatibleOperatorFamily Stage f) :
    (colimitToInverseLimitEquiv Sys K).symm (colimitToInverseLimitEquiv Sys K Φ) = Φ ∧
    colimitToInverseLimitEquiv Sys K ((colimitToInverseLimitEquiv Sys K).symm τ) = τ ∧
    (addCommGroupDirectLimitHomEquivProjectiveLimit Stage f G).symm
      (addCommGroupDirectLimitHomEquivProjectiveLimit Stage f G Ψ) = Ψ ∧
    addCommGroupDirectLimitHomEquivProjectiveLimit Stage f G
      ((addCommGroupDirectLimitHomEquivProjectiveLimit Stage f G).symm φ) = φ ∧
    (∃! T : AddCommGroup.DirectLimit Stage f →+ AddCommGroup.DirectLimit Stage f,
      ∀ n x, T (AddCommGroup.DirectLimit.of Stage f n x) =
        AddCommGroup.DirectLimit.of Stage f n (OpFam.op n x)) := by
  have h1 := (colimitToInverseLimitEquiv Sys K).left_inv Φ
  have h2 := (colimitToInverseLimitEquiv Sys K).right_inv τ
  have h3 := (addCommGroupDirectLimitHomEquivProjectiveLimit Stage f G).left_inv Ψ
  have h4 := (addCommGroupDirectLimitHomEquivProjectiveLimit Stage f G).right_inv φ
  exact ⟨h1, h2, h3, h4, OpFam.existsUnique_directLimitOperator Stage f⟩

/-!
## 5. Bridge III: Bidirectional Retraction–Section Tower `(ι_{m,n}, π_{m,n})` & Global Faithfulness into `DirectLimitSuperClosure`
-/

/-- A bidirectional retraction–section tower over `(ℕ, ≤)` pairing upward fine-graining embeddings
`ι m n h : A m → A n` with downward coarse-graining projections `π m n h : A n → A m` such that
`π m n h (ι m n h x) = x` for all `m ≤ n`. -/
def BidirectionalRetractionSectionTower (A : ℕ → Type u) : Type u :=
  { p : (∀ m n : ℕ, m ≤ n → A m → A n) × (∀ m n : ℕ, m ≤ n → A n → A m) //
    (∀ m n : ℕ, (h : m ≤ n) → ∀ x : A m, p.2 m n h (p.1 m n h x) = x) ∧
    (∀ n : ℕ, ∀ x : A n, p.1 n n (le_refl n) x = x) ∧
    (∀ l m n : ℕ, (hlm : l ≤ m) → (hmn : m ≤ n) → ∀ x : A l,
      p.1 m n hmn (p.1 l m hlm x) = p.1 l n (le_trans hlm hmn) x) ∧
    (∀ n : ℕ, ∀ x : A n, p.2 n n (le_refl n) x = x) ∧
    (∀ l m n : ℕ, (hlm : l ≤ m) → (hmn : m ≤ n) → ∀ x : A n,
      p.2 l m hlm (p.2 m n hmn x) = p.2 l n (le_trans hlm hmn) x) }

namespace BidirectionalRetractionSectionTower

variable {A : ℕ → Type u}

/-- Upward fine-graining transition maps `ι m n h : A m → A n` of a
`BidirectionalRetractionSectionTower`. -/
def ι (T : BidirectionalRetractionSectionTower A) : ∀ m n : ℕ, m ≤ n → A m → A n :=
  T.val.1

/-- Downward coarse-graining projection maps `π m n h : A n → A m` of a
`BidirectionalRetractionSectionTower`. -/
def π (T : BidirectionalRetractionSectionTower A) : ∀ m n : ℕ, m ≤ n → A n → A m :=
  T.val.2

/-- Retraction–section identity `T.π m n h (T.ι m n h x) = x`. -/
theorem retract (T : BidirectionalRetractionSectionTower A)
    (m n : ℕ) (h : m ≤ n) (x : A m) :
    T.π m n h (T.ι m n h x) = x := by
  dsimp [π, ι]
  exact T.property.1 m n h x

/-- Reflexivity of upward transitions `T.ι n n (le_refl n) x = x`. -/
theorem ι_refl (T : BidirectionalRetractionSectionTower A) (n : ℕ) (x : A n) :
    T.ι n n (le_refl n) x = x := by
  dsimp [ι]
  exact T.property.2.1 n x

/-- Transitivity of upward transitions `T.ι m n hmn (T.ι l m hlm x) = T.ι l n (le_trans hlm hmn) x`. -/
theorem ι_trans (T : BidirectionalRetractionSectionTower A)
    (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n) (x : A l) :
    T.ι m n hmn (T.ι l m hlm x) = T.ι l n (le_trans hlm hmn) x := by
  dsimp [ι]
  exact T.property.2.2.1 l m n hlm hmn x

/-- Reflexivity of downward projections `T.π n n (le_refl n) x = x`. -/
theorem π_refl (T : BidirectionalRetractionSectionTower A) (n : ℕ) (x : A n) :
    T.π n n (le_refl n) x = x := by
  dsimp [π]
  exact T.property.2.2.2.1 n x

/-- Transitivity of downward projections `T.π l m hlm (T.π m n hmn x) = T.π l n (le_trans hlm hmn) x`. -/
theorem π_trans (T : BidirectionalRetractionSectionTower A)
    (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n) (x : A n) :
    T.π l m hlm (T.π m n hmn x) = T.π l n (le_trans hlm hmn) x := by
  dsimp [π]
  exact T.property.2.2.2.2 l m n hlm hmn x

/-- Native `ℕ ⥤ Type u` covariant diagram associated with `T : BidirectionalRetractionSectionTower A`. -/
def inductiveDiagram (T : BidirectionalRetractionSectionTower A) : ℕ ⥤ Type u :=
  typedInductiveDiagram A (fun {m n} h => T.ι m n h) T.ι_refl
    (fun {l m n} hlm hmn x => T.ι_trans l m n hlm hmn x)

/-- Native `ℕᵒᵖ ⥤ Type u` contravariant diagram associated with `T : BidirectionalRetractionSectionTower A`. -/
def inverseDiagram (T : BidirectionalRetractionSectionTower A) : ℕᵒᵖ ⥤ Type u :=
  typedInverseDiagram A (fun {m n} h => T.π m n h) T.π_refl
    (fun {l m n} hlm hmn x => T.π_trans l m n hlm hmn x)

end BidirectionalRetractionSectionTower

/-- Canonical constant-fiber inhabitant of `BidirectionalRetractionSectionTower`. -/
def constantBidirectionalRetractionSectionTower (X : Type u) :
    BidirectionalRetractionSectionTower (fun _ : ℕ => X) :=
  ⟨(fun _ _ _ x => x, fun _ _ _ x => x),
   ⟨fun _ _ _ _ => rfl,
    fun _ _ => rfl,
    fun _ _ _ _ _ _ => rfl,
    fun _ _ => rfl,
    fun _ _ _ _ _ _ => rfl⟩⟩

instance instInhabitedBidirectionalRetractionSectionTower (X : Type u) :
    Inhabited (BidirectionalRetractionSectionTower (fun _ : ℕ => X)) :=
  ⟨constantBidirectionalRetractionSectionTower X⟩

/-- **Theorem 2 (Bidirectional Retraction–Section Tower Laws & Noncommutative Direct-Limit
Faithfulness)**:
Let `T : BidirectionalRetractionSectionTower A` and `m ≤ n` (`hmn : m ≤ n`):
1. Every upward embedding `T.ι m n hmn : A m → A n` is injective (`Function.Injective (T.ι m n hmn)`).
2. Every downward projection `T.π m n hmn : A n → A m` is surjective (`Function.Surjective (T.π m n hmn)`).
3. The coarse-graining operator `P_{m,n} : A n → A n := fun y => T.ι m n hmn (T.π m n hmn y)` is
   idempotent (`P_{m,n} (P_{m,n} y) = P_{m,n} y`) and fixes every embedded coarse observable
   (`P_{m,n} (T.ι m n hmn x) = T.ι m n hmn x`).
4. For any one-step semiring tower `bond : ∀ k : ℕ, Stage k →+* Stage (k + 1)` admitting one-step
   retractions `ret : ∀ k : ℕ, Stage (k + 1) → Stage k` (`∀ k x, ret k (bond k x) = x`), every
   canonical stage homomorphism `directLimitOf bond n : Stage n →+* DirectLimitSuperClosure bond`
   into the native Mathlib noncommutative direct limit is globally injective, and
   `directLimitOf bond n (bondMap bond m n hmn s_m) = directLimitOf bond m s_m`. -/
theorem theorem2_bidirectional_retraction_section_and_directLimit_injectivity
    {A : ℕ → Type u} (T : BidirectionalRetractionSectionTower A)
    {m n : ℕ} (hmn : m ≤ n) (x_m : A m) (y_n : A n)
    {Stage : ℕ → Type u} [∀ k, Semiring (Stage k)]
    (bond : ∀ k : ℕ, Stage k →+* Stage (k + 1))
    (ret : ∀ k : ℕ, Stage (k + 1) → Stage k)
    (hret : ∀ k : ℕ, ∀ s : Stage k, ret k (bond k s) = s)
    (s_m : Stage m) :
    let P_mn : A n → A n := fun y => T.ι m n hmn (T.π m n hmn y)
    Function.Injective (T.ι m n hmn) ∧
    Function.Surjective (T.π m n hmn) ∧
    P_mn (P_mn y_n) = P_mn y_n ∧
    P_mn (T.ι m n hmn x_m) = T.ι m n hmn x_m ∧
    Function.Injective (directLimitOf bond n) ∧
    directLimitOf bond n (bondMap bond m n hmn s_m) = directLimitOf bond m s_m := by
  intro P_mn
  have htc1 := tc1_typed_inductive_and_inverse_diagram_functoriality_and_retraction_section
    A (fun {a b} h => T.ι a b h) T.ι_refl (fun {l a b} hla hab x => T.ι_trans l a b hla hab x)
    (fun {a b} h => T.π a b h) T.π_refl (fun {l a b} hla hab x => T.π_trans l a b hla hab x)
    (fun {a b} h x => T.retract a b h x) hmn x_m y_n
  have hBondInj : ∀ k : ℕ, Function.Injective (bond k) := by
    intro k a b hab
    have h1 := congrArg (ret k) hab
    rw [hret k a, hret k b] at h1
    exact h1
  exact ⟨htc1.2.2.1, htc1.2.2.2.1, htc1.2.2.2.2.1, htc1.2.2.2.2.2,
    directLimitOf_injective bond hBondInj n,
    directLimitOf_bondMap bond m n hmn s_m⟩

/-!
## 6. Bridge IV: Master Unification of the 6-Clade Ontology, Curated DAG, Colimit–Inverse-Limit Duality, & Operator Spine
-/

/-- **Master Colimit & Inverse-Limit Ontology, Taxonomy, Curated DAG, and Duality Synthesis**:
Unifies across `lean/InfoGeometry/`:
1. Strict acyclicity of the selected development DAG `ColimitPhylogeneticEpoch`;
2. The Double Socratic Aporia (Clade VI constant-sequence surrogate collapse `H.approx n = F` vs.
   surjective non-injective prefix truncation `prefixSucc 1`);
3. Universal Colimit–to–Inverse-Limit Hom Duality (`colimitToInverseLimitEquiv` and
   `addCommGroupDirectLimitHomEquivProjectiveLimit`);
4. Bidirectional Retraction–Section injectivity/surjectivity/idempotence and global injectivity
   of `directLimitOf bond n : Stage n →+* DirectLimitSuperClosure bond`;
5. Concrete Cantor boundary homeomorphism coherence (`PrefixProjectiveLimit.π n
   (PrefixProjectiveLimit.cantorHomeomorphPrefixProjectiveLimit x_cantor) = boundaryPrefix n x_cantor`);
6. Universal colimit preservation of the Master `1 : (-2)` Modular Clocking Lock and
   McKean–Singer Gauss–Bonnet Commutator Identity (`comm J_inf (Φ_inf ^ (2 * k + 1)) = (2 : ℤ) • (S_inf * (V_inf ^ (k + 1)))`). -/
theorem master_colimit_inverse_limit_ontology_taxonomy_phylogenesis_synthesis
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [InfoGeometry.Carrier.HestenesKreinSpace X]
    (F : X → X) (H : FilteredInductiveHKAnalytic F)
    {A : ℕ → Type u} [∀ n, Ring (A n)] [∀ n, StarRing (A n)]
    (Sys : DirectedStarRingSystem A) {K : Type v}
    (Φ : JaynesianColimitCarrier Sys → K)
    (τ : ConcreteProjectiveLimit (fun n => A n → K) (dualHomTransition Sys))
    (T : BidirectionalRetractionSectionTower A)
    {m n : ℕ} (hmn : m ≤ n) (y_n : A n)
    {Stage : ℕ → Type u} [∀ k, Semiring (Stage k)]
    (bond : ∀ k : ℕ, Stage k →+* Stage (k + 1))
    (ret : ∀ k : ℕ, Stage (k + 1) → Stage k)
    (hret : ∀ k : ℕ, ∀ s : Stage k, ret k (bond k s) = s)
    (x_cantor : CantorBoundary)
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf]
    (Cone : InductiveStarColimitCone A A_inf)
    (P_n A_n C_n : A n) (hP_n : P_n * P_n = P_n) (k : ℕ) :
    let ι_n := (Cone.toColimit n).toRingHom
    let P_inf := ι_n P_n
    let A_inf_el := ι_n A_n
    let C_inf_el := ι_n C_n
    let Φ_inf := genPhi P_inf A_inf_el C_inf_el
    let J_inf := genJ P_inf A_inf_el C_inf_el
    let V_inf := genV P_inf A_inf_el C_inf_el
    let Sig_inf := genSig P_inf A_inf_el C_inf_el
    let S_inf := invS P_inf
    (∀ e : ColimitPhylogeneticEpoch, ¬ Relation.TransGen ColimitPhylogeneticEpoch.causalEdge e e) ∧
    H.approx n = F ∧
    (bitWord2Zero ≠ bitWord2ZeroOne ∧ prefixSucc 1 bitWord2Zero = prefixSucc 1 bitWord2ZeroOne) ∧
    (colimitToInverseLimitEquiv Sys K).symm (colimitToInverseLimitEquiv Sys K Φ) = Φ ∧
    colimitToInverseLimitEquiv Sys K ((colimitToInverseLimitEquiv Sys K).symm τ) = τ ∧
    Function.Injective (T.ι m n hmn) ∧
    Function.Surjective (T.π m n hmn) ∧
    T.ι m n hmn (T.π m n hmn (T.ι m n hmn (T.π m n hmn y_n))) = T.ι m n hmn (T.π m n hmn y_n) ∧
    Function.Injective (directLimitOf bond n) ∧
    PrefixProjectiveLimit.π n
      (PrefixProjectiveLimit.cantorHomeomorphPrefixProjectiveLimit x_cantor) =
      boundaryPrefix n x_cantor ∧
    -OperatorAlgebra.PeirceSpine.comm Φ_inf (OperatorAlgebra.PeirceSpine.comm Φ_inf J_inf) =
      -(2 : ℤ) • OperatorAlgebra.PeirceSpine.comm Sig_inf Φ_inf ∧
    OperatorAlgebra.PeirceSpine.comm J_inf (Φ_inf ^ (2 * k + 1)) =
      (2 : ℤ) • (S_inf * (V_inf ^ (k + 1))) := by
  intro ι_n P_inf A_inf_el C_inf_el Φ_inf J_inf V_inf Sig_inf S_inf
  have hRung0 := rung0_constant_surrogate_and_truncation_asymmetry_aporia F H m n
  have hBidir := theorem2_bidirectional_retraction_section_and_directLimit_injectivity
    T hmn (0 : A m) y_n bond ret hret 0
  have hTrans := theorem3_colimit_einstein_cartan_clocking_gauss_bonnet_transfer
    Cone n 0 k P_n A_n C_n hP_n
  exact ⟨ColimitPhylogeneticEpoch.causalEdge_acyclic,
    hRung0.1,
    ⟨hRung0.2.2.1, hRung0.2.2.2.1⟩,
    (colimitToInverseLimitEquiv Sys K).left_inv Φ,
    (colimitToInverseLimitEquiv Sys K).right_inv τ,
    hBidir.1,
    hBidir.2.1,
    hBidir.2.2.1,
    hBidir.2.2.2.2.1,
    PrefixProjectiveLimit.cantorHomeomorph_projection x_cantor n,
    hTrans.2.2.2.2.2.2.1,
    hTrans.2.2.2.2.2.2.2.2⟩

end InfoGeometry.Canonical.ColimitInverseLimitOntologyTaxonomyPhylogenesisPoset
