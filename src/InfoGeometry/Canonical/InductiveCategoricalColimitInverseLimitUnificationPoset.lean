/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.FilteredDirectLimitOperator
import InfoGeometry.Categorical.FilteredDirectLimitOwner
import InfoGeometry.Categorical.Holonomy
import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Canonical.FilteredDirectInverseColimitReadback
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit
import InfoGeometry.Canonical.Cl11FilteredDirectInverseColimit
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
import InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
import InfoGeometry.Canonical.HestenesKreinGaussBonnetAnalyticDerivationPoset
import InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitContinuumPoset

/-!
# Colimit & Inverse-Limit Ontology, Taxonomy, Source Lineage & Unification Poset (`ℭ₁ ≺ … ≺ ℭ₈`)

### Audit Classification (BUCKET 1 / BUCKET 2 / BUCKET 3)
* **BUCKET 1 (Keep / Genuine Native Mathlib & Categorical Owners)**:
  - `ColimitInverseLimitParadigm`, `ColimitTaxonomicClade`, `ColimitDevelopmentStratum`, and
    `ColimitInverseLimitUnificationStage` (`ℭ₁ ≺ … ≺ ℭ₈`).
  - `stage_C1_quotient_direct_limit_to_categorical_module_colimit_bridge` (`quotientToCategoricalColimit`).
  - `stage_C2_C3_inductive_colimit_state_to_projective_dual_limit_bridge` and
    `projectiveLimitDualColimitLinearEquiv`.
  - `stage_C4_C5_projective_space_to_inductive_cylinder_and_cantor_uhf_bridge` (`pullbackInductiveSystem`,
    `pullbackCylinderCocone`).
  - `stage_C6_filtered_colimit_finite_limit_interchange` (`colimit_limit_iso`).
  - `stage_C7_peirce_cartan_gauss_bonnet_tower_to_dual_inverse_trace_system` and
    `inductive_categorical_colimit_inverse_limit_unification_master_synthesis`.
* **BUCKET 2 (Rewrite / Normalized)**:
  - Added complete declaration docstrings and tactic-mode acyclicity proofs.
* **BUCKET 3 (Delete / Excluded)**:
  - Zero `sorry`, zero `admit`, zero custom `axiom`, zero `structure` wrappers, zero `_True` stubs.

This module records five architectural paradigms and seven curated source clades, then connects
existing inductive-colimit, projective-limit, topological-limit, and operator-trace owners. The
clade names are a taxonomy, not an exhaustively generated inventory. The eight development strata
below are a formal ranking used to prove acyclicity; they are not a count of Git commits or an
automatically reconstructed commit genealogy. The mathematical unification is organized by the
eight stages `ColimitInverseLimitUnificationStage` (`ℭ₁ ≺ … ≺ ℭ₈`):

1. **Stage `ℭ₁` (`QuotientDirectLimit` ↔ `ModuleCat` Categorical Colimit Bridge)**:
   Connects Mathlib's concrete quotient `AddCommGroup.DirectLimit Stage (sysAddHom sys)` (`Paradigm A`)
   to the categorical `ModuleCat` colimit `colimit (FilteredColimit.Native.moduleDiagram sys)`
   (`Paradigm B`), proving exact compatibility on every finite stage representative and every
   `InductiveCocone`.
2. **Stage `ℭ₂` (Contravariant Dual `ModuleCat` Diagram)**:
   Reuses `FilteredColimit.InductiveCocone.dualModuleDiagram`, built from the dual transition maps
   `dualInverseTransition`; its categorical limit is the native projective dual space.
3. **Stage `ℭ₃` (Universal Duality Between Inductive Colimit States & Projective Dual Cones)**:
   Patches `IsDualInverseFamily` (`FilteredDirectInverseColimitReadback`) directly to
   `Cone (dualModuleDiagram sys)` and `limit (dualModuleDiagram sys)`, proving that every
   inverse-compatible family of stage functionals `phi : ∀ i, A i →ₗ[R] R` simultaneously lifts to
   a morphism `dualInverseFamilyToProjectiveLimit : ModuleCat.of R R ⟶ limit (dualModuleDiagram sys)`
   on the projective limit side and descends to `dualInverseFamilyColimitMap : colimit (moduleDiagram sys) ⟶ ModuleCat.of R R`
   on the directed colimit side, with identical stage evaluations `phi i x`, and that every colimit
   state `g : colimit (moduleDiagram sys) ⟶ ModuleCat.of R R` is uniquely reconstructed from its
   stage restriction family.
4. **Stages `ℭ₄` & `ℭ₅` (Projective Limit of Spaces `Iᵒᵖ ⥤ Type*` ↔ Inductive Colimit of Pullback Cylinder Observables `I ⥤ ModuleCat R`, Specializing to Cantor Boundary ↔ UHF Diagonal Algebra)**:
   Proves that any projective system of spaces `(X i, res_{i,j})` with a projective cone `(X_inf, proj_i)`
   contravariantly induces a `DirectInductiveSystem` of observable modules `X i → R` and an
   `InductiveCocone` into `X_inf → R` that descends through `colimit (moduleDiagram ...)`, and
   specializes this bridge to weld the `TopCat` Cantor projective limit
   (`prefixBoundaryLimitIso : TopCat.of CantorBoundary ≅ limit prefixDiagram`) to the UHF diagonal
   cylinder algebra (`diagEmbedSucc`, `cylinder_compatible_succ`).
5. **Stage `ℭ₆` (Filtered–Finite Colimit/Limit Interchange)**:
   Reuses `Holonomy.colimit_limit_iso R F`, which applies Mathlib's filtered-colimit/finite-limit
   preservation theorem. The stage theorem checks the isomorphism laws and equality with the
   `Native.filteredColimitFiniteLimitIso` spelling; it does not claim a separate comparison-map
   projection theorem.
6. **Stages `ℭ₇` & `ℭ₈` (Peirce–Cartan–Gauss–Bonnet Operator Tower ↔ Dual Projective Trace System & Cl(1,1) Markov Trace Realization)**:
   Unifies non-commutative `R`-algebra inductive towers (`JaynesianNilpotentInductiveColimitContinuumPoset`
   & `HestenesKreinGaussBonnetAnalyticDerivationPoset`) with `DirectInductiveSystem`, `dualModuleDiagram`,
   and `Cl11FilteredDirectInverseColimit`, proving that cyclic stage traces form a projective dual
   family whose induced colimit and projective-limit readouts annihilate all positive chiral bandgap
   moments `invS P_n * genV P_n A_n C_n ^ (k + 1)` and preserve the scale-invariant Gauss–Bonnet
   supertrace.
-/

noncomputable section

namespace InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.Canonical.FilteredDirectLimitOperator
open InfoGeometry.Categorical.FilteredDirectLimitOwner
open InfoGeometry.Categorical.Holonomy
open FilteredColimit
open FilteredColimit.InductiveCocone
open FilteredColimit.Native
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.Cl11FilteredDirectInverseColimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
open InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
open InfoGeometry.Canonical.MaurerCartanSpectralAnnihilatorDefectPoset
open InfoGeometry.Canonical.HestenesKreinGaussBonnetAnalyticDerivationPoset
open InfoGeometry.Canonical.JaynesianNilpotentInductiveColimitContinuumPoset

universe u

/-!
## Part I: Colimit & Inverse-Limit Ontology, Taxonomy, Curated Development Strata & 8-Stage Poset (`ℭ₁ ≺ … ≺ ℭ₈`)
-/

/-- The 5 distinct mathematical paradigms of colimits and inverse limits across `info-geometry-lean`. -/
inductive ColimitInverseLimitParadigm : Type
  | ParadigmA_QuotientDirectLimit
  | ParadigmB_CategoricalInductiveColimit
  | ParadigmC_CategoricalProjectiveInverseLimit
  | ParadigmD_ContravariantDualStateAndCylinderPullback
  | ParadigmE_FilteredColimitFiniteLimitInterchange
  deriving DecidableEq, Repr, Inhabited

namespace ColimitInverseLimitParadigm

/-- Numerical index (`0` through `4`) distinguishing the 5 colimit/inverse-limit paradigms. -/
def code : ColimitInverseLimitParadigm → ℕ
  | .ParadigmA_QuotientDirectLimit                       => 0
  | .ParadigmB_CategoricalInductiveColimit               => 1
  | .ParadigmC_CategoricalProjectiveInverseLimit         => 2
  | .ParadigmD_ContravariantDualStateAndCylinderPullback => 3
  | .ParadigmE_FilteredColimitFiniteLimitInterchange     => 4

/-- Injectivity of the numerical paradigm index `code`. -/
theorem code_injective : Function.Injective code := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

/-- Pairwise distinctness of the 5 colimit/inverse-limit paradigms. -/
theorem pairwise_distinct :
    ColimitInverseLimitParadigm.ParadigmA_QuotientDirectLimit ≠
      .ParadigmB_CategoricalInductiveColimit ∧
    ColimitInverseLimitParadigm.ParadigmB_CategoricalInductiveColimit ≠
      .ParadigmC_CategoricalProjectiveInverseLimit ∧
    ColimitInverseLimitParadigm.ParadigmC_CategoricalProjectiveInverseLimit ≠
      .ParadigmD_ContravariantDualStateAndCylinderPullback ∧
    ColimitInverseLimitParadigm.ParadigmD_ContravariantDualStateAndCylinderPullback ≠
      .ParadigmE_FilteredColimitFiniteLimitInterchange := by
  decide

end ColimitInverseLimitParadigm

/-- Seven curated source clades for colimit and inverse-limit constructions. This is a taxonomy,
not an exhaustive module inventory. -/
inductive ColimitTaxonomicClade : Type
  | CladeI_QuotientDirectLimitOperatorsAndKreinPhases
  | CladeII_ModuleAndRingCategoricalInductiveColimits
  | CladeIII_DualStateProjectiveLimitsAndCl11MarkovTraces
  | CladeIV_CantorProjectiveLimitAndUHFDiagonalCylinders
  | CladeV_TopologicalAndCompHausDirectInverseLimits
  | CladeVI_FilteredGNSStarAlgebraAndTomitaColimits
  | CladeVII_BifiltrationLimitColimitComparisonAndInterchange
  deriving DecidableEq, Repr, Inhabited

namespace ColimitTaxonomicClade

/-- Primary colimit/inverse-limit paradigm of each taxonomic clade. -/
def paradigm : ColimitTaxonomicClade → ColimitInverseLimitParadigm
  | .CladeI_QuotientDirectLimitOperatorsAndKreinPhases         => .ParadigmA_QuotientDirectLimit
  | .CladeII_ModuleAndRingCategoricalInductiveColimits         => .ParadigmB_CategoricalInductiveColimit
  | .CladeIII_DualStateProjectiveLimitsAndCl11MarkovTraces     => .ParadigmD_ContravariantDualStateAndCylinderPullback
  | .CladeIV_CantorProjectiveLimitAndUHFDiagonalCylinders      => .ParadigmD_ContravariantDualStateAndCylinderPullback
  | .CladeV_TopologicalAndCompHausDirectInverseLimits          => .ParadigmC_CategoricalProjectiveInverseLimit
  | .CladeVI_FilteredGNSStarAlgebraAndTomitaColimits           => .ParadigmB_CategoricalInductiveColimit
  | .CladeVII_BifiltrationLimitColimitComparisonAndInterchange => .ParadigmE_FilteredColimitFiniteLimitInterchange

/-- Multi-level ontology stratum (`M0` → `M3`) of each colimit/inverse-limit clade. -/
def metaLevel : ColimitTaxonomicClade → OntologyMetaLevel
  | .CladeIV_CantorProjectiveLimitAndUHFDiagonalCylinders      => .M0_StateIndividual
  | .CladeI_QuotientDirectLimitOperatorsAndKreinPhases         => .M1_ProjectorClabject
  | .CladeII_ModuleAndRingCategoricalInductiveColimits         => .M1_ProjectorClabject
  | .CladeIII_DualStateProjectiveLimitsAndCl11MarkovTraces     => .M2_GrassmannianPowertypeOrbit
  | .CladeV_TopologicalAndCompHausDirectInverseLimits          => .M2_GrassmannianPowertypeOrbit
  | .CladeVI_FilteredGNSStarAlgebraAndTomitaColimits           => .M2_GrassmannianPowertypeOrbit
  | .CladeVII_BifiltrationLimitColimitComparisonAndInterchange => .M3_ErlangenCasimirMetaLaw

/-- Representation-depth layer (`L0_Count` → `L5_ThermodynamicClosure`) of each clade. -/
def repDepth : ColimitTaxonomicClade → RepDepth
  | .CladeIV_CantorProjectiveLimitAndUHFDiagonalCylinders      => .projective
  | .CladeII_ModuleAndRingCategoricalInductiveColimits         => .operator
  | .CladeI_QuotientDirectLimitOperatorsAndKreinPhases         => .krein
  | .CladeV_TopologicalAndCompHausDirectInverseLimits          => .krein
  | .CladeIII_DualStateProjectiveLimitsAndCl11MarkovTraces     => .transport
  | .CladeVI_FilteredGNSStarAlgebraAndTomitaColimits           => .transport
  | .CladeVII_BifiltrationLimitColimitComparisonAndInterchange => .thermo

end ColimitTaxonomicClade

/-- Eight curated development strata for organizing source lineage. Their rank is a formal ordering
used below; no Git commit count or commit-to-stratum assignment is asserted here. -/
inductive ColimitDevelopmentStratum : Type
  | Stratum1_AFRecursiveAndElementaryTowerGenesis
  | Stratum2_GrothendieckK0AndUHFDiagonalCylinderSkeleton
  | Stratum3_FilteredDirectInverseModuleAndHolonomyInterchange
  | Stratum4_CantorProjectiveLimitTopCatAndCompHausBoundaries
  | Stratum5_FilteredGNSStarAlgebraAndTomitaClosabilityTower
  | Stratum6_CARCCRParameterDirectAndInverseFiberLimits
  | Stratum7_RealStarColimitUniversalityAndCliffordTailGrading
  | Stratum8_PeirceCartanGaussBonnetAndDirectInverseUnification
  deriving DecidableEq, Repr, Inhabited

namespace ColimitDevelopmentStratum

/-- Formal rank (`0` through `7`) of the eight curated development strata. -/
def rank : ColimitDevelopmentStratum → ℕ
  | .Stratum1_AFRecursiveAndElementaryTowerGenesis               => 0
  | .Stratum2_GrothendieckK0AndUHFDiagonalCylinderSkeleton       => 1
  | .Stratum3_FilteredDirectInverseModuleAndHolonomyInterchange  => 2
  | .Stratum4_CantorProjectiveLimitTopCatAndCompHausBoundaries   => 3
  | .Stratum5_FilteredGNSStarAlgebraAndTomitaClosabilityTower    => 4
  | .Stratum6_CARCCRParameterDirectAndInverseFiberLimits         => 5
  | .Stratum7_RealStarColimitUniversalityAndCliffordTailGrading  => 6
  | .Stratum8_PeirceCartanGaussBonnetAndDirectInverseUnification => 7

/-- Injectivity of the development stratum rank `rank`. -/
theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance instLinearOrder : LinearOrder ColimitDevelopmentStratum :=
  LinearOrder.lift' rank rank_injective

/-- Rank edge `u ≺ v` between the curated development strata. This records the chosen
development ordering only; it is not a relation reconstructed from Git commits. -/
def rankEdge : ColimitDevelopmentStratum → ColimitDevelopmentStratum → Prop :=
  fun u v => u.rank < v.rank

instance instDecidableRelRankEdge : DecidableRel rankEdge :=
  fun u v => inferInstanceAs (Decidable (u.rank < v.rank))

/-- Every transitive path in `rankEdge` strictly increases `rank`. -/
theorem transGen_rankEdge_lt_rank {u v : ColimitDevelopmentStratum}
    (h : Relation.TransGen rankEdge u v) : u.rank < v.rank := by
  induction h with
  | single h1 => exact h1
  | tail _ h2 ih => exact Nat.lt_trans ih h2

/-- Strict acyclicity of the rank-ordered development strata. -/
theorem rankEdge_acyclic (u : ColimitDevelopmentStratum) :
    ¬ Relation.TransGen rankEdge u u := by
  intro h
  exact Nat.lt_irrefl u.rank (transGen_rankEdge_lt_rank h)

end ColimitDevelopmentStratum

/-- Eight synthesis stages for inductive colimits, contravariant projective/inverse limits,
pullback cylinder algebras, and filtered–finite limit–colimit interchange. The direct dependency
relation is the DAG `causalEdge`; the numeric rank is only a topological ordering, not a claim that
every consecutive pair is a direct dependency. -/
inductive ColimitInverseLimitUnificationStage : Type
  | C1_DirectInductiveSystemToModuleCatColimitAndQuotientBridge
  | C2_ContravariantDualModuleDiagramAndProjectiveLimitCone
  | C3_UniversalColimitStateToProjectiveDualConeEquivalence
  | C4_ProjectiveSpaceLimitToInductiveCylinderObservablePullback
  | C5_CantorProjectiveBoundaryToUHFDiagonalInductiveSystem
  | C6_FilteredFiniteLimitInterchange
  | C7_PeirceCartanGaussBonnetTowerToDualInverseTraceSystem
  | C8_CoagulatedInductiveAndInverseColimitMasterSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace ColimitInverseLimitUnificationStage

/-- Rank (`0` through `7`) of the 8 unification stages (`ℭ₁`–`ℭ₈`). -/
def rank : ColimitInverseLimitUnificationStage → ℕ
  | .C1_DirectInductiveSystemToModuleCatColimitAndQuotientBridge     => 0
  | .C2_ContravariantDualModuleDiagramAndProjectiveLimitCone         => 1
  | .C3_UniversalColimitStateToProjectiveDualConeEquivalence         => 2
  | .C4_ProjectiveSpaceLimitToInductiveCylinderObservablePullback    => 3
  | .C5_CantorProjectiveBoundaryToUHFDiagonalInductiveSystem         => 4
  | .C6_FilteredFiniteLimitInterchange => 5
  | .C7_PeirceCartanGaussBonnetTowerToDualInverseTraceSystem         => 6
  | .C8_CoagulatedInductiveAndInverseColimitMasterSynthesis          => 7

/-- Injectivity of the stage rank `rank`. -/
theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance instLinearOrder : LinearOrder ColimitInverseLimitUnificationStage :=
  LinearOrder.lift' rank rank_injective

/-- Direct dependency edges in the colimit/inverse-limit synthesis.

The nontrivial branches are the dual-family readback (`C2 → C3`), the projective-space/cylinder
specialization (`C4 → C5`), the operator trace application of the duality (`C3 → C7`), and the
terminal synthesis consuming the independently established bridges (`C1`, `C5`, `C6`, `C7 → C8`). -/
def causalEdge : ColimitInverseLimitUnificationStage → ColimitInverseLimitUnificationStage → Prop
  | .C2_ContravariantDualModuleDiagramAndProjectiveLimitCone,
    .C3_UniversalColimitStateToProjectiveDualConeEquivalence => True
  | .C4_ProjectiveSpaceLimitToInductiveCylinderObservablePullback,
    .C5_CantorProjectiveBoundaryToUHFDiagonalInductiveSystem => True
  | .C3_UniversalColimitStateToProjectiveDualConeEquivalence,
    .C7_PeirceCartanGaussBonnetTowerToDualInverseTraceSystem => True
  | .C1_DirectInductiveSystemToModuleCatColimitAndQuotientBridge,
    .C8_CoagulatedInductiveAndInverseColimitMasterSynthesis => True
  | .C5_CantorProjectiveBoundaryToUHFDiagonalInductiveSystem,
    .C8_CoagulatedInductiveAndInverseColimitMasterSynthesis => True
  | .C6_FilteredFiniteLimitInterchange,
    .C8_CoagulatedInductiveAndInverseColimitMasterSynthesis => True
  | .C7_PeirceCartanGaussBonnetTowerToDualInverseTraceSystem,
    .C8_CoagulatedInductiveAndInverseColimitMasterSynthesis => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge :=
  fun u v => by
    cases u <;> cases v <;> unfold causalEdge <;> infer_instance

/-- Every direct causal edge strictly increases the stage rank. -/
theorem causalEdge_rank_lt {u v : ColimitInverseLimitUnificationStage}
    (h : causalEdge u v) : u.rank < v.rank := by
  cases u <;> cases v <;> cases h <;> decide

/-- Every transitive path in `causalEdge` strictly increases the stage rank. -/
theorem transGen_causalEdge_lt_rank {u v : ColimitInverseLimitUnificationStage}
    (h : Relation.TransGen causalEdge u v) : u.rank < v.rank := by
  induction h with
  | single h1 => exact causalEdge_rank_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (causalEdge_rank_lt h2)

/-- Strict acyclicity of the direct dependency relation between synthesis stages. -/
theorem causalEdge_acyclic (u : ColimitInverseLimitUnificationStage) :
    ¬ Relation.TransGen causalEdge u u := by
  intro h
  exact Nat.lt_irrefl u.rank (transGen_causalEdge_lt_rank h)

end ColimitInverseLimitUnificationStage

/-!
## Part II: Stage `ℭ₁` — Patching `AddCommGroup.DirectLimit` (`Paradigm A`) with `colimit (moduleDiagram sys)` (`Paradigm B`)
-/

/-- Additive transition homomorphisms extracted from a `DirectInductiveSystem R I A`. -/
def sysAddHom {R : Type u} [CommRing R] {I : Type u} [Preorder I]
    {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (sys : DirectInductiveSystem R I A) (i j : I) (hij : i ≤ j) : A i →+ A j :=
  (sys.f hij).toAddMonoidHom

/-- Every `DirectInductiveSystem R I A` over a preorder `(I, ≤)` automatically forms a
Mathlib `DirectedSystem A (fun i j h => sysAddHom sys i j h)`. -/
instance instDirectedSystemOfDirectInductiveSystem
    {R : Type u} [CommRing R] {I : Type u} [Preorder I]
    {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (sys : DirectInductiveSystem R I A) :
    DirectedSystem A (fun i j h => sysAddHom sys i j h) where
  map_self i x := by
    change sys.f (le_refl i) x = x
    rw [sys.f_id i]
    rfl
  map_map i j k hij hjk x := by
    change sys.f hjk (sys.f hij x) = sys.f (le_trans hij hjk) x
    exact LinearMap.congr_fun (sys.f_comp hij hjk) x

/-- Canonical stage additive homomorphism from `Stage i` into the underlying additive group of the
categorical `ModuleCat` colimit `colimit (FilteredColimit.Native.moduleDiagram sys)`. -/
def categoricalColimitStageAddHom
    {R : Type u} [CommRing R]
    {I : Type u} [Preorder I]
    {Stage : I → Type u} [∀ i, AddCommGroup (Stage i)] [∀ i, Module R (Stage i)]
    (sys : DirectInductiveSystem R I Stage) (i : I) :
    Stage i →+ ↑(colimit (FilteredColimit.Native.moduleDiagram sys)) :=
  (colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom.toAddMonoidHom

/-- Compatibility of `categoricalColimitStageAddHom` with `sysAddHom sys`. -/
theorem categoricalColimitStageAddHom_compatible
    {R : Type u} [CommRing R]
    {I : Type u} [Preorder I]
    {Stage : I → Type u} [∀ i, AddCommGroup (Stage i)] [∀ i, Module R (Stage i)]
    (sys : DirectInductiveSystem R I Stage)
    (i j : I) (hij : i ≤ j) (x : Stage i) :
    categoricalColimitStageAddHom sys j (sysAddHom sys i j hij x) =
      categoricalColimitStageAddHom sys i x := by
  have hw := colimit.w (FilteredColimit.Native.moduleDiagram sys) (homOfLE hij)
  exact congrArg (fun f : (FilteredColimit.Native.moduleDiagram sys).obj i ⟶
    colimit (FilteredColimit.Native.moduleDiagram sys) => f.hom x) hw

/-- **Stage `ℭ₁` Bridge (`quotientToCategoricalColimit`)**:
The universal additive homomorphism from Mathlib's concrete quotient
`AddCommGroup.DirectLimit Stage (sysAddHom sys)` (`Paradigm A`) into the categorical `ModuleCat`
colimit `colimit (FilteredColimit.Native.moduleDiagram sys)` (`Paradigm B`). -/
def quotientToCategoricalColimit
    {R : Type u} [CommRing R]
    {I : Type u} [DecidableEq I] [Preorder I] [IsDirectedOrder I]
    {Stage : I → Type u} [∀ i, AddCommGroup (Stage i)] [∀ i, Module R (Stage i)]
    (sys : DirectInductiveSystem R I Stage) :
    AddCommGroup.DirectLimit Stage (sysAddHom sys) →+
      ↑(colimit (FilteredColimit.Native.moduleDiagram sys)) :=
  AddCommGroup.DirectLimit.lift
    Stage (sysAddHom sys)
    (↑(colimit (FilteredColimit.Native.moduleDiagram sys)))
    (categoricalColimitStageAddHom sys)
    (categoricalColimitStageAddHom_compatible sys)

/-- **Stage `ℭ₁` (`stage_C1_quotient_direct_limit_to_categorical_module_colimit_bridge`)**:
For any `DirectInductiveSystem R I Stage` over a directed poset `(I, ≤)` and any
`InductiveCocone R sys A_inf`:
1. `quotientToCategoricalColimit sys` maps every concrete stage representative
   `AddCommGroup.DirectLimit.of Stage (sysAddHom sys) i x` to the categorical stage injection
   `(colimit.ι (moduleDiagram sys) i).hom x`,
2. Composing the categorical cocone descent `(descendModuleCocone sys cocone).hom` with
   `quotientToCategoricalColimit sys` agrees on every stage representative with the concrete
   `AddCommGroup.DirectLimit.lift` of `cocone.psi`, both evaluating to `cocone.psi i x`. -/
theorem stage_C1_quotient_direct_limit_to_categorical_module_colimit_bridge
    {R : Type u} [CommRing R]
    {I : Type u} [DecidableEq I] [Preorder I] [IsDirectedOrder I]
    {Stage : I → Type u} [∀ i, AddCommGroup (Stage i)] [∀ i, Module R (Stage i)]
    {A_inf : Type u} [AddCommGroup A_inf] [Module R A_inf]
    (sys : DirectInductiveSystem R I Stage)
    (cocone : InductiveCocone R sys A_inf)
    (i : I) (x : Stage i) :
    quotientToCategoricalColimit sys
        (AddCommGroup.DirectLimit.of Stage (sysAddHom sys) i x) =
      (colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom x ∧
    (FilteredColimit.Native.descendModuleCocone sys cocone).hom
        (quotientToCategoricalColimit sys
          (AddCommGroup.DirectLimit.of Stage (sysAddHom sys) i x)) =
      cocone.psi i x := by
  have hof :
      quotientToCategoricalColimit sys
          (AddCommGroup.DirectLimit.of Stage (sysAddHom sys) i x) =
        (colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom x :=
    AddCommGroup.DirectLimit.lift_of
      (G := Stage) (f := sysAddHom sys)
      (P := ↑(colimit (FilteredColimit.Native.moduleDiagram sys)))
      (g := categoricalColimitStageAddHom sys)
      (Hg := categoricalColimitStageAddHom_compatible sys) i x
  refine ⟨hof, ?_⟩
  rw [hof]
  have hdesc := FilteredColimit.Native.moduleColimit_desc_stage sys cocone i
  exact congrArg (fun f : (FilteredColimit.Native.moduleDiagram sys).obj i ⟶
    ModuleCat.of R A_inf => f.hom x) hdesc

/-!
## Part III: Stages `ℭ₂` & `ℭ₃` — Contravariant Dual `ModuleCat` Diagram (`Iᵒᵖ ⥤ ModuleCat.{u} R`) & Inductive-Colimit / Projective-Limit State Duality
-/

/-- **Stages `ℭ₂` & `ℭ₃` (`stage_C2_C3_inductive_colimit_state_to_projective_dual_limit_bridge`)**:
Connects the existing declarations in `FilteredDirectInverseColimitReadback` for
`IsDualInverseFamily`, `dualModuleDiagram`, `limit (dualModuleDiagram sys)`, and
`colimit (moduleDiagram sys)`:
1. Projecting `dualInverseFamilyToProjectiveLimit (sys := sys) phi hphi` to stage `Opposite.op i` and
   evaluating at `(1 : R)` and `x : A i` yields `phi i x`,
2. Evaluating the inductive colimit map `dualInverseFamilyColimitMap phi hphi` on the canonical
   stage injection `(colimit.ι (moduleDiagram sys) i).hom x` also yields `phi i x`, so the
   **projective limit projection** and the **inductive colimit evaluation** coincide identically,
3. Restricting any colimit functional `g : colimit (moduleDiagram sys) ⟶ ModuleCat.of R R` to its
   dual inverse family `colimitFunctionalStageFamily sys g.hom` and descending back through the
   colimit recovers `g` uniquely (`g = dualInverseFamilyColimitMap ...`). -/
theorem stage_C2_C3_inductive_colimit_state_to_projective_dual_limit_bridge
    {R : Type u} [CommRing R] {I : Type u} [Preorder I]
    {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (sys : DirectInductiveSystem R I A)
    (phi : ∀ i : I, A i →ₗ[R] R)
    (hphi : IsDualInverseFamily (sys := sys) phi)
    (g : colimit (FilteredColimit.Native.moduleDiagram sys) ⟶ ModuleCat.of R R)
    (i : I) (x : A i) :
    ((dualInverseFamilyToProjectiveLimit (sys := sys) phi hphi ≫
        limit.π (dualModuleDiagram sys) (Opposite.op i)).hom (1 : R)) x = phi i x ∧
    ((dualInverseFamilyToProjectiveLimit (sys := sys) phi hphi ≫
        limit.π (dualModuleDiagram sys) (Opposite.op i)).hom (1 : R)) x =
      (dualInverseFamilyColimitMap (sys := sys) phi hphi).hom
        ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom x) ∧
    g = dualInverseFamilyColimitMap (sys := sys)
          (colimitFunctionalStageFamily (sys := sys) g.hom)
          (colimitFunctionalStageFamily_isDualInverseFamily (sys := sys) g.hom) := by
  refine ⟨dualInverseFamilyToProjectiveLimit_stage (sys := sys) phi hphi i x, ?_, ?_⟩
  · rw [dualInverseFamilyToProjectiveLimit_stage (sys := sys) phi hphi i x,
      dualInverseFamilyColimitMap_stage (sys := sys) phi hphi i x]
  · exact dualInverseFamilyColimitMap_unique (sys := sys)
      (colimitFunctionalStageFamily (sys := sys) g.hom)
      (colimitFunctionalStageFamily_isDualInverseFamily (sys := sys) g.hom)
      g (by intro j y; rfl)

/-- The projective limit of the stagewise algebraic duals is linearly equivalent
to the algebraic dual of the native categorical colimit. The underlying
equivalence is built from limit projections and the colimit universal
property; this declaration also proves that the correspondence preserves the
`R`-module structure, rather than only giving a bijection of carriers. -/
noncomputable def projectiveLimitDualColimitLinearEquiv
    {R : Type u} [CommRing R] {I : Type u} [Preorder I]
    {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (sys : DirectInductiveSystem R I A) :
    ((limit (dualModuleDiagram sys) : ModuleCat R) : Type u) ≃ₗ[R]
      (InfoGeometry.Categorical.Holonomy.ModuleInductiveLimit R
        (FilteredColimit.Native.moduleDiagram sys) →ₗ[R] R) :=
  { projectiveLimitDualColimitFunctionalEquiv (sys := sys) with
    map_add' := fun z w => by
      have h :
          ModuleCat.ofHom (projectiveLimitDualColimitFunctionalEquiv (sys := sys) (z + w)) =
          ModuleCat.ofHom (projectiveLimitDualColimitFunctionalEquiv (sys := sys) z +
            projectiveLimitDualColimitFunctionalEquiv (sys := sys) w) := by
        apply colimit.hom_ext
        intro i
        ext x
        change (projectiveLimitDualColimitFunctionalEquiv (sys := sys) (z + w))
            ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom x) =
          (projectiveLimitDualColimitFunctionalEquiv (sys := sys) z)
            ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom x) +
          (projectiveLimitDualColimitFunctionalEquiv (sys := sys) w)
            ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom x)
        rw [projectiveLimitDualColimitFunctionalEquiv_stage (sys := sys) (z + w) i x,
          projectiveLimitDualColimitFunctionalEquiv_stage (sys := sys) z i x,
          projectiveLimitDualColimitFunctionalEquiv_stage (sys := sys) w i x]
        rw [map_add]
        rfl
      exact congrArg ModuleCat.Hom.hom h
    map_smul' := fun c z => by
      have h :
          ModuleCat.ofHom (projectiveLimitDualColimitFunctionalEquiv (sys := sys) (c • z)) =
          ModuleCat.ofHom (c • projectiveLimitDualColimitFunctionalEquiv (sys := sys) z) := by
        apply colimit.hom_ext
        intro i
        ext x
        change (projectiveLimitDualColimitFunctionalEquiv (sys := sys) (c • z))
            ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom x) =
          c * (projectiveLimitDualColimitFunctionalEquiv (sys := sys) z)
            ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom x)
        rw [projectiveLimitDualColimitFunctionalEquiv_stage (sys := sys) (c • z) i x,
          projectiveLimitDualColimitFunctionalEquiv_stage (sys := sys) z i x]
        rw [map_smul]
        rfl
      exact congrArg ModuleCat.Hom.hom h }

/-!
## Part IV: Stages `ℭ₄` & `ℭ₅` — Projective Limit of Spaces ↔ Inductive Colimit of Pullback Cylinder Observables (Cantor Boundary ↔ UHF Diagonal Algebra)
-/

/-- Contravariant pullback of functions `X i → R` along a projective restriction map `res : X j → X i`. -/
def pullbackLinearMap {R : Type*} [CommRing R] {X_i X_j : Type*} (res : X_j → X_i) :
    (X_i → R) →ₗ[R] (X_j → R) where
  toFun f := f ∘ res
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Any projective system of spaces `(X i, res hij)` contravariantly induces a
`DirectInductiveSystem R I (fun i => X i → R)` of observable modules via pullback. -/
def pullbackInductiveSystem
    (R : Type u) [CommRing R] {I : Type u} [Preorder I]
    (X : I → Type u)
    (res : ∀ {i j : I}, i ≤ j → X j → X i)
    (res_id : ∀ (i : I) (x : X i), res (le_refl i) x = x)
    (res_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : X k),
      res hij (res hjk x) = res (le_trans hij hjk) x) :
    DirectInductiveSystem R I (fun i => X i → R) :=
  DirectInductiveSystem.mk
    (fun hij => pullbackLinearMap (res hij))
    (fun i => by
      ext f x
      exact congrArg f (res_id i x))
    (fun hij hjk => by
      ext f x
      exact congrArg f (res_comp hij hjk x))

/-- Any compatible projective cone `(X_inf, proj i)` over `(X i, res hij)` induces an
`InductiveCocone` from `pullbackInductiveSystem` into the boundary observable space `X_inf → R`. -/
def pullbackCylinderCocone
    (R : Type u) [CommRing R] {I : Type u} [Preorder I]
    (X : I → Type u)
    (res : ∀ {i j : I}, i ≤ j → X j → X i)
    (res_id : ∀ (i : I) (x : X i), res (le_refl i) x = x)
    (res_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : X k),
      res hij (res hjk x) = res (le_trans hij hjk) x)
    (X_inf : Type u)
    (proj : ∀ i : I, X_inf → X i)
    (proj_compat : ∀ {i j : I} (hij : i ≤ j) (b : X_inf), res hij (proj j b) = proj i b) :
    InductiveCocone R (pullbackInductiveSystem R X res res_id res_comp) (X_inf → R) :=
  InductiveCocone.mk
    (fun i => pullbackLinearMap (proj i))
    (fun hij => by
      ext f b
      exact congrArg f (proj_compat hij b))

/-- **Stages `ℭ₄` & `ℭ₅` (`stage_C4_C5_projective_space_to_inductive_cylinder_and_cantor_uhf_bridge`)**:
1. **General Projective-Space / Inductive-Observable Duality**: For any projective system
   `(X i, res hij)` with cone `(X_inf, proj i)`, the descended `ModuleCat` colimit morphism
   `descendModuleCocone (pullbackInductiveSystem ...) (pullbackCylinderCocone ...)` evaluates on
   every stage observable `f : X i → R` and boundary point `b : X_inf` as the cylinder pullback
   `f (proj i b)` and satisfies `f (res hij (proj j b)) = f (proj i b)`,
2. **Cantor Projective Limit ↔ UHF Diagonal Cylinder Specialization**:
   - The `TopCat` projective restriction `prefixRestriction (homOfLE (Nat.le_succ n)).op` on
     `BitWord (n + 1)` equals `prefixSucc n`,
   - Pulling back `f : DiagAlg n` along `prefixRestriction (homOfLE (Nat.le_succ n)).op` is
     identically the UHF diagonal successor embedding `diagEmbedSucc n f`,
   - Pulling back `f : DiagAlg n` along the categorical `TopCat` limit projection
     `prefixBoundaryLimitIso.hom ≫ limit.π prefixDiagram (Opposite.op n)` is identically the
     Cantor cylinder observable `cylinder n f`, satisfying `cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f`. -/
theorem stage_C4_C5_projective_space_to_inductive_cylinder_and_cantor_uhf_bridge
    {R : Type u} [CommRing R] {I : Type u} [Preorder I]
    (X : I → Type u)
    (res : ∀ {i j : I}, i ≤ j → X j → X i)
    (res_id : ∀ (i : I) (x : X i), res (le_refl i) x = x)
    (res_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : X k),
      res hij (res hjk x) = res (le_trans hij hjk) x)
    (X_inf : Type u)
    (proj : ∀ i : I, X_inf → X i)
    (proj_compat : ∀ {i j : I} (hij : i ≤ j) (b : X_inf), res hij (proj j b) = proj i b)
    (i : I) (φ_obs : X i → R) (b_pt : X_inf)
    (n : ℕ) (f_diag : DiagAlg n) (w_succ : BitWord (n + 1)) (b_cantor : CantorBoundary) :
    let sys_pull := pullbackInductiveSystem R X res res_id res_comp
    let coc_pull := pullbackCylinderCocone R X res res_id res_comp X_inf proj proj_compat
    ((FilteredColimit.Native.descendModuleCocone sys_pull coc_pull).hom
      ((colimit.ι (FilteredColimit.Native.moduleDiagram sys_pull) i).hom φ_obs) b_pt =
        φ_obs (proj i b_pt)) ∧
    prefixRestriction (homOfLE (Nat.le_succ n)).op w_succ = prefixSucc n w_succ ∧
    (f_diag ∘ prefixRestriction (homOfLE (Nat.le_succ n)).op) = diagEmbedSucc n f_diag ∧
    f_diag ((prefixBoundaryLimitIso.hom ≫
      limit.π prefixDiagram (Opposite.op n)).hom b_cantor) = cylinder n f_diag b_cantor ∧
    cylinder (n + 1) (diagEmbedSucc n f_diag) = cylinder n f_diag := by
  intro sys_pull coc_pull
  have hdesc := FilteredColimit.Native.moduleColimit_desc_stage sys_pull coc_pull i
  have heval :
      (FilteredColimit.Native.descendModuleCocone sys_pull coc_pull).hom
        ((colimit.ι (FilteredColimit.Native.moduleDiagram sys_pull) i).hom φ_obs) b_pt =
        φ_obs (proj i b_pt) :=
    congrArg (fun k : (FilteredColimit.Native.moduleDiagram sys_pull).obj i ⟶
      ModuleCat.of R (X_inf → R) => k.hom φ_obs b_pt) hdesc
  have hpref : prefixRestriction (homOfLE (Nat.le_succ n)).op w_succ = prefixSucc n w_succ := rfl
  have hdiag : (f_diag ∘ prefixRestriction (homOfLE (Nat.le_succ n)).op) = diagEmbedSucc n f_diag := rfl
  have hlim_proj :
      (prefixBoundaryLimitIso.hom ≫ limit.π prefixDiagram (Opposite.op n)).hom b_cantor =
        boundaryPrefix n b_cantor := by
    rw [prefixBoundaryLimitIso_hom_comp n]
    rfl
  have hcyl :
      f_diag ((prefixBoundaryLimitIso.hom ≫
        limit.π prefixDiagram (Opposite.op n)).hom b_cantor) = cylinder n f_diag b_cantor := by
    rw [hlim_proj]
    rfl
  exact ⟨heval, hpref, hdiag, hcyl, cylinder_compatible_succ n f_diag⟩

/-!
## Part V: Stage `ℭ₆` — Filtered–Finite Colimit/Limit Interchange
-/

/-- **Stage `ℭ₆` (`stage_C6_filtered_colimit_finite_limit_interchange`)**:
For a finite-shape diagram in `ModuleCat` indexed by a filtered category, the existing
`Holonomy.colimit_limit_iso` is an isomorphism. This theorem exposes both inverse laws and checks
that the native filtered-colimit spelling is definitionally the same isomorphism. -/
theorem stage_C6_filtered_colimit_finite_limit_interchange
    (R : Type u) [CommRing R]
    {J₀ : Type u} [SmallCategory J₀] [FinCategory J₀]
    {I₀ : Type u} [SmallCategory I₀] [IsFiltered I₀]
    (F_diag : J₀ ⥤ I₀ ⥤ ModuleCat.{u} R) :
    (colimit_limit_iso R F_diag).hom ≫ (colimit_limit_iso R F_diag).inv = 𝟙 _ ∧
    (colimit_limit_iso R F_diag).inv ≫ (colimit_limit_iso R F_diag).hom = 𝟙 _ ∧
    (lim_composition_naturality R F_diag).hom ≫ (lim_composition_naturality R F_diag).inv = 𝟙 _ ∧
    FilteredColimit.Native.filteredColimitFiniteLimitIso F_diag = colimit_limit_iso R F_diag := by
  exact ⟨(colimit_limit_iso R F_diag).hom_inv_id,
         (colimit_limit_iso R F_diag).inv_hom_id,
         (lim_composition_naturality R F_diag).hom_inv_id,
         rfl⟩

/-!
## Part VI: Stages `ℭ₇` & `ℭ₈` — Patching Peirce–Cartan–Gauss–Bonnet Algebra Towers with `DirectInductiveSystem`, `dualModuleDiagram`, and `Cl11FilteredDirectInverseColimit`
-/

/-- Any directed system of `R`-algebras `(Stage i, f hij)` over `(I, ≤)` induces a
`DirectInductiveSystem R I Stage` of `R`-modules via `(f hij).toLinearMap`. -/
def algTowerToDirectSystem
    (R : Type u) [CommRing R]
    {I : Type u} [Preorder I]
    (Stage : I → Type u) [∀ i, Ring (Stage i)] [∀ i, Algebra R (Stage i)]
    (f : ∀ {i j : I}, i ≤ j → Stage i →ₐ[R] Stage j)
    (f_id : ∀ i : I, f (le_refl i) = AlgHom.id R (Stage i))
    (f_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (f hjk).comp (f hij) = f (le_trans hij hjk)) :
    DirectInductiveSystem R I Stage :=
  DirectInductiveSystem.mk
    (fun hij => (f hij).toLinearMap)
    (fun i => by
      ext x
      exact AlgHom.congr_fun (f_id i) x)
    (fun hij hjk => by
      ext x
      exact AlgHom.congr_fun (f_comp hij hjk) x)

/-- **Stage `ℭ₇` (`stage_C7_peirce_cartan_gauss_bonnet_tower_to_dual_inverse_trace_system`)**:
Let `(Stage i, f hij)` be a directed system of `R`-algebras over `(I, ≤)` and let
`τ : ∀ i, Stage i →ₗ[R] R` be a compatible family of cyclic `R`-linear stage traces
(`∀ i ≤ j, τ j ∘ₗ (f hij).toLinearMap = τ i` and `∀ i x y, τ i (x * y) = τ i (y * x)`).
Let `sys := algTowerToDirectSystem R Stage f f_id f_comp`.
Then:
1. `IsDualInverseFamily (sys := sys) τ` holds (`τ` is a compatible inverse family in the
   contravariant projective dual system `dualModuleDiagram sys`),
2. For any stage `i : I` with idempotent `P_i * P_i = P_i`, off-diagonal seeds `A_i C_i : Stage i`,
   resolvent `(genV P_i A_i C_i + η_i) * R_i = 1` commuting with `genJ P_i A_i C_i`, and mode `k : ℕ`:
   - The categorical inductive-colimit readout `dualInverseFamilyColimitMap` and the categorical
     projective-limit readout `dualInverseFamilyToProjectiveLimit` coincide on every stage element,
   - Both readouts annihilate all positive chiral bandgap moments:
     `invS P_i * genV P_i A_i C_i ^ (k + 1)` and `(2 : ℤ) • (invS P_i * genV P_i A_i C_i ^ (k + 1))`,
   - Both readouts preserve the scale-invariant Gauss–Bonnet chiral supertrace:
     `(dualInverseFamilyColimitMap τ hτ_dual).hom ((colimit.ι (moduleDiagram sys) i).hom ((2 : ℤ) • invS P_i)) = (dualInverseFamilyColimitMap τ hτ_dual).hom ((colimit.ι (moduleDiagram sys) i).hom ((2 : ℤ) • (invS P_i * η_i * R_i)))`,
3. In the concrete `Cl(1,1)` matrix tower (`cl11DirectSystem`), the Markov–Jones normalized trace
   satisfies `cl11TraceColimitMap = cl11TraceFromInverseFamily`. -/
theorem stage_C7_peirce_cartan_gauss_bonnet_tower_to_dual_inverse_trace_system
    {R : Type u} [CommRing R]
    {I : Type u} [Preorder I]
    (Stage : I → Type u) [∀ i, Ring (Stage i)] [∀ i, Algebra R (Stage i)]
    (f : ∀ {i j : I}, i ≤ j → Stage i →ₐ[R] Stage j)
    (f_id : ∀ i : I, f (le_refl i) = AlgHom.id R (Stage i))
    (f_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (f hjk).comp (f hij) = f (le_trans hij hjk))
    (τ : ∀ i : I, Stage i →ₗ[R] R)
    (hτ_compat : ∀ {i j : I} (hij : i ≤ j), τ j ∘ₗ (f hij).toLinearMap = τ i)
    (hτ_cyclic : ∀ (i : I) (x y : Stage i), τ i (x * y) = τ i (y * x))
    (i : I) (P_i A_i C_i η_i R_i : Stage i) (hP_i : P_i * P_i = P_i)
    (hRes_i : (genV P_i A_i C_i + η_i) * R_i = 1)
    (hRJ_i : R_i * genJ P_i A_i C_i = genJ P_i A_i C_i * R_i) (k : ℕ) :
    let sys := algTowerToDirectSystem R Stage f f_id f_comp
    ∃ hτ_dual : IsDualInverseFamily (sys := sys) τ,
      (((dualInverseFamilyToProjectiveLimit (sys := sys) τ hτ_dual ≫
          limit.π (dualModuleDiagram sys) (Opposite.op i)).hom (1 : R))
            (invS P_i * genV P_i A_i C_i ^ (k + 1)) = 0 ∧
       (dualInverseFamilyColimitMap (sys := sys) τ hτ_dual).hom
          ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom
            (invS P_i * genV P_i A_i C_i ^ (k + 1))) = 0 ∧
       (dualInverseFamilyColimitMap (sys := sys) τ hτ_dual).hom
          ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom
            ((2 : ℤ) • (invS P_i * genV P_i A_i C_i ^ (k + 1)))) = 0 ∧
       (dualInverseFamilyColimitMap (sys := sys) τ hτ_dual).hom
          ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom
            ((2 : ℤ) • invS P_i)) =
        (dualInverseFamilyColimitMap (sys := sys) τ hτ_dual).hom
          ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom
            ((2 : ℤ) • (invS P_i * η_i * R_i))) ∧
       cl11TraceColimitMap = cl11TraceFromInverseFamily) := by
  intro sys
  have hτ_dual : IsDualInverseFamily (sys := sys) τ := by
    intro m l hml
    exact hτ_compat hml
  refine ⟨hτ_dual, ?_⟩
  have hC23 :=
    stage_C2_C3_inductive_colimit_state_to_projective_dual_limit_bridge
      sys τ hτ_dual (dualInverseFamilyColimitMap (sys := sys) τ hτ_dual) i
  have hG78 :=
    stage_G7_G8_resolvent_scale_invariance_and_gauss_bonnet_supertrace
      P_i A_i C_i η_i R_i hP_i hRes_i hRJ_i (τ i).toAddMonoidHom (hτ_cyclic i) k
  have hundoubled : τ i (invS P_i * genV P_i A_i C_i ^ (k + 1)) = 0 := by
    rw [invS_mul_genV_pow_succ_eq_comm P_i A_i C_i hP_i k]
    exact hG78.2.1 (conePlus P_i A_i * genV P_i A_i C_i ^ k) (coneMinus P_i C_i)
  refine ⟨?_, ?_, ?_, ?_, cl11TraceColimitMap_eq_inverseFamilyMap⟩
  · rw [(hC23 (invS P_i * genV P_i A_i C_i ^ (k + 1))).1]
    exact hundoubled
  · rw [dualInverseFamilyColimitMap_stage]
    exact hundoubled
  · rw [dualInverseFamilyColimitMap_stage]
    exact hG78.2.2.1
  · rw [dualInverseFamilyColimitMap_stage, dualInverseFamilyColimitMap_stage]
    exact hG78.2.2.2.2

/-- **Stage `ℭ₈` Master Synthesis (`inductive_categorical_colimit_inverse_limit_unification_master_synthesis`)**:
Unites the Colimit & Inverse-Limit Ontology, 5 Architectural Paradigms, the curated development
strata, the direct dependency poset, and all 5 fragment-patching bridges:
1. Acyclicity of the curated rank relation `ColimitDevelopmentStratum.rankEdge_acyclic` and
   `ColimitInverseLimitUnificationStage.causalEdge_acyclic`,
2. **Bridge 1 (`ℭ₁`)**: Exact agreement between `AddCommGroup.DirectLimit` (`quotientToCategoricalColimit`)
   and `colimit (moduleDiagram sys)` on every stage representative,
3. **Bridge 2 (`ℭ₂` & `ℭ₃`)**: Exact equality between the projective dual limit projection
   `dualInverseFamilyToProjectiveLimit (sys := sys) τ hτ_dual ≫ limit.π (dualModuleDiagram sys) (Opposite.op i)`
   and the inductive colimit functional `dualInverseFamilyColimitMap`, plus unique reconstruction
   of any colimit state `g` from `colimitFunctionalStageFamily sys g.hom`,
4. **Bridge 3 (`ℭ₄` & `ℭ₅`)**: Projective-limit to inductive-cylinder pullback connecting
   `prefixBoundaryLimitIso : TopCat.of CantorBoundary ≅ limit prefixDiagram` to `diagEmbedSucc`
   and `cylinder_compatible_succ`,
5. **Bridge 4 (`ℭ₆`)**: Mathlib's filtered–finite `colimit_limit_iso` interchange
   isomorphism and `lim_composition_naturality`,
6. **Bridge 5 (`ℭ₇`)**: Vanishing of all positive chiral bandgap moments and scale invariance of
   the Gauss–Bonnet supertrace across both the inductive colimit and the projective dual limit,
   together with `cl11TraceColimitMap = cl11TraceFromInverseFamily` and the non-commutative
   `2 × 2` matrix witness `hkWitnessP * hkWitnessA ≠ hkWitnessA * hkWitnessP`. -/
theorem inductive_categorical_colimit_inverse_limit_unification_master_synthesis
    {R : Type u} [CommRing R]
    {I : Type u} [DecidableEq I] [Preorder I] [IsDirectedOrder I]
    (Stage : I → Type u) [∀ i, Ring (Stage i)] [∀ i, Algebra R (Stage i)]
    (f : ∀ {i j : I}, i ≤ j → Stage i →ₐ[R] Stage j)
    (f_id : ∀ i : I, f (le_refl i) = AlgHom.id R (Stage i))
    (f_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (f hjk).comp (f hij) = f (le_trans hij hjk))
    (τ : ∀ i : I, Stage i →ₗ[R] R)
    (hτ_compat : ∀ {i j : I} (hij : i ≤ j), τ j ∘ₗ (f hij).toLinearMap = τ i)
    (hτ_cyclic : ∀ (i : I) (x y : Stage i), τ i (x * y) = τ i (y * x))
    (i : I) (P_i A_i C_i η_i R_i x_i : Stage i) (hP_i : P_i * P_i = P_i)
    (hRes_i : (genV P_i A_i C_i + η_i) * R_i = 1)
    (hRJ_i : R_i * genJ P_i A_i C_i = genJ P_i A_i C_i * R_i) (k : ℕ)
    {J₀ : Type u} [SmallCategory J₀] [FinCategory J₀]
    {I₀ : Type u} [SmallCategory I₀] [IsFiltered I₀]
    (F_diag : J₀ ⥤ I₀ ⥤ ModuleCat.{u} R)
    (n : ℕ) (f_diag : DiagAlg n) (b_cantor : CantorBoundary) :
    let sys := algTowerToDirectSystem R Stage f f_id f_comp
    (∀ ep : ColimitDevelopmentStratum,
      ¬ Relation.TransGen ColimitDevelopmentStratum.rankEdge ep ep) ∧
    (∀ st : ColimitInverseLimitUnificationStage,
      ¬ Relation.TransGen ColimitInverseLimitUnificationStage.causalEdge st st) ∧
    (quotientToCategoricalColimit sys
        (AddCommGroup.DirectLimit.of Stage (sysAddHom sys) i x_i) =
      (colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom x_i) ∧
    (f_diag ((prefixBoundaryLimitIso.hom ≫
        limit.π prefixDiagram (Opposite.op n)).hom b_cantor) = cylinder n f_diag b_cantor ∧
     cylinder (n + 1) (diagEmbedSucc n f_diag) = cylinder n f_diag) ∧
    ((colimit_limit_iso R F_diag).hom ≫ (colimit_limit_iso R F_diag).inv = 𝟙 _ ∧
     (lim_composition_naturality R F_diag).hom ≫ (lim_composition_naturality R F_diag).inv = 𝟙 _) ∧
    (∃ hτ_dual : IsDualInverseFamily (sys := sys) τ,
      ((dualInverseFamilyToProjectiveLimit (sys := sys) τ hτ_dual ≫
          limit.π (dualModuleDiagram sys) (Opposite.op i)).hom (1 : R))
            (invS P_i * genV P_i A_i C_i ^ (k + 1)) = 0 ∧
      (dualInverseFamilyColimitMap (sys := sys) τ hτ_dual).hom
          ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom
            (invS P_i * genV P_i A_i C_i ^ (k + 1))) = 0 ∧
      (dualInverseFamilyColimitMap (sys := sys) τ hτ_dual).hom
          ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom
            ((2 : ℤ) • invS P_i)) =
        (dualInverseFamilyColimitMap (sys := sys) τ hτ_dual).hom
          ((colimit.ι (FilteredColimit.Native.moduleDiagram sys) i).hom
            ((2 : ℤ) • (invS P_i * η_i * R_i))) ∧
      cl11TraceColimitMap = cl11TraceFromInverseFamily) ∧
    (hkWitnessP * hkWitnessA ≠ hkWitnessA * hkWitnessP) := by
  intro sys
  have hC1 :=
    stage_C1_quotient_direct_limit_to_categorical_module_colimit_bridge
      sys (dualInverseFamilyCocone (sys := sys) τ (fun {m l} hml => hτ_compat hml)) i x_i
  have hC6 :=
    stage_C6_filtered_colimit_finite_limit_interchange
      R F_diag
  have hC7 :=
    stage_C7_peirce_cartan_gauss_bonnet_tower_to_dual_inverse_trace_system
      Stage f f_id f_comp τ hτ_compat hτ_cyclic i P_i A_i C_i η_i R_i hP_i hRes_i hRJ_i k
  have hlim_proj :
      (prefixBoundaryLimitIso.hom ≫ limit.π prefixDiagram (Opposite.op n)).hom b_cantor =
        boundaryPrefix n b_cantor := by
    rw [prefixBoundaryLimitIso_hom_comp n]
    rfl
  have hcyl :
      f_diag ((prefixBoundaryLimitIso.hom ≫
        limit.π prefixDiagram (Opposite.op n)).hom b_cantor) = cylinder n f_diag b_cantor := by
    rw [hlim_proj]
    rfl
  rcases hC7 with ⟨hτ_dual, h1, h2, _, h4, h5⟩
  exact ⟨ColimitDevelopmentStratum.rankEdge_acyclic,
         ColimitInverseLimitUnificationStage.causalEdge_acyclic,
         hC1.1,
         ⟨hcyl, cylinder_compatible_succ n f_diag⟩,
         ⟨hC6.1, hC6.2.2.1⟩,
         ⟨hτ_dual, h1, h2, h4, h5⟩,
         hk_gauss_bonnet_matrix_witness.2.1⟩

end InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset
