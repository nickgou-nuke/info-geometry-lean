import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Physics.Cl11WittChevalleyBridge
import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Canonical.CanonicalZornCompositionTriality
import InfoGeometry.Canonical.CanonicalZornRealSpin44
import InfoGeometry.Canonical.CanonicalZornOuterTrialityGroup
import InfoGeometry.SuperGrassmannian.MajoranaCARSuperalgebra
import InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule
import InfoGeometry.SuperGrassmannian.CategoricalModuleColimitSato
import InfoGeometry.SuperGrassmannian.SatoColimitTriality
import InfoGeometry.Canonical.MatrixStageInductiveLimit

/-!
# Source-evidenced partial causal poset of noncommutative archetypes

This graph records only implications with owner-source evidence carried by
each edge. Its nodes distinguish the native `CliffordAlgebra q11` Witt
operators, two independent generic split-cell schemas, the tagged Zorn-copy
cycle, the real `(4,4)` spin representation, the recursive split-Clifford
limit, and the complex matrix-stage limit. The last two limits are not
identified. Conditional schema edges retain their actual hypotheses. No
dimension-only, Jones-index, KO-periodicity, or Stiefel–Whitney conclusion is
encoded here.
-/

noncomputable section

namespace InfoGeometry.SuperGrassmannian.CanonicalArchetypePosetV6

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Physics.Cl11WittChevalleyBridge
open CanonicalZornCompositionTriality
open CanonicalZornRealSpin44
open CanonicalZornOuterTrialityGroup
open InfoGeometry.SuperGrassmannian.MajoranaCAR
open InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule
open InfoGeometry.SuperGrassmannian.ModuleColimitSato
open InfoGeometry.SuperGrassmannian.SatoColimitTriality
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.SplitCliffordDirectLimit

inductive Archetype where
  | q11CliffordAlgebra
  | q11MatrixAlgebraEquivalence
  | q11WittOperatorImages
  | q11WittNilpotence
  | q11WittCAR
  | majoranaGenericSplitCell
  | majoranaGenericSplitCellCAR
  | satoGenericSplitCell
  | satoGenericSplitCellCAR
  | superMatrixAndSuperVector
  | homogeneousSupertraceSchema
  | superVectorAction
  | taggedZornCopies
  | taggedZornCoordinateCycle
  | bothChiralZornCompositionIdentities
  | realSplit44QuadraticCarrier
  | realSplit44CliffordRepresentation
  | relatedTripleGroup
  | relatedTripleOuterCycle
  | recursiveSplitCliffordStages
  | oneStepSplitBottEquivalence
  | splitCliffordBondingMaps
  | splitCliffordDirectedSystem
  | splitCliffordDirectLimit
  | abstractGradedSequenceSchema
  | conditionalGradingPropagation
  | abstractModuleActionSequenceSchema
  | conditionalActionPropagation
  | tracialAlgebraSchema
  | satoGaugePremiseSchema
  | conditionalSatoGaugeIndex
  | finiteComplexMatrixStages
  | complexMatrixStageLimit
  | descendedMatrixTrace
  | compatibleStarAlgFamilySchema
  | directLimitMediator
  | uniquenessComparisonPremise
  | uniqueDirectLimitMediator
  deriving DecidableEq, Repr

/-! An edge is admissible only when its constructor receives its owner theorem
or the exact source map/equivalence. Quantified arguments on schema edges are
the premises of the source theorem, not silently discharged assumptions. -/

inductive SourceArc : Archetype → Archetype → Prop where
  | q11_matrix_equiv (h : cl11EquivMat) :
      SourceArc .q11CliffordAlgebra .q11MatrixAlgebraEquivalence
  | q11_witt_matrix_images
      (h : cl11EquivMat cliffordWittAnnihilation = wittAnnihilationBase ∧
        cl11EquivMat cliffordWittCreation = wittCreationBase) :
      SourceArc .q11MatrixAlgebraEquivalence .q11WittOperatorImages
  | q11_witt_nilpotence
      (h : cliffordWittAnnihilation * cliffordWittAnnihilation = 0 ∧
        cliffordWittCreation * cliffordWittCreation = 0) :
      SourceArc .q11WittOperatorImages .q11WittNilpotence
  | q11_witt_car
      (h : cliffordWittAnnihilation * cliffordWittCreation +
        cliffordWittCreation * cliffordWittAnnihilation = 1) :
      SourceArc .q11WittOperatorImages .q11WittCAR
  | majorana_cell_car
      (h : ∀ {R : Type*} [Ring R]
        (C : MajoranaCAR.SplitCliffordCell R),
        MajoranaCAR.SplitCliffordCell.a C * MajoranaCAR.SplitCliffordCell.a_star C +
          MajoranaCAR.SplitCliffordCell.a_star C * MajoranaCAR.SplitCliffordCell.a C = 1) :
      SourceArc .majoranaGenericSplitCell .majoranaGenericSplitCellCAR
  | sato_cell_car
      (h : ∀ {R : Type*} [Ring R]
        (C : SatoColimitTriality.SplitCliffordCell R),
        C.a * C.a_star + C.a_star * C.a = 1) :
      SourceArc .satoGenericSplitCell .satoGenericSplitCellCAR
  | homogeneous_supertrace
      (h : ∀ {R : Type*} [CommRing R]
        (pM pN : RealSuperGrassmannianModule.Parity)
        (M N : RealSuperGrassmannianModule.SuperMatrix R),
        RealSuperGrassmannianModule.isHomogeneous pM M →
        RealSuperGrassmannianModule.isHomogeneous pN N →
        RealSuperGrassmannianModule.SuperMatrix.supertrace
          (RealSuperGrassmannianModule.SuperMatrix.superbracket pM pN M N) = 0) :
      SourceArc .superMatrixAndSuperVector .homogeneousSupertraceSchema
  | supervector_action
      (h : @RealSuperGrassmannianModule.SuperModule.act_mul) :
      SourceArc .superMatrixAndSuperVector .superVectorAction
  | zorn_tagged_coordinate_cycle
      (h : ∀ X : Vector8,
        spinorMinusToVector
          (spinorPlusToSpinorMinus (vectorToSpinorPlus X)) = X) :
      SourceArc .taggedZornCopies .taggedZornCoordinateCycle
  | zorn_both_chiral_compositions
      (h₊ : ∀ (X : Vector8) (S : SpinorPlus8),
        (cliffordMinus X (cliffordPlus X S)).val = zornSmul (vectorNorm X) S.val)
      (h₋ : ∀ (X : Vector8) (S : SpinorMinus8),
        (cliffordPlus X (cliffordMinus X S)).val = zornSmul (vectorNorm X) S.val) :
      SourceArc .taggedZornCopies .bothChiralZornCompositionIdentities
  | real_clifford44_representation
      (h : ∀ x : RealSplit44,
        realClifford44Representation (CliffordAlgebra.ι realQuadratic44 x) =
          realGammaLinear x ∧
        realGammaLinear x * realGammaLinear x =
          algebraMap ℝ (Module.End ℝ DiracSpinor16) (realQuadratic44 x)) :
      SourceArc .realSplit44QuadraticCarrier .realSplit44CliffordRepresentation
  | related_triple_outer_cycle
      (h : ∀ g : CartanTrialityGroup,
        cartanTrialityOuterEquiv (cartanTrialityOuterEquiv
          (cartanTrialityOuterEquiv g)) = g) :
      SourceArc .relatedTripleGroup .relatedTripleOuterCycle
  | split_bott_step
      (h : ∀ n : ℕ,
        SplitBottClifford (n + 1) ≃ₐ[ℝ]
          (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ]
            CliffordAlgebra.evenOdd (SplitBottQuad n))) :
      SourceArc .recursiveSplitCliffordStages .oneStepSplitBottEquivalence
  | split_bonding_maps
      (h : ∀ n : ℕ, SplitClNNAlg n →ₐ[ℝ] SplitClNNAlg (n + 1)) :
      SourceArc .recursiveSplitCliffordStages .splitCliffordBondingMaps
  | split_directed_system
      (h : DirectedSystem SplitClNNAlg
        (fun m n hmn => splitCliffordMap m n hmn)) :
      SourceArc .splitCliffordBondingMaps .splitCliffordDirectedSystem
  | split_direct_limit_carrier
      (h : SplitCliffordInfinity =
        _root_.DirectLimit SplitClNNAlg
          (fun m n hmn => splitCliffordMap m n hmn)) :
      SourceArc .splitCliffordDirectedSystem .splitCliffordDirectLimit
  | graded_chain
      (h : @ModuleColimitSato.grade_intertwining_chain) :
      SourceArc .abstractGradedSequenceSchema .conditionalGradingPropagation
  | module_action_chain
      (h : @ModuleColimitSato.action_intertwining_chain) :
      SourceArc .abstractModuleActionSequenceSchema .conditionalActionPropagation
  | sato_gauge_invariance
      (h : ∀ {A : Type*} [Ring A] (T : SatoColimitTriality.TracialAlgebra A)
        (P Gamma U U_star : A) (hP : P ^ 2 = P)
        (hU_left : U_star * U = 1) (hU_right : U * U_star = 1)
        (hU_comm : U * Gamma = Gamma * U),
        SatoColimitTriality.operatorChiralIndex T (U * P * U_star) Gamma =
          SatoColimitTriality.operatorChiralIndex T P Gamma) :
      SourceArc .satoGaugePremiseSchema .conditionalSatoGaugeIndex
  | matrix_limit_carrier
      (h : MatrixStageLimit = _root_.Quotient matrixStageSetoid) :
      SourceArc .finiteComplexMatrixStages .complexMatrixStageLimit
  | matrix_trace_descent
      (h : ∀ n : ℕ,
        limitNormalizedTrace.comp (canonicalStageHom n).toLinearMap =
          stageNormalizedTraceLM n) :
      SourceArc .complexMatrixStageLimit .descendedMatrixTrace
  | matrix_compatible_family_mediator
      (h : @liftStarAlgHom_comp) :
      SourceArc .compatibleStarAlgFamilySchema .directLimitMediator
  | matrix_unique_mediator
      (h : @liftStarAlgHom_unique) :
      SourceArc .uniquenessComparisonPremise .uniqueDirectLimitMediator

/-! The edge packet is a proposition whose fields instantiate each arc with
the exact imported owner declaration. Conditional interfaces remain visibly
conditional; no default model or hidden hypotheses are supplied. -/

structure OwnerEdges : Prop where
  q11_matrix_equiv : SourceArc .q11CliffordAlgebra .q11MatrixAlgebraEquivalence
  q11_witt_images : SourceArc .q11MatrixAlgebraEquivalence .q11WittOperatorImages
  q11_witt_nilpotence : SourceArc .q11WittOperatorImages .q11WittNilpotence
  q11_witt_car : SourceArc .q11WittOperatorImages .q11WittCAR
  majorana_car : SourceArc .majoranaGenericSplitCell .majoranaGenericSplitCellCAR
  sato_cell_car : SourceArc .satoGenericSplitCell .satoGenericSplitCellCAR
  supertrace : SourceArc .superMatrixAndSuperVector .homogeneousSupertraceSchema
  super_action : SourceArc .superMatrixAndSuperVector .superVectorAction
  zorn_cycle : SourceArc .taggedZornCopies .taggedZornCoordinateCycle
  zorn_compositions : SourceArc .taggedZornCopies .bothChiralZornCompositionIdentities
  real_clifford44 : SourceArc .realSplit44QuadraticCarrier .realSplit44CliffordRepresentation
  related_triple_cycle : SourceArc .relatedTripleGroup .relatedTripleOuterCycle
  bott_step : SourceArc .recursiveSplitCliffordStages .oneStepSplitBottEquivalence
  split_bonding : SourceArc .recursiveSplitCliffordStages .splitCliffordBondingMaps
  split_system : SourceArc .splitCliffordBondingMaps .splitCliffordDirectedSystem
  split_limit : SourceArc .splitCliffordDirectedSystem .splitCliffordDirectLimit
  grade_chain : SourceArc .abstractGradedSequenceSchema .conditionalGradingPropagation
  action_chain : SourceArc .abstractModuleActionSequenceSchema .conditionalActionPropagation
  sato_index : SourceArc .satoGaugePremiseSchema .conditionalSatoGaugeIndex
  matrix_limit : SourceArc .finiteComplexMatrixStages .complexMatrixStageLimit
  trace_descent : SourceArc .complexMatrixStageLimit .descendedMatrixTrace
  lift_mediator : SourceArc .compatibleStarAlgFamilySchema .directLimitMediator
  lift_unique : SourceArc .uniquenessComparisonPremise .uniqueDirectLimitMediator

def ownerEdges : OwnerEdges where
  q11_matrix_equiv := .q11_matrix_equiv cl11EquivMat
  q11_witt_images := .q11_witt_matrix_images
    ⟨cl11EquivMat_wittAnnihilation, cl11EquivMat_wittCreation⟩
  q11_witt_nilpotence := .q11_witt_nilpotence
    ⟨cliffordWittAnnihilation_sq, cliffordWittCreation_sq⟩
  q11_witt_car := .q11_witt_car cliffordWitt_car
  majorana_car := .majorana_cell_car
    (fun {R} _ C => MajoranaCAR.SplitCliffordCell.car_anticommutator C)
  sato_cell_car := .sato_cell_car
    (fun {R} _ C => SatoColimitTriality.SplitCliffordCell.car_anticomm C)
  supertrace := .homogeneous_supertrace
    (fun pM pN M N hM hN =>
      RealSuperGrassmannianModule.SuperMatrix.supertrace_superbracket_eq_zero
        pM pN M N hM hN)
  super_action := .supervector_action (@RealSuperGrassmannianModule.SuperModule.act_mul)
  zorn_cycle := .zorn_tagged_coordinate_cycle (fun X => typed_triality_order_three X)
  zorn_compositions := .zorn_both_chiral_compositions
    (fun X S => cliffordMinus_plus X S)
    (fun X S => cliffordPlus_minus X S)
  real_clifford44 := .real_clifford44_representation
    (fun x => ⟨realClifford44Representation_ι x, realGamma_sq x⟩)
  related_triple_cycle := .related_triple_outer_cycle
    (fun g => cartanTrialityOuterEquiv_order_three g)
  bott_step := .split_bott_step (fun n => splitBottStep n)
  split_bonding := .split_bonding (fun n => splitCliffordStep n)
  split_system := .split_directed_system splitCliffordDirectedSystem
  split_limit := .split_direct_limit_carrier rfl
  grade_chain := .graded_chain (@grade_intertwining_chain)
  action_chain := .module_action_chain (@action_intertwining_chain)
  sato_index := .sato_gauge_invariance (@sato_index_unitary_invariant)
  matrix_limit := .matrix_limit_carrier rfl
  trace_descent := .matrix_trace_descent (fun n => inductiveLimitTrace_comp_stage n)
  lift_mediator := .matrix_compatible_family_mediator (@liftStarAlgHom_comp)
  lift_unique := .matrix_unique_mediator (@liftStarAlgHom_unique)

/-! The causal relation is the reflexive-transitive closure of witnessed source
arcs. The level certificate proves antisymmetry without identifying separate
carrier branches merely because their informal names resemble one another. -/

inductive CausalPath : Archetype → Archetype → Prop where
  | refl (a : Archetype) : CausalPath a a
  | extend {a b c : Archetype} : CausalPath a b → SourceArc b c → CausalPath a c

namespace CausalPath

theorem trans {a b c : Archetype} (p : CausalPath a b) (q : CausalPath b c) :
    CausalPath a c := by
  induction q with
  | refl => exact p
  | @extend b c d q arc ih => exact .extend ih arc

end CausalPath

def level : Archetype → ℕ
  | .q11CliffordAlgebra => 0
  | .q11MatrixAlgebraEquivalence => 1
  | .q11WittOperatorImages => 2
  | .q11WittNilpotence => 3
  | .q11WittCAR => 3
  | .majoranaGenericSplitCell => 0
  | .majoranaGenericSplitCellCAR => 1
  | .satoGenericSplitCell => 0
  | .satoGenericSplitCellCAR => 1
  | .superMatrixAndSuperVector => 0
  | .homogeneousSupertraceSchema => 1
  | .superVectorAction => 1
  | .taggedZornCopies => 0
  | .taggedZornCoordinateCycle => 1
  | .bothChiralZornCompositionIdentities => 1
  | .realSplit44QuadraticCarrier => 0
  | .realSplit44CliffordRepresentation => 1
  | .relatedTripleGroup => 0
  | .relatedTripleOuterCycle => 1
  | .recursiveSplitCliffordStages => 0
  | .oneStepSplitBottEquivalence => 1
  | .splitCliffordBondingMaps => 1
  | .splitCliffordDirectedSystem => 2
  | .splitCliffordDirectLimit => 3
  | .abstractGradedSequenceSchema => 0
  | .conditionalGradingPropagation => 1
  | .abstractModuleActionSequenceSchema => 0
  | .conditionalActionPropagation => 1
  | .tracialAlgebraSchema => 0
  | .satoGaugePremiseSchema => 1
  | .conditionalSatoGaugeIndex => 2
  | .finiteComplexMatrixStages => 0
  | .complexMatrixStageLimit => 1
  | .descendedMatrixTrace => 2
  | .compatibleStarAlgFamilySchema => 0
  | .directLimitMediator => 1
  | .uniquenessComparisonPremise => 2
  | .uniqueDirectLimitMediator => 3

theorem sourceArc_level_lt {a b : Archetype} (h : SourceArc a b) : level a < level b := by
  cases h <;> decide

theorem path_eq_or_level_lt {a b : Archetype} (h : CausalPath a b) :
    a = b ∨ level a < level b := by
  induction h with
  | refl => exact Or.inl rfl
  | @extend a b c p arc ih =>
      rcases ih with heq | hlt
      · subst b
        exact Or.inr (sourceArc_level_lt arc)
      · exact Or.inr (Nat.lt_trans hlt (sourceArc_level_lt arc))

def causalLE (a b : Archetype) : Prop := CausalPath a b

instance : LE Archetype := ⟨causalLE⟩

instance : PartialOrder Archetype where
  le := causalLE
  le_refl a := CausalPath.refl a
  le_trans := CausalPath.trans
  le_antisymm := by
    intro a b hab hba
    rcases path_eq_or_level_lt hab with h | h
    · exact h
    · rcases path_eq_or_level_lt hba with h' | h'
      · exact h'.symm
      · exact (Nat.lt_asymm h h').elim

end InfoGeometry.SuperGrassmannian.CanonicalArchetypePosetV6
