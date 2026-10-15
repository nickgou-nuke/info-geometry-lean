import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Physics.Cl11WittChevalleyBridge
import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Canonical.CanonicalZornCompositionTriality
import InfoGeometry.SuperGrassmannian.MajoranaCARSuperalgebra
import InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule
import InfoGeometry.SuperGrassmannian.CategoricalModuleColimitSato
import InfoGeometry.SuperGrassmannian.SatoColimitTriality
import InfoGeometry.Canonical.MatrixStageInductiveLimit

/-!
# Evidence-carrying partial causal poset of operator archetypes

The arcs below carry owner-level Lean evidence. This is a curated partial
poset, not a claim that every repository declaration has been classified.
The native `CliffordAlgebra q11`, the two separately defined split-cell
structures, complex Zorn triality copies, the recursive split-Clifford direct
limit, generic sequence schemas, and the complex matrix-stage direct limit
remain distinct carriers. No arc identifies the two limits or promotes
dimension parity to a geometric orientability result.
-/

noncomputable section

namespace InfoGeometry.SuperGrassmannian.CanonicalArchetypePosetV5

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Physics.Cl11WittChevalleyBridge
open CanonicalZornCompositionTriality
open InfoGeometry.SuperGrassmannian.MajoranaCAR
open InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule
open InfoGeometry.SuperGrassmannian.ModuleColimitSato
open InfoGeometry.SuperGrassmannian.SatoColimitTriality
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.SplitCliffordDirectLimit

inductive Archetype where
  | cl11QuadraticCarrier
  | cl11MatrixEquivalence
  | cl11WittElements
  | cl11WittCAR
  | majoranaCell
  | majoranaCellCAR
  | satoCell
  | satoCellCAR
  | superMatrixCarrier
  | homogeneousSupertraceIdentity
  | superMatrixOnSuperVectorAction
  | zornCompositionCarrier
  | typedZornTriality
  | zornChiralCliffordActions
  | recursiveSplitCliffordStages
  | oneStepSplitBottEquivalence
  | splitCliffordBondingMaps
  | splitCliffordDirectedSystem
  | splitCliffordDirectLimit
  | abstractGradedSequence
  | conditionalGradingPropagation
  | abstractModuleActionSequence
  | conditionalActionPropagation
  | tracialAlgebraSchema
  | conditionalSatoGaugeIndex
  | finiteComplexMatrixStages
  | complexMatrixStageLimit
  | descendedMatrixTrace
  | directLimitMediator
  | uniqueDirectLimitMediator
  deriving DecidableEq, Repr

/-! Each constructor requires the actual theorem/map carried by its edge. -/

inductive SourceArc : Archetype → Archetype → Prop where
  | q11_matrix_equiv
      (h : CliffordAlgebra q11 ≃ₐ[ℝ] Mat2) :
      SourceArc .cl11QuadraticCarrier .cl11MatrixEquivalence
  | q11_witt_elements
      (h : (cliffordWittAnnihilation, cliffordWittCreation) :
        CliffordAlgebra q11 × CliffordAlgebra q11) :
      SourceArc .cl11QuadraticCarrier .cl11WittElements
  | witt_car
      (h : cliffordWittAnnihilation * cliffordWittCreation +
        cliffordWittCreation * cliffordWittAnnihilation = 1) :
      SourceArc .cl11WittElements .cl11WittCAR
  | matrix_equiv_used_for_witt_car
      (h : Function.Injective cl11EquivMat ∧
        cliffordWittAnnihilation * cliffordWittCreation +
          cliffordWittCreation * cliffordWittAnnihilation = 1) :
      SourceArc .cl11MatrixEquivalence .cl11WittCAR
  | majorana_cell_car
      (h : ∀ {R : Type*} [Ring R]
        (C : MajoranaCAR.SplitCliffordCell R),
        MajoranaCAR.SplitCliffordCell.a C * MajoranaCAR.SplitCliffordCell.a_star C +
          MajoranaCAR.SplitCliffordCell.a_star C * MajoranaCAR.SplitCliffordCell.a C = 1) :
      SourceArc .majoranaCell .majoranaCellCAR
  | sato_cell_car
      (h : ∀ {R : Type*} [Ring R]
        (C : SatoColimitTriality.SplitCliffordCell R),
        C.a * C.a_star + C.a_star * C.a = 1) :
      SourceArc .satoCell .satoCellCAR
  | supertrace_homogeneous
      (h : @SuperMatrix.supertrace_superbracket_eq_zero) :
      SourceArc .superMatrixCarrier .homogeneousSupertraceIdentity
  | supermatrix_action
      (h : @SuperModule.act_mul) :
      SourceArc .superMatrixCarrier .superMatrixOnSuperVectorAction
  | zorn_typed_cycle
      (h : ∀ X : Vector8,
        spinorMinusToVector
          (spinorPlusToSpinorMinus (vectorToSpinorPlus X)) = X) :
      SourceArc .zornCompositionCarrier .typedZornTriality
  | zorn_chiral_composition
      (h : ∀ (X : Vector8) (S : SpinorPlus8),
        (cliffordMinus X (cliffordPlus X S)).val = zornSmul (vectorNorm X) S.val) :
      SourceArc .typedZornTriality .zornChiralCliffordActions
  | split_bott_step
      (h : ∀ n : ℕ, SplitBottClifford (n + 1) ≃ₐ[ℝ]
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
      SourceArc .abstractGradedSequence .conditionalGradingPropagation
  | module_action_chain
      (h : @ModuleColimitSato.action_intertwining_chain) :
      SourceArc .abstractModuleActionSequence .conditionalActionPropagation
  | sato_unitary_index
      (h : @SatoColimitTriality.sato_index_unitary_invariant) :
      SourceArc .tracialAlgebraSchema .conditionalSatoGaugeIndex
  | matrix_limit_carrier
      (h : MatrixStageLimit =
        _root_.Quotient matrixStageSetoid) :
      SourceArc .finiteComplexMatrixStages .complexMatrixStageLimit
  | matrix_trace_descent
      (h : ∀ n : ℕ,
        limitNormalizedTrace.comp (canonicalStageHom n).toLinearMap =
          stageNormalizedTraceLM n) :
      SourceArc .complexMatrixStageLimit .descendedMatrixTrace
  | matrix_lift_exists
      (h : @liftStarAlgHom_comp) :
      SourceArc .complexMatrixStageLimit .directLimitMediator
  | matrix_lift_unique
      (h : @liftStarAlgHom_unique) :
      SourceArc .directLimitMediator .uniqueDirectLimitMediator

/-! Canonical edge witnesses bind the graph to the imported owner declarations. -/

structure OwnerEdges : Prop where
  q11_matrix_equiv : SourceArc .cl11QuadraticCarrier .cl11MatrixEquivalence
  q11_witt_elements : SourceArc .cl11QuadraticCarrier .cl11WittElements
  witt_car : SourceArc .cl11WittElements .cl11WittCAR
  matrix_witt_car : SourceArc .cl11MatrixEquivalence .cl11WittCAR
  majorana_car : SourceArc .majoranaCell .majoranaCellCAR
  sato_car : SourceArc .satoCell .satoCellCAR
  supertrace : SourceArc .superMatrixCarrier .homogeneousSupertraceIdentity
  super_action : SourceArc .superMatrixCarrier .superMatrixOnSuperVectorAction
  zorn_cycle : SourceArc .zornCompositionCarrier .typedZornTriality
  zorn_action : SourceArc .typedZornTriality .zornChiralCliffordActions
  bott_step : SourceArc .recursiveSplitCliffordStages .oneStepSplitBottEquivalence
  split_bonding : SourceArc .recursiveSplitCliffordStages .splitCliffordBondingMaps
  split_system : SourceArc .splitCliffordBondingMaps .splitCliffordDirectedSystem
  split_limit : SourceArc .splitCliffordDirectedSystem .splitCliffordDirectLimit
  grade_chain : SourceArc .abstractGradedSequence .conditionalGradingPropagation
  action_chain : SourceArc .abstractModuleActionSequence .conditionalActionPropagation
  sato_index : SourceArc .tracialAlgebraSchema .conditionalSatoGaugeIndex
  matrix_limit : SourceArc .finiteComplexMatrixStages .complexMatrixStageLimit
  trace_descent : SourceArc .complexMatrixStageLimit .descendedMatrixTrace
  lift_exists : SourceArc .complexMatrixStageLimit .directLimitMediator
  lift_unique : SourceArc .directLimitMediator .uniqueDirectLimitMediator

def ownerEdges : OwnerEdges where
  q11_matrix_equiv := .q11_matrix_equiv cl11EquivMat
  q11_witt_elements := .q11_witt_elements ⟨cliffordWittAnnihilation, cliffordWittCreation⟩
  witt_car := .witt_car cliffordWitt_car
  matrix_witt_car := .matrix_equiv_used_for_witt_car
    ⟨cl11EquivMat.injective, cliffordWitt_car⟩
  majorana_car := .majorana_cell_car
    (fun {R} _ C => MajoranaCAR.SplitCliffordCell.car_anticommutator C)
  sato_car := .sato_cell_car
    (fun {R} _ C => SatoColimitTriality.SplitCliffordCell.car_anticomm C)
  supertrace := .supertrace_homogeneous
    (@SuperMatrix.supertrace_superbracket_eq_zero)
  super_action := .supermatrix_action (@SuperModule.act_mul)
  zorn_cycle := .zorn_typed_cycle (fun X => typed_triality_order_three X)
  zorn_action := .zorn_chiral_composition (fun X S => cliffordMinus_plus X S)
  bott_step := .split_bott_step (fun n => splitBottStep n)
  split_bonding := .split_bonding (fun n => splitCliffordStep n)
  split_system := .split_directed_system splitCliffordDirectedSystem
  split_limit := .split_direct_limit_carrier rfl
  grade_chain := .graded_chain (@grade_intertwining_chain)
  action_chain := .module_action_chain (@action_intertwining_chain)
  sato_index := .sato_unitary_index (@sato_index_unitary_invariant)
  matrix_limit := .matrix_limit_carrier rfl
  trace_descent := .matrix_trace_descent (fun n => inductiveLimitTrace_comp_stage n)
  lift_exists := .matrix_lift_exists (@liftStarAlgHom_comp)
  lift_unique := .matrix_lift_unique (@liftStarAlgHom_unique)

/-! ## Causal relation and its partial-order proof -/

inductive CausalPath : Archetype → Archetype → Prop where
  | refl (a : Archetype) : CausalPath a a
  | extend {a b c : Archetype} : CausalPath a b → SourceArc b c → CausalPath a c

namespace CausalPath

theorem trans {a b c : Archetype} (p : CausalPath a b) (q : CausalPath b c) :
    CausalPath a c := by
  induction q with
  | refl => exact p
  | @extend b c d q h ih => exact .extend ih h

end CausalPath

def level : Archetype → ℕ
  | .cl11QuadraticCarrier => 0
  | .cl11MatrixEquivalence => 1
  | .cl11WittElements => 1
  | .cl11WittCAR => 2
  | .majoranaCell => 0
  | .majoranaCellCAR => 1
  | .satoCell => 0
  | .satoCellCAR => 1
  | .superMatrixCarrier => 0
  | .homogeneousSupertraceIdentity => 1
  | .superMatrixOnSuperVectorAction => 1
  | .zornCompositionCarrier => 0
  | .typedZornTriality => 1
  | .zornChiralCliffordActions => 2
  | .recursiveSplitCliffordStages => 0
  | .oneStepSplitBottEquivalence => 1
  | .splitCliffordBondingMaps => 1
  | .splitCliffordDirectedSystem => 2
  | .splitCliffordDirectLimit => 3
  | .abstractGradedSequence => 0
  | .conditionalGradingPropagation => 1
  | .abstractModuleActionSequence => 0
  | .conditionalActionPropagation => 1
  | .tracialAlgebraSchema => 0
  | .conditionalSatoGaugeIndex => 1
  | .finiteComplexMatrixStages => 0
  | .complexMatrixStageLimit => 1
  | .descendedMatrixTrace => 2
  | .directLimitMediator => 2
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
      · exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt h')) h)

theorem native_and_generic_cells_are_distinct_labels :
    Archetype.cl11QuadraticCarrier ≠ Archetype.majoranaCell := by decide

theorem recursive_and_matrix_limits_are_distinct_labels :
    Archetype.splitCliffordDirectLimit ≠ Archetype.complexMatrixStageLimit := by decide

theorem no_path_between_clifford_and_generic_majorana_cell :
    ¬ CausalPath .cl11QuadraticCarrier .majoranaCell ∧
      ¬ CausalPath .majoranaCell .cl11QuadraticCarrier := by
  constructor <;> intro h <;>
    rcases path_eq_or_level_lt h with heq | hlt <;> cases heq <;> cases hlt

end InfoGeometry.SuperGrassmannian.CanonicalArchetypePosetV5

end
