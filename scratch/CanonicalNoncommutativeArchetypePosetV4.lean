import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Physics.Cl11WittChevalleyBridge
import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Canonical.CanonicalZornCompositionTriality
import InfoGeometry.SuperGrassmannian.MajoranaCARSuperalgebra
import InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule
import InfoGeometry.SuperGrassmannian.CategoricalModuleColimitSato
import InfoGeometry.SuperGrassmannian.SatoColimitTriality
import InfoGeometry.Canonical.MatrixStageInductiveLimit

/-!
# Source-grounded partial causal poset of noncommutative archetypes

This file records only dependency edges backed by owner declarations. Distinct
carriers remain distinct branches unless an owner theorem supplies a map:
the native `CliffordAlgebra q11`, the generic `SplitCliffordCell`, the complex
Zorn copies, the generic graded-sequence systems, the tracial-algebra index,
and the complex matrix-stage limit are not silently identified.

Dimension-only triality/Bott arithmetic, orientability language, a GNS or
type-II₁ completion, and Jones-index claims are not nodes in this graph.
-/

noncomputable section

namespace InfoGeometry.SuperGrassmannian.CanonicalArchetypePosetV4

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Physics.Cl11WittChevalleyBridge
open CanonicalZornCompositionTriality
open InfoGeometry.SuperGrassmannian.MajoranaCAR
open InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule
open InfoGeometry.SuperGrassmannian.ModuleColimitSato
open InfoGeometry.SuperGrassmannian.SatoColimitTriality
open InfoGeometry.Canonical.MatrixStageInductiveLimit

/-! ## Owner anchors: each is an actual source declaration, not a label claim. -/

def nativeCl11MatrixEquiv : CliffordAlgebra q11 ≃ₐ[ℝ] Mat2 := cl11EquivMat

theorem nativeCl11WittCAR :
    cliffordWittAnnihilation * cliffordWittCreation +
      cliffordWittCreation * cliffordWittAnnihilation = 1 := cliffordWitt_car

theorem nativeCl11WittNilpotence :
    cliffordWittAnnihilation * cliffordWittAnnihilation = 0 ∧
      cliffordWittCreation * cliffordWittCreation = 0 :=
  ⟨cliffordWittAnnihilation_sq, cliffordWittCreation_sq⟩

def genericSplitCellCARAnchor {R : Type*} [Ring R] (C : SplitCliffordCell R) :=
  SplitCliffordCell.car_anticomm C

def splitBottStepAnchor (n : ℕ) := splitBottStep n

theorem zornTrialityCycleAnchor (X : Vector8) :
    spinorMinusToVector
        (spinorPlusToSpinorMinus (vectorToSpinorPlus X)) = X :=
  typed_triality_order_three X

theorem zornChiralCompositionAnchor (X : Vector8) (S : SpinorPlus8) :
    (cliffordMinus X (cliffordPlus X S)).val = zornSmul (vectorNorm X) S.val :=
  cliffordMinus_plus X S

def superMatrixActionAnchor {R : Type*} [CommRing R] := @SuperModule.act_mul R _

def supertraceAnchor {R : Type*} [CommRing R] := @SuperMatrix.supertrace_superbracket_eq_zero R _

def gradedChainAnchor := @grade_intertwining_chain

def moduleActionChainAnchor := @action_intertwining_chain

def satoUnitaryIndexAnchor := @sato_index_unitary_invariant

def matrixStageLimitAnchor : Type := MatrixStageLimit

theorem matrixStageTraceNormalizedAnchor : limitTrace (1 : MatrixStageLimit) = 1 :=
  limitTrace_one

def matrixStageUniversalMapAnchor := @liftStarAlgHom

/-! ## Nodes and source-supported dependency arcs -/

inductive Archetype where
  | cl11QuadraticCarrier
  | cl11MatrixEquivalence
  | cl11WittOperators
  | cl11CAR
  | genericSplitCell
  | genericSplitCellCAR
  | superMatrixCarrier
  | supertraceIdentity
  | superModuleAction
  | zornCompositionCarrier
  | typedZornTriality
  | zornChiralCliffordActions
  | splitCliffordTower
  | oneStepSplitBottEquivalence
  | abstractGradedSequence
  | conditionalGradingPropagation
  | abstractModuleActionSequence
  | conditionalActionPropagation
  | tracialAlgebraHypotheses
  | conditionalSatoIndexInvariance
  | finiteComplexMatrixStages
  | algebraicMatrixStageLimit
  | descendedLimitTraceAndUniversalMap
  deriving DecidableEq, Repr

inductive Arc : Archetype → Archetype → Prop where
  | cl11_matrix : Arc .cl11QuadraticCarrier .cl11MatrixEquivalence
  | cl11_witt : Arc .cl11QuadraticCarrier .cl11WittOperators
  | witt_car : Arc .cl11WittOperators .cl11CAR
  | cell_car : Arc .genericSplitCell .genericSplitCellCAR
  | super_trace : Arc .superMatrixCarrier .supertraceIdentity
  | super_action : Arc .superMatrixCarrier .superModuleAction
  | zorn_typed : Arc .zornCompositionCarrier .typedZornTriality
  | zorn_actions : Arc .typedZornTriality .zornChiralCliffordActions
  | bott_step : Arc .splitCliffordTower .oneStepSplitBottEquivalence
  | grading_chain : Arc .abstractGradedSequence .conditionalGradingPropagation
  | action_chain : Arc .abstractModuleActionSequence .conditionalActionPropagation
  | sato_index : Arc .tracialAlgebraHypotheses .conditionalSatoIndexInvariance
  | stage_limit : Arc .finiteComplexMatrixStages .algebraicMatrixStageLimit
  | limit_trace : Arc .algebraicMatrixStageLimit .descendedLimitTraceAndUniversalMap

inductive CausalPath : Archetype → Archetype → Prop where
  | refl (a : Archetype) : CausalPath a a
  | extend {a b c : Archetype} : CausalPath a b → Arc b c → CausalPath a c

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
  | .cl11WittOperators => 1
  | .cl11CAR => 2
  | .genericSplitCell => 0
  | .genericSplitCellCAR => 1
  | .superMatrixCarrier => 0
  | .supertraceIdentity => 1
  | .superModuleAction => 1
  | .zornCompositionCarrier => 0
  | .typedZornTriality => 1
  | .zornChiralCliffordActions => 2
  | .splitCliffordTower => 0
  | .oneStepSplitBottEquivalence => 1
  | .abstractGradedSequence => 0
  | .conditionalGradingPropagation => 1
  | .abstractModuleActionSequence => 0
  | .conditionalActionPropagation => 1
  | .tracialAlgebraHypotheses => 0
  | .conditionalSatoIndexInvariance => 1
  | .finiteComplexMatrixStages => 0
  | .algebraicMatrixStageLimit => 1
  | .descendedLimitTraceAndUniversalMap => 2

theorem arc_level_lt {a b : Archetype} (h : Arc a b) : level a < level b := by
  cases h <;> decide

theorem path_eq_or_level_lt {a b : Archetype} (h : CausalPath a b) :
    a = b ∨ level a < level b := by
  induction h with
  | refl => exact Or.inl rfl
  | @extend a b c p arc ih =>
      rcases ih with heq | hlt
      · subst b
        exact Or.inr (arc_level_lt arc)
      · exact Or.inr (Nat.lt_trans hlt (arc_level_lt arc))

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

theorem unrelated_branches_incomparable :
    ¬ CausalPath .cl11QuadraticCarrier .genericSplitCell ∧
      ¬ CausalPath .genericSplitCell .cl11QuadraticCarrier := by
  constructor <;> intro h <;>
    rcases path_eq_or_level_lt h with heq | hlt <;> cases heq <;> cases hlt

theorem generic_cell_is_not_native_cl11_equiv :
    Archetype.genericSplitCell ≠ Archetype.cl11QuadraticCarrier := by
  decide

theorem no_claimed_edge_from_conditional_sato_to_matrix_limit :
    ¬ CausalPath .conditionalSatoIndexInvariance .algebraicMatrixStageLimit := by
  intro h
  rcases path_eq_or_level_lt h with heq | hlt
  · cases heq
  · cases hlt

end InfoGeometry.SuperGrassmannian.CanonicalArchetypePosetV4

end
