import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11GeometricSynthesis
import InfoGeometry.Clifford.SplitQ11CausalCone
import InfoGeometry.SuperGrassmannian.MajoranaCARSuperalgebra
import InfoGeometry.OperatorAlgebra.ChiralRealBivectorRotor
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Clifford.Cl55BivectorVectorRepresentation
import InfoGeometry.Clifford.Cl55SpinGroupChiralLinearEquivRepresentation
import InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule
import InfoGeometry.SuperGrassmannian.CategoricalModuleColimitSato
import InfoGeometry.Canonical.MatrixStageInductiveLimit
import InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
import InfoGeometry.Probability.HomologicalProbability
import InfoGeometry.Lie.SouriauAffineCoadjointInfinitesimalBridge
import Mathlib.Tactic

/-!
# Source-grounded index of noncommutative archetypes

This scratch module indexes owner declarations as a finite causal graph.  Its
edges carry the corresponding owner theorem or algebra-map witness.  Separate
matrix models, abstract sockets, and direct-limit carriers remain separate
vertices unless an imported owner declaration supplies an explicit map.  The
graph is an architecture index; it does not assert that its disconnected
branches form one algebra, representation, or colimit.
-/

noncomputable section

namespace InfoGeometry.Scratch.CanonicalNoncommutativeArchetypePoset

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GeometricSynthesis
open InfoGeometry.Clifford.SplitQ11CausalCone
open InfoGeometry.SuperGrassmannian.MajoranaCAR
open InfoGeometry.SuperGrassmannian.ModuleColimitSato
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.BivectorVectorRepresentation
open InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
open InfoGeometry.Lie

/-- Vertices are carrier/theorem roles from distinct owner branches. -/
inductive Archetype where
  | nativeQ11
  | realMatrixRepresentation
  | volumeForm
  | volumePeirceProjectors
  | diagonalKreinProjectors
  | causalNullHops
  | abstractSplitCell
  | carRelations
  | nativeBivectorAction
  | bivectorBracketLaw
  | abstractRotorCalculus
  | rotorConjugationLaw
  | splitTensorStages
  | splitTensorDirectLimit
  | spinGroupAction
  | chiralSpinRepresentation
  | gradedSupermatrix
  | supertraceLaw
  | gradedSatoSequence
  | gradedSatoTransport
  | complexMatrixStageLimit
  | matrixLimitTrace
  | concreteFiveGrade
  | concreteFiveGradeQuintic
  | genericFiveGradeSocket
  | souriauAffineContext
  | souriauInvariantDerivative
  deriving DecidableEq, Repr

/-- A fixed finite linear extension of the witnessed dependency graph. -/
def rank : Archetype → Nat
  | .nativeQ11 => 0
  | .realMatrixRepresentation => 1
  | .volumeForm => 2
  | .volumePeirceProjectors => 3
  | .diagonalKreinProjectors => 4
  | .causalNullHops => 5
  | .abstractSplitCell => 6
  | .carRelations => 7
  | .nativeBivectorAction => 8
  | .bivectorBracketLaw => 9
  | .abstractRotorCalculus => 10
  | .rotorConjugationLaw => 11
  | .splitTensorStages => 12
  | .splitTensorDirectLimit => 13
  | .spinGroupAction => 14
  | .chiralSpinRepresentation => 15
  | .gradedSupermatrix => 16
  | .supertraceLaw => 17
  | .gradedSatoSequence => 18
  | .gradedSatoTransport => 19
  | .complexMatrixStageLimit => 20
  | .matrixLimitTrace => 21
  | .concreteFiveGrade => 22
  | .concreteFiveGradeQuintic => 23
  | .genericFiveGradeSocket => 24
  | .souriauAffineContext => 25
  | .souriauInvariantDerivative => 26

/-- The relation contains only arrows backed by named owner declarations. -/
inductive EvidenceEdge : Archetype → Archetype → Prop where
  | q11_matrix_equiv
      (w : Nonempty (CliffordAlgebra q11 ≃ₐ[ℝ] Mat2)) :
      EvidenceEdge .nativeQ11 .realMatrixRepresentation
  | volume_projectors
      (hω : omega * omega = 1)
      (hplus : P_plus * P_plus = P_plus)
      (hminus : P_minus * P_minus = P_minus)
      (horth : P_plus * P_minus = 0)
      (hsum : P_plus + P_minus = one) :
      EvidenceEdge .volumeForm .volumePeirceProjectors
  | krein_null_closure
      (h : matrixCausalNullPlus * matrixCausalNullPlus = 0 ∧
        matrixCausalNullMinus * matrixCausalNullMinus = 0 ∧
        matrixCausalNullPlus * matrixCausalNullMinus = matrixKreinPlusProjector ∧
        matrixCausalNullMinus * matrixCausalNullPlus = matrixKreinMinusProjector ∧
        matrixCausalNullPlus * matrixCausalNullMinus +
          matrixCausalNullMinus * matrixCausalNullPlus = (1 : Mat2) ∧
        matrixCausalNullPlus * matrixCausalNullMinus -
          matrixCausalNullMinus * matrixCausalNullPlus = Eplus) :
      EvidenceEdge .diagonalKreinProjectors .causalNullHops
  | split_cell_car
      (h : ∀ {R : Type*} [Ring R] (C : SplitCliffordCell R),
        a C * a_star C + a_star C * a C = 1) :
      EvidenceEdge .abstractSplitCell .carRelations
  | bivector_bracket
      (h : ∀ (u₁ v₁ u₂ v₂ w : V55),
        ⁅⁅ι55 u₁ * ι55 v₁, ι55 u₂ * ι55 v₂⁆, ι55 w⁆ =
          ι55 (bivectorVectorTransform u₁ v₁
            (bivectorVectorTransform u₂ v₂ w) -
            bivectorVectorTransform u₂ v₂
              (bivectorVectorTransform u₁ v₁ w))) :
      EvidenceEdge .nativeBivectorAction .bivectorBracketLaw
  | rotor_conjugation
      (h : ∀ {A : Type*} [Ring A] [Algebra ℝ A]
        (mirror : Units A) (B : A) (θ : ℝ),
        conjugate mirror B = -B →
        conjugate mirror (rotor B θ) = reverseRotor B θ) :
      EvidenceEdge .abstractRotorCalculus .rotorConjugationLaw
  | split_tower_limit
      (h : ∀ (n : ℕ) (A : Cl11TensorTowerLimit.Stage n),
        Cl11TensorTowerLimit.ofStage (n + 1)
          (Cl11TensorTower.stageEmbed n A) =
        Cl11TensorTowerLimit.ofStage n A) :
      EvidenceEdge .splitTensorStages .splitTensorDirectLimit
  | spin_representation
      (w : Nonempty (Spin55 →*
        (Cl55SpinGroupChiralSectorBridge.chiralPlusSector ≃ₗ[ℝ]
          Cl55SpinGroupChiralSectorBridge.chiralPlusSector))) :
      EvidenceEdge .spinGroupAction .chiralSpinRepresentation
  | supertrace_bracket
      (h : ∀ {R : Type*} [CommRing R]
        (p q : RealSuperGrassmannianModule.Parity)
        (M N : RealSuperGrassmannianModule.SuperMatrix R)
        (hM : RealSuperGrassmannianModule.SuperMatrix.isHomogeneous p M)
        (hN : RealSuperGrassmannianModule.SuperMatrix.isHomogeneous q N),
        RealSuperGrassmannianModule.SuperMatrix.supertrace
          (RealSuperGrassmannianModule.SuperMatrix.superbracket p q M N) = 0) :
      EvidenceEdge .gradedSupermatrix .supertraceLaw
  | sato_grade_transport
      (h : ∀ (S : GradedInductiveSequence) (n k : ℕ) (v : S.V n),
        (S.graded (n + k)).gamma (iotaChain S n k v) =
          iotaChain S n k ((S.graded n).gamma v)) :
      EvidenceEdge .gradedSatoSequence .gradedSatoTransport
  | matrix_limit_trace
      (hcompat : ∀ (n : ℕ),
        limitNormalizedTrace.comp (canonicalStageHom n).toLinearMap =
          stageNormalizedTraceLM n)
      (hcyclic : ∀ (X Y : MatrixStageLimit),
        limitTrace (X * Y) = limitTrace (Y * X)) :
      EvidenceEdge .complexMatrixStageLimit .matrixLimitTrace
  | concrete_five_grade_quintic
      (h : ∀ {R : Type*} [CommRing R]
        (X : Matrix (Fin 3) (Fin 3) R),
        adH (adH (adH (adH (adH X)))) -
          5 • adH (adH (adH X)) + 4 • adH X = 0) :
      EvidenceEdge .concreteFiveGrade .concreteFiveGradeQuintic
  | souriau_affine_invariance
      (h : ∀ {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
        {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g]
        (A : SouriauAffineCoadjointInfinitesimalBridge.AffineCoadjointInfinitesimalData M g)
        (S : M → ℝ) (dS_Q : M →L[ℝ] ℝ)
        (h_inv : IsFlowInvariant A.toInfinitesimalCurveFamilyDatum S)
        (Q : M) (h_diff : HasFDerivAt S dS_Q Q),
        dS_Q (A.datum.adStar A.generator Q + A.datum.Theta A.generator) = 0) :
      EvidenceEdge .souriauAffineContext .souriauInvariantDerivative

theorem q11_matrix_equiv_edge :
    EvidenceEdge .nativeQ11 .realMatrixRepresentation :=
  .q11_matrix_equiv ⟨cl11EquivMat⟩

theorem volume_projectors_edge :
    EvidenceEdge .volumeForm .volumePeirceProjectors :=
  .volume_projectors omega_sq P_plus_sq P_minus_sq P_plus_mul_P_minus
    P_plus_add_P_minus

theorem krein_null_closure_edge :
    EvidenceEdge .diagonalKreinProjectors .causalNullHops :=
  .krein_null_closure matrix_causal_null_closure_laws

theorem split_cell_car_edge :
    EvidenceEdge .abstractSplitCell .carRelations :=
  .split_cell_car car_anticommutator

theorem bivector_bracket_edge :
    EvidenceEdge .nativeBivectorAction .bivectorBracketLaw :=
  .bivector_bracket bivector_bracket_vector_action

theorem rotor_conjugation_edge :
    EvidenceEdge .abstractRotorCalculus .rotorConjugationLaw :=
  .rotor_conjugation conjugate_rotor

theorem split_tower_limit_edge :
    EvidenceEdge .splitTensorStages .splitTensorDirectLimit :=
  .split_tower_limit Cl11TensorTowerLimit.ofStage_apply_bond

theorem spin_representation_edge :
    EvidenceEdge .spinGroupAction .chiralSpinRepresentation :=
  .spin_representation ⟨Cl55SpinGroupChiralLinearEquivRepresentation.chiralPlusLinearEquivRepresentation⟩

theorem supertrace_bracket_edge :
    EvidenceEdge .gradedSupermatrix .supertraceLaw :=
  .supertrace_bracket RealSuperGrassmannianModule.SuperMatrix.supertrace_superbracket_eq_zero

theorem sato_grade_transport_edge :
    EvidenceEdge .gradedSatoSequence .gradedSatoTransport :=
  .sato_grade_transport grade_intertwining_chain

theorem matrix_limit_trace_edge :
    EvidenceEdge .complexMatrixStageLimit .matrixLimitTrace :=
  .matrix_limit_trace inductiveLimitTrace_comp_stage limitTrace_mul_comm

theorem concrete_five_grade_quintic_edge :
    EvidenceEdge .concreteFiveGrade .concreteFiveGradeQuintic :=
  .concrete_five_grade_quintic adH_quintic_identity

theorem souriau_affine_invariance_edge :
    EvidenceEdge .souriauAffineContext .souriauInvariantDerivative :=
  .souriau_affine_invariance
    SouriauAffineCoadjointInfinitesimalBridge.affineCasimir_annihilates_fundamentalVector

/-- Reflexive-transitive closure of the owner-witnessed direct edges. -/
inductive Reachable : Archetype → Archetype → Prop where
  | refl (a : Archetype) : Reachable a a
  | step {a b : Archetype} (h : EvidenceEdge a b) : Reachable a b
  | trans {a b c : Archetype} (hab : Reachable a b)
      (hbc : Reachable b c) : Reachable a c

theorem edge_rank_strict {a b : Archetype} (h : EvidenceEdge a b) :
    rank a < rank b := by
  cases h <;> simp [rank] <;> omega

theorem reachable_rank_monotone {a b : Archetype}
    (h : Reachable a b) : rank a ≤ rank b := by
  induction h with
  | refl a => exact Nat.le_refl _
  | step h => exact Nat.le_of_lt (edge_rank_strict h)
  | trans _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂

theorem reachable_refl (a : Archetype) : Reachable a a :=
  .refl a

theorem reachable_trans {a b c : Archetype}
    (hab : Reachable a b) (hbc : Reachable b c) : Reachable a c :=
  .trans hab hbc

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp [rank] at h <;> rfl

theorem reachable_antisymm {a b : Archetype}
    (hab : Reachable a b) (hba : Reachable b a) : a = b := by
  apply rank_injective
  exact Nat.le_antisymm (reachable_rank_monotone hab)
    (reachable_rank_monotone hba)

theorem reachable_acyclic {a : Archetype}
    (h : Reachable a a) : rank a ≤ rank a :=
  reachable_rank_monotone h

theorem reachability_is_partial_order :
    (∀ a : Archetype, Reachable a a) ∧
    (∀ {a b c : Archetype}, Reachable a b → Reachable b c → Reachable a c) ∧
    (∀ {a b : Archetype}, Reachable a b → Reachable b a → a = b) := by
  exact ⟨reachable_refl, fun _ _ => reachable_trans,
    fun hab hba => reachable_antisymm hab hba⟩

theorem archetype_partial_order :
    ∀ {a b : Archetype}, Reachable a b → Reachable b a → a = b :=
  fun _ _ hab hba => reachable_antisymm hab hba

end InfoGeometry.Scratch.CanonicalNoncommutativeArchetypePoset
