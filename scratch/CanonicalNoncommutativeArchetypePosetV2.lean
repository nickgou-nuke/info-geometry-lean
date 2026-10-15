import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11GeometricSynthesis
import InfoGeometry.Clifford.Cl11CanonicalArchetypePoset
import InfoGeometry.Clifford.Cl11SplitQuaternions
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
# Source-grounded index of witnessed noncommutative archetypes

This scratch module is an owner-source architecture index. Every edge carries
an exact imported owner theorem or algebra-map witness. The native Cl(1,1)
CAR cell is locally constructed over `CliffordAlgebra q11`; the generic CAR
socket remains a separate branch. Volume projectors and diagonal Krein
projectors are distinct branches. The real split tensor limit and complex
matrix limit remain separate. The Cl(1,2) matrix-generator-relations theorem
is included without upgrading it to a native Clifford equivalence. The
Cl(1,2) AlgEquiv attempt and other unverified scratch candidates are isolated
vertices and supply no edges.
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
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Probability.Homological
open InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule

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
  | nativeCl11CARCandidate
  | nativeBivectorAction
  | bivectorBracketLaw
  | abstractRotorCalculus
  | rotorConjugationLaw
  | nativeCl12EquivalenceCandidate
  | cl12MatrixGeneratorModel
  | cl12MatrixGeneratorRelations
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
  | .nativeCl11CARCandidate => 8
  | .nativeBivectorAction => 9
  | .bivectorBracketLaw => 10
  | .abstractRotorCalculus => 11
  | .rotorConjugationLaw => 12
  | .nativeCl12EquivalenceCandidate => 13
  | .cl12MatrixGeneratorModel => 14
  | .cl12MatrixGeneratorRelations => 15
  | .splitTensorStages => 16
  | .splitTensorDirectLimit => 17
  | .spinGroupAction => 18
  | .chiralSpinRepresentation => 19
  | .gradedSupermatrix => 20
  | .supertraceLaw => 21
  | .gradedSatoSequence => 22
  | .gradedSatoTransport => 23
  | .complexMatrixStageLimit => 24
  | .matrixLimitTrace => 25
  | .concreteFiveGrade => 26
  | .concreteFiveGradeQuintic => 27
  | .genericFiveGradeSocket => 28
  | .souriauAffineContext => 29
  | .souriauInvariantDerivative => 30

/-- Native real Clifford carrier used to instantiate the repository CAR cell. -/
abbrev NativeCl11 := CliffordAlgebra Cl11Matrix.q11

def nativePositiveGenerator : NativeCl11 :=
  CliffordAlgebra.ι Cl11Matrix.q11 (1, 0)

def nativeNegativeGenerator : NativeCl11 :=
  CliffordAlgebra.ι Cl11Matrix.q11 (0, 1)

def nativeHalf : NativeCl11 := algebraMap ℝ NativeCl11 (1 / 2 : ℝ)

theorem nativeHalf_add_nativeHalf : nativeHalf + nativeHalf = 1 := by
  calc
    nativeHalf + nativeHalf =
        algebraMap ℝ NativeCl11 ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
          rw [← map_add]
          rfl
    _ = 1 := by
      rw [show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num, map_one]

theorem nativeHalf_commutes (x : NativeCl11) : nativeHalf * x = x * nativeHalf :=
  Algebra.commutes (1 / 2 : ℝ) x

def nativeCARCell : MajoranaCAR.SplitCliffordCell NativeCl11 where
  e := nativePositiveGenerator
  f := nativeNegativeGenerator
  half := nativeHalf
  e_sq := by
    apply Cl11Matrix.cl11EquivMat.injective
    simp [nativePositiveGenerator, Cl11Matrix.cl11EquivMat_iota_pos,
      Cl11Matrix.Eplus_sq]
  f_sq := by
    apply Cl11Matrix.cl11EquivMat.injective
    simp [nativeNegativeGenerator, Cl11Matrix.cl11EquivMat_iota_neg,
      Cl11Matrix.Eminus_sq]
  anticomm := by
    apply Cl11Matrix.cl11EquivMat.injective
    simpa [nativePositiveGenerator, nativeNegativeGenerator] using
      Cl11Matrix.cl11EquivMat_iota_pos_neg_anticomm
  two_half := nativeHalf_add_nativeHalf
  half_comm := nativeHalf_commutes

theorem native_cl11_CAR :
    MajoranaCAR.SplitCliffordCell.a nativeCARCell *
        MajoranaCAR.SplitCliffordCell.a_star nativeCARCell +
      MajoranaCAR.SplitCliffordCell.a_star nativeCARCell *
        MajoranaCAR.SplitCliffordCell.a nativeCARCell = 1 :=
  MajoranaCAR.SplitCliffordCell.car_anticommutator nativeCARCell

/-- Branch identifiers preserve carrier separation along every witnessed edge. -/
def branch : Archetype → Nat
  | .nativeQ11 | .realMatrixRepresentation | .volumeForm |
      .volumePeirceProjectors | .nativeCl11CARCandidate => 0
  | .diagonalKreinProjectors | .causalNullHops => 1
  | .abstractSplitCell | .carRelations => 3
  | .nativeBivectorAction | .bivectorBracketLaw => 5
  | .abstractRotorCalculus | .rotorConjugationLaw => 6
  | .nativeCl12EquivalenceCandidate => 7
  | .cl12MatrixGeneratorModel | .cl12MatrixGeneratorRelations => 8
  | .splitTensorStages | .splitTensorDirectLimit => 9
  | .spinGroupAction | .chiralSpinRepresentation => 10
  | .gradedSupermatrix | .supertraceLaw => 11
  | .gradedSatoSequence | .gradedSatoTransport => 12
  | .complexMatrixStageLimit | .matrixLimitTrace => 13
  | .concreteFiveGrade | .concreteFiveGradeQuintic => 14
  | .genericFiveGradeSocket => 15
  | .souriauAffineContext | .souriauInvariantDerivative => 16

/-- The relation contains only arrows backed by named owner declarations. -/
inductive EvidenceEdge : Archetype → Archetype → Prop where
  | q11_matrix_equiv
      (w : Nonempty (CliffordAlgebra q11 ≃ₐ[ℝ] Mat2)) :
      EvidenceEdge .nativeQ11 .realMatrixRepresentation
  | q11_volume_matrix_readback
      (h : InfoGeometry.Clifford.Cl11GeometricSynthesis.omega =
        InfoGeometry.Clifford.Cl11Matrix.J1) :
      EvidenceEdge .realMatrixRepresentation .volumeForm
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
  | native_cl11_car
      (C : MajoranaCAR.SplitCliffordCell NativeCl11)
      (h : MajoranaCAR.SplitCliffordCell.a C *
          MajoranaCAR.SplitCliffordCell.a_star C +
        MajoranaCAR.SplitCliffordCell.a_star C *
          MajoranaCAR.SplitCliffordCell.a C = 1) :
      EvidenceEdge .nativeQ11 .nativeCl11CARCandidate
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
        ChiralRealBivectorRotor.conjugate mirror B = -B →
        ChiralRealBivectorRotor.conjugate mirror
          (ChiralRealBivectorRotor.rotor B θ) =
            ChiralRealBivectorRotor.reverseRotor B θ) :
      EvidenceEdge .abstractRotorCalculus .rotorConjugationLaw
  | cl12_matrix_relations
      (h : InfoGeometry.Clifford.Cl11.I_3D * InfoGeometry.Clifford.Cl11.I_3D =
            -(1 : InfoGeometry.Clifford.Cl11.Mat2C) ∧
        (∀ M : InfoGeometry.Clifford.Cl11.Mat2C,
          InfoGeometry.Clifford.Cl11.I_3D * M = M * InfoGeometry.Clifford.Cl11.I_3D) ∧
        InfoGeometry.Clifford.Cl11.e₁C * InfoGeometry.Clifford.Cl11.e₁C = 1 ∧
        InfoGeometry.Clifford.Cl11.e₂C * InfoGeometry.Clifford.Cl11.e₂C = -1 ∧
        InfoGeometry.Clifford.Cl11.fC * InfoGeometry.Clifford.Cl11.fC = -1) :
      EvidenceEdge .cl12MatrixGeneratorModel .cl12MatrixGeneratorRelations
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
        FiveGradedLieSuperalgebra.adH
          (FiveGradedLieSuperalgebra.adH
            (FiveGradedLieSuperalgebra.adH
              (FiveGradedLieSuperalgebra.adH
                (FiveGradedLieSuperalgebra.adH X)))) -
          5 • FiveGradedLieSuperalgebra.adH
            (FiveGradedLieSuperalgebra.adH
              (FiveGradedLieSuperalgebra.adH X)) +
          4 • FiveGradedLieSuperalgebra.adH X = 0) :
      EvidenceEdge .concreteFiveGrade .concreteFiveGradeQuintic
  | souriau_affine_invariance
      (h : ∀ {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
        {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g]
        (A : SouriauAffineCoadjointInfinitesimalBridge.AffineCoadjointInfinitesimalData M g)
        (S : M → ℝ) (dS_Q : M →L[ℝ] ℝ)
        (h_inv : InfoGeometry.Lie.IsFlowInvariant
          A.toInfinitesimalCurveFamilyDatum S)
        (Q : M) (h_diff : HasFDerivAt S dS_Q Q),
        dS_Q (A.datum.adStar A.generator Q + A.datum.Theta A.generator) = 0) :
      EvidenceEdge .souriauAffineContext .souriauInvariantDerivative

theorem q11_matrix_equiv_edge :
    EvidenceEdge .nativeQ11 .realMatrixRepresentation :=
  .q11_matrix_equiv ⟨cl11EquivMat⟩

theorem q11_volume_matrix_readback_edge :
    EvidenceEdge .realMatrixRepresentation .volumeForm :=
  .q11_volume_matrix_readback
    Cl11CanonicalArchetypePoset.synthesis_omega_eq_native

theorem volume_projectors_edge :
    EvidenceEdge .volumeForm .volumePeirceProjectors :=
  .volume_projectors omega_sq P_plus_sq P_minus_sq P_plus_mul_P_minus
    P_plus_add_P_minus

theorem krein_null_closure_edge :
    EvidenceEdge .diagonalKreinProjectors .causalNullHops :=
  .krein_null_closure matrix_causal_null_closure_laws

theorem split_cell_car_edge :
    EvidenceEdge .abstractSplitCell .carRelations :=
  .split_cell_car MajoranaCAR.car_anticommutator

theorem native_cl11_car_edge :
    EvidenceEdge .nativeQ11 .nativeCl11CARCandidate :=
  .native_cl11_car nativeCARCell native_cl11_CAR

theorem bivector_bracket_edge :
    EvidenceEdge .nativeBivectorAction .bivectorBracketLaw :=
  .bivector_bracket
    BivectorVectorRepresentation.bivector_bracket_vector_action

theorem rotor_conjugation_edge :
    EvidenceEdge .abstractRotorCalculus .rotorConjugationLaw :=
  .rotor_conjugation ChiralRealBivectorRotor.conjugate_rotor

theorem cl12_matrix_generator_relations_edge :
    EvidenceEdge .cl12MatrixGeneratorModel .cl12MatrixGeneratorRelations :=
  .cl12_matrix_relations
    InfoGeometry.Clifford.Cl11.cl12_biquaternion_generator_relations

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
  .concrete_five_grade_quintic
    FiveGradedLieSuperalgebra.adH_quintic_identity

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

/-- A path with at least one witnessed edge. -/
inductive PositivePath : Archetype → Archetype → Prop where
  | edge {a b : Archetype} (h : EvidenceEdge a b) : PositivePath a b
  | tail {a b c : Archetype} (hab : PositivePath a b)
      (hbc : Reachable b c) : PositivePath a c

theorem edge_rank_strict {a b : Archetype} (h : EvidenceEdge a b) :
    rank a < rank b := by
  cases h <;> simp [rank] <;> omega

theorem edge_preserves_branch {a b : Archetype} (h : EvidenceEdge a b) :
    branch a = branch b := by
  cases h <;> rfl

theorem reachable_rank_monotone {a b : Archetype}
    (h : Reachable a b) : rank a ≤ rank b := by
  induction h with
  | refl a => exact Nat.le_refl _
  | step h => exact Nat.le_of_lt (edge_rank_strict h)
  | trans _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂

theorem reachable_preserves_branch {a b : Archetype}
    (h : Reachable a b) : branch a = branch b := by
  induction h with
  | refl => rfl
  | step edge => exact edge_preserves_branch edge
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

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
    (h : PositivePath a a) : False := by
  have hstrict : rank a < rank a := by
    induction h with
    | edge e => exact edge_rank_strict e
    | tail hab hbc ih =>
        exact lt_of_lt_of_le ih (reachable_rank_monotone hbc)
  exact (Nat.lt_irrefl _ hstrict)

theorem reachability_is_partial_order :
    (∀ a : Archetype, Reachable a a) ∧
    (∀ {a b c : Archetype}, Reachable a b → Reachable b c → Reachable a c) ∧
    (∀ {a b : Archetype}, Reachable a b → Reachable b a → a = b) := by
  exact ⟨reachable_refl, fun _ _ => reachable_trans,
    fun hab hba => reachable_antisymm hab hba⟩

theorem archetype_partial_order :
    ∀ {a b : Archetype}, Reachable a b → Reachable b a → a = b :=
  fun _ _ hab hba => reachable_antisymm hab hba

theorem branch_incomparable {a b : Archetype}
    (hne : branch a ≠ branch b) :
    ¬ Reachable a b ∨ ¬ Reachable b a := by
  left
  intro hab
  exact hne (reachable_preserves_branch hab)

theorem branch_no_reach {a b : Archetype}
    (hne : branch a ≠ branch b) :
    ¬ Reachable a b ∧ ¬ Reachable b a := by
  constructor <;> intro h <;>
    exact hne (reachable_preserves_branch h)

theorem volume_and_krein_projectors_incomparable :
    ¬ Reachable .volumePeirceProjectors .diagonalKreinProjectors ∧
    ¬ Reachable .diagonalKreinProjectors .volumePeirceProjectors := by
  constructor <;> intro h <;>
    have hb := reachable_preserves_branch h <;> simp [branch] at hb

theorem real_split_and_complex_matrix_limits_incomparable :
    ¬ Reachable .splitTensorDirectLimit .matrixLimitTrace ∧
    ¬ Reachable .matrixLimitTrace .splitTensorDirectLimit := by
  exact branch_no_reach (by decide)

theorem concrete_and_generic_five_grade_incomparable :
    ¬ Reachable .concreteFiveGradeQuintic .genericFiveGradeSocket ∧
    ¬ Reachable .genericFiveGradeSocket .concreteFiveGradeQuintic := by
  exact branch_no_reach (by decide)

theorem cl12_candidate_and_matrix_relations_incomparable :
    ¬ Reachable .nativeCl12EquivalenceCandidate .cl12MatrixGeneratorRelations ∧
    ¬ Reachable .cl12MatrixGeneratorRelations .nativeCl12EquivalenceCandidate := by
  exact branch_no_reach (by decide)

instance : PartialOrder Archetype where
  le := Reachable
  le_refl := reachable_refl
  le_trans := fun _ _ _ hab hbc => reachable_trans hab hbc
  le_antisymm := fun _ _ hab hba => reachable_antisymm hab hba

end InfoGeometry.Scratch.CanonicalNoncommutativeArchetypePoset
