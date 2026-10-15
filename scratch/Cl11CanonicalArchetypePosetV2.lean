import InfoGeometry.Clifford.CockleCoquaternionPlanarTriad
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11GeometricSynthesis
import InfoGeometry.Clifford.SplitQ11CausalCone
import InfoGeometry.Clifford.Cl11GeometricBiquaternionBridge
import InfoGeometry.Clifford.Cl11SplitQuaternions

/-!
Finite evidence-carrying dependency poset for the Cl(1,1)/geometric-biquaternion
archetypes represented by the imported owner declarations. The raw coquaternion
elements and normalized real-matrix projectors are distinct nodes; likewise the
native Clifford equivalence and the doubled-real matrix map remain distinct.
-/

namespace InfoGeometry.Clifford.Cl11CanonicalArchetypePosetV2

open InfoGeometry.Clifford.Coquaternion.Coquaternion

private abbrev Coq := InfoGeometry.Clifford.Coquaternion.Coquaternion
private abbrev B := InfoGeometry.Clifford.GeometricBiquaternion.Biquat


/-- The finite node set used by this poset. -/
inductive Archetype where
  | splitAlgebra
  | generatorRelations
  | planarTriad
  | planarMultiplication
  | chiralGrading
  | rawOrthogonalPair
  | coquaternionMatrixMap
  | nativeCliffordMatrixEquivalence
  | synthesisMatrixModel
  | normalizedMatrixPeirce
  | nullRayProducts
  | kreinProjectorPair
  | causalNullHopClosure
  | spinorKreinAction
  | geometricBiquaternionCarrier
  | centralI3Extension
  | complexCliffordMatrixGenerators
  | doubledRealMatrixMap
  deriving DecidableEq, Repr


theorem synthesis_e1_eq_native :
    InfoGeometry.Clifford.Cl11GeometricSynthesis.e1 =
      InfoGeometry.Clifford.Cl11Matrix.Eplus := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem synthesis_e2_eq_native :
    InfoGeometry.Clifford.Cl11GeometricSynthesis.e2 =
      InfoGeometry.Clifford.Cl11Matrix.Eminus := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem synthesis_omega_eq_native :
    InfoGeometry.Clifford.Cl11GeometricSynthesis.omega =
      InfoGeometry.Clifford.Cl11Matrix.J1 := by
  rw [← InfoGeometry.Clifford.Cl11GeometricSynthesis.e1_mul_e2,
    synthesis_e1_eq_native, synthesis_e2_eq_native,
    InfoGeometry.Clifford.Cl11Matrix.Eplus_mul_Eminus]

/-- Typed direct edges carry actual propositions witnessed by imported owner
theorems. Their direction records prerequisite-to-consequence dependency. -/
inductive EvidenceEdge : Archetype → Archetype → Prop where
  | algebra_generator_relations
      (h : (e1 : Coq ℝ) * e1 = 1 ∧
        (e2 : Coq ℝ) * e2 = -1 ∧
        (e1 : Coq ℝ) * e2 + e2 * e1 = 0) :
      EvidenceEdge .splitAlgebra .generatorRelations
  | generators_planar_triad
      (h : (i_unit : Coq ℝ) * i_unit = -1 ∧
        (j_unit : Coq ℝ) * j_unit = 1 ∧
        (epsilon : Coq ℝ) * epsilon = 0) :
      EvidenceEdge .generatorRelations .planarTriad
  | synthesis_planar_multiplication
      (h : ∀ a b c d : ℝ,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.elliptic_elem a b *
            InfoGeometry.Clifford.Cl11GeometricSynthesis.elliptic_elem c d =
          InfoGeometry.Clifford.Cl11GeometricSynthesis.elliptic_elem (a * c - b * d) (a * d + b * c) ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.hyperbolic_elem a b *
            InfoGeometry.Clifford.Cl11GeometricSynthesis.hyperbolic_elem c d =
          InfoGeometry.Clifford.Cl11GeometricSynthesis.hyperbolic_elem (a * c + b * d) (a * d + b * c) ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.parabolic_elem a b *
            InfoGeometry.Clifford.Cl11GeometricSynthesis.parabolic_elem c d =
          InfoGeometry.Clifford.Cl11GeometricSynthesis.parabolic_elem (a * c) (a * d + b * c)) :
      EvidenceEdge .synthesisMatrixModel .planarMultiplication
  | generators_chiral_grading
      (h : ∀ q : Coq ℝ,
        chiralGrading * evenPart q * chiralGrading = evenPart q ∧
        chiralGrading * oddPart q * chiralGrading = -oddPart q) :
      EvidenceEdge .generatorRelations .chiralGrading
  | grading_raw_pair
      (h : (P_plus_raw : Coq ℝ) * P_minus_raw = 0 ∧
        (P_minus_raw : Coq ℝ) * P_plus_raw = 0 ∧
        (P_plus_raw : Coq ℝ) * P_plus_raw = ⟨2, 0, 0, 2⟩ ∧
        (P_minus_raw : Coq ℝ) * P_minus_raw = ⟨2, 0, 0, -2⟩) :
      EvidenceEdge .chiralGrading .rawOrthogonalPair
  | coquaternion_matrix_map
      (h : (∀ p q : Coq ℝ,
          InfoGeometry.Clifford.Coquaternion.Coquaternion.toMatrix (p * q) =
            InfoGeometry.Clifford.Coquaternion.Coquaternion.toMatrix p *
              InfoGeometry.Clifford.Coquaternion.Coquaternion.toMatrix q) ∧
        ∀ q : Coq ℝ,
          InfoGeometry.Clifford.Coquaternion.Coquaternion.det2
              (InfoGeometry.Clifford.Coquaternion.Coquaternion.toMatrix q) =
            InfoGeometry.Clifford.Coquaternion.Coquaternion.normSq q) :
      EvidenceEdge .splitAlgebra .coquaternionMatrixMap
  | native_clifford_matrix
      (h : Nonempty (CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 ≃ₐ[ℝ]
        InfoGeometry.Clifford.Cl11Matrix.Mat2)) :
      EvidenceEdge .generatorRelations .nativeCliffordMatrixEquivalence
  | native_to_synthesis_matrices
      (h : InfoGeometry.Clifford.Cl11GeometricSynthesis.e1 =
          InfoGeometry.Clifford.Cl11Matrix.Eplus ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.e2 =
          InfoGeometry.Clifford.Cl11Matrix.Eminus ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.omega =
          InfoGeometry.Clifford.Cl11Matrix.J1) :
      EvidenceEdge .nativeCliffordMatrixEquivalence .synthesisMatrixModel
  | synthesis_normalized_peirce
      (h : InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus *
          InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus =
            InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus *
          InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus =
            InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus *
          InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus = 0 ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus *
          InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus = 0 ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus +
          InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus =
            InfoGeometry.Clifford.Cl11GeometricSynthesis.one) :
      EvidenceEdge .synthesisMatrixModel .normalizedMatrixPeirce
  | synthesis_null_ray_products
      (h : InfoGeometry.Clifford.Cl11GeometricSynthesis.n_plus *
          InfoGeometry.Clifford.Cl11GeometricSynthesis.n_plus = 0 ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.n_minus *
          InfoGeometry.Clifford.Cl11GeometricSynthesis.n_minus = 0 ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.n_plus *
          InfoGeometry.Clifford.Cl11GeometricSynthesis.n_minus =
            (4 : ℝ) • InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus ∧
        InfoGeometry.Clifford.Cl11GeometricSynthesis.n_minus *
          InfoGeometry.Clifford.Cl11GeometricSynthesis.n_plus =
            (4 : ℝ) • InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus) :
      EvidenceEdge .synthesisMatrixModel .nullRayProducts
  | krein_projector_laws
      (h : InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinPlusProjector = !![(1 : ℝ), 0; 0, 0] ∧
           InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinMinusProjector = !![0, 0; 0, (1 : ℝ)]) :
      EvidenceEdge .nativeCliffordMatrixEquivalence .kreinProjectorPair
  | krein_projector_null_hops
      (h : InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus *
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus = 0 ∧
           InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus *
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus = 0 ∧
           InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus *
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus =
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinPlusProjector ∧
           InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus *
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus =
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinMinusProjector ∧
           InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus *
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus +
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus *
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus =
             (1 : InfoGeometry.Clifford.Cl11Matrix.Mat2) ∧
           InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus *
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus -
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullMinus *
             InfoGeometry.Clifford.SplitQ11CausalCone.matrixCausalNullPlus =
             InfoGeometry.Clifford.Cl11Matrix.Eplus) :
      EvidenceEdge .kreinProjectorPair .causalNullHopClosure
  | krein_projector_spinor_action
      (h : ∀ ψ : InfoGeometry.Clifford.SplitQ11CausalCone.Spinor2,
        InfoGeometry.Clifford.SplitQ11CausalCone.matrixAct
          InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinPlusProjector ψ 0 =
            ψ 0 ∧
        InfoGeometry.Clifford.SplitQ11CausalCone.matrixAct
          InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinPlusProjector ψ 1 =
            0 ∧
        InfoGeometry.Clifford.SplitQ11CausalCone.matrixAct
          InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinMinusProjector ψ 0 =
            0 ∧
        InfoGeometry.Clifford.SplitQ11CausalCone.matrixAct
          InfoGeometry.Clifford.SplitQ11CausalCone.matrixKreinMinusProjector ψ 1 =
            ψ 1) :
      EvidenceEdge .kreinProjectorPair .spinorKreinAction
  | algebra_biquaternion_extension
      (h : ∀ q : Coq ℝ,
        (InfoGeometry.Clifford.GeometricBiquaternion.Biquat.ofCoquaternion q).re = q ∧
        (InfoGeometry.Clifford.GeometricBiquaternion.Biquat.ofCoquaternion q).im = 0) :
      EvidenceEdge .splitAlgebra .geometricBiquaternionCarrier
  | biquaternion_central_i3
      (h : (InfoGeometry.Clifford.GeometricBiquaternion.Biquat.I3 : B ℝ) *
          InfoGeometry.Clifford.GeometricBiquaternion.Biquat.I3 = -1 ∧
        ∀ q : Coq ℝ,
          (InfoGeometry.Clifford.GeometricBiquaternion.Biquat.I3 : B ℝ) *
              InfoGeometry.Clifford.GeometricBiquaternion.Biquat.ofCoquaternion q =
            InfoGeometry.Clifford.GeometricBiquaternion.Biquat.ofCoquaternion q *
              InfoGeometry.Clifford.GeometricBiquaternion.Biquat.I3) :
      EvidenceEdge .geometricBiquaternionCarrier .centralI3Extension
  | central_i3_doubled_matrix
      (h : ∀ p q : B ℝ,
        InfoGeometry.Clifford.GeometricBiquaternion.Biquat.toMatrix4 (p * q) =
          InfoGeometry.Clifford.GeometricBiquaternion.Biquat.toMatrix4 p *
            InfoGeometry.Clifford.GeometricBiquaternion.Biquat.toMatrix4 q) :
      EvidenceEdge .centralI3Extension .doubledRealMatrixMap
  | complex_matrix_generators
      (h : InfoGeometry.Clifford.Cl11.I_3D * InfoGeometry.Clifford.Cl11.I_3D =
            -(1 : InfoGeometry.Clifford.Cl11.Mat2C) ∧
        ∀ M : InfoGeometry.Clifford.Cl11.Mat2C,
          InfoGeometry.Clifford.Cl11.I_3D * M = M * InfoGeometry.Clifford.Cl11.I_3D ∧
        InfoGeometry.Clifford.Cl11.e₁C * InfoGeometry.Clifford.Cl11.e₁C = 1 ∧
        InfoGeometry.Clifford.Cl11.e₂C * InfoGeometry.Clifford.Cl11.e₂C = -1 ∧
        InfoGeometry.Clifford.Cl11.fC * InfoGeometry.Clifford.Cl11.fC = -1) :
      EvidenceEdge .centralI3Extension .complexCliffordMatrixGenerators

/-- The edge witnesses are supplied by the canonical owner declarations. -/
theorem owner_edges :
    EvidenceEdge .splitAlgebra .generatorRelations ∧
    EvidenceEdge .generatorRelations .planarTriad ∧
    EvidenceEdge .synthesisMatrixModel .planarMultiplication ∧
    EvidenceEdge .generatorRelations .chiralGrading ∧
    EvidenceEdge .chiralGrading .rawOrthogonalPair ∧
    EvidenceEdge .splitAlgebra .coquaternionMatrixMap ∧
    EvidenceEdge .generatorRelations .nativeCliffordMatrixEquivalence ∧
    EvidenceEdge .nativeCliffordMatrixEquivalence .synthesisMatrixModel ∧
    EvidenceEdge .synthesisMatrixModel .normalizedMatrixPeirce ∧
    EvidenceEdge .synthesisMatrixModel .nullRayProducts ∧
    EvidenceEdge .nativeCliffordMatrixEquivalence .kreinProjectorPair ∧
    EvidenceEdge .kreinProjectorPair .causalNullHopClosure ∧
    EvidenceEdge .kreinProjectorPair .spinorKreinAction ∧
    EvidenceEdge .splitAlgebra .geometricBiquaternionCarrier ∧
    EvidenceEdge .geometricBiquaternionCarrier .centralI3Extension ∧
    EvidenceEdge .centralI3Extension .complexCliffordMatrixGenerators ∧
    EvidenceEdge .centralI3Extension .doubledRealMatrixMap := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact .algebra_generator_relations ⟨e1_sq, e2_sq, anticomm_e1_e2⟩
  · exact .generators_planar_triad (planar_triad_coexistence (R := ℝ))
  · exact .synthesis_planar_multiplication (fun a b c d =>
      ⟨InfoGeometry.Clifford.Cl11GeometricSynthesis.elliptic_mul a b c d,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.hyperbolic_mul a b c d,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.parabolic_mul a b c d⟩)
  · exact .generators_chiral_grading (fun q =>
      ⟨chiral_grading_even q, chiral_grading_odd q⟩)
  · exact .grading_raw_pair ⟨P_plus_mul_P_minus, P_minus_mul_P_plus,
      P_plus_sq, P_minus_sq⟩
  · exact .coquaternion_matrix_map
      ⟨InfoGeometry.Clifford.Coquaternion.Coquaternion.toMatrix_mul,
        InfoGeometry.Clifford.Coquaternion.Coquaternion.toMatrix_det⟩
  · exact .native_clifford_matrix
      ⟨InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat⟩
  · exact .native_to_synthesis_matrices
      ⟨synthesis_e1_eq_native, synthesis_e2_eq_native, synthesis_omega_eq_native⟩
  · exact .synthesis_normalized_peirce
      ⟨InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus_sq,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus_sq,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus_mul_P_minus,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_minus_mul_P_plus,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.P_plus_add_P_minus⟩
  · exact .synthesis_null_ray_products
      ⟨InfoGeometry.Clifford.Cl11GeometricSynthesis.n_plus_sq,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.n_minus_sq,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.n_plus_mul_n_minus,
        InfoGeometry.Clifford.Cl11GeometricSynthesis.n_minus_mul_n_plus⟩
  · exact .krein_projector_laws
      InfoGeometry.Clifford.SplitQ11CausalCone.matrix_krein_projectors_explicit
  · exact .krein_projector_null_hops
      InfoGeometry.Clifford.SplitQ11CausalCone.matrix_causal_null_closure_laws
  · exact .krein_projector_spinor_action
      InfoGeometry.Clifford.SplitQ11CausalCone.matrix_projector_spinor_action
  · exact .algebra_biquaternion_extension (fun _ => ⟨rfl, rfl⟩)
  · exact .biquaternion_central_i3
      ⟨InfoGeometry.Clifford.GeometricBiquaternion.Biquat.I3_sq,
        InfoGeometry.Clifford.GeometricBiquaternion.Biquat.I3_comm_coquaternion⟩
  · exact .complex_matrix_generators
      ⟨InfoGeometry.Clifford.Cl11.I_3D_sq,
        fun M => ⟨InfoGeometry.Clifford.Cl11.I_3D_comm M,
          InfoGeometry.Clifford.Cl11.e₁C_sq,
          InfoGeometry.Clifford.Cl11.e₂C_sq,
          InfoGeometry.Clifford.Cl11.fC_sq⟩⟩
  · exact .central_i3_doubled_matrix
      InfoGeometry.Clifford.GeometricBiquaternion.Biquat.toMatrix4_mul

def layer : Archetype → Nat
  | .splitAlgebra => 0
  | .generatorRelations => 1
  | .planarTriad => 2
  | .planarMultiplication => 4
  | .chiralGrading => 2
  | .rawOrthogonalPair => 3
  | .coquaternionMatrixMap => 1
  | .nativeCliffordMatrixEquivalence => 2
  | .synthesisMatrixModel => 3
  | .normalizedMatrixPeirce => 4
  | .nullRayProducts => 4
  | .kreinProjectorPair => 3
  | .causalNullHopClosure => 4
  | .spinorKreinAction => 4
  | .geometricBiquaternionCarrier => 1
  | .centralI3Extension => 2
  | .complexCliffordMatrixGenerators => 3
  | .doubledRealMatrixMap => 3

private theorem layer_lt_edge {a b : Archetype} (h : EvidenceEdge a b) :
    layer a < layer b := by
  cases h <;> simp [layer]

/-- Reflexive-transitive reachability generated by evidence-carrying edges. -/
inductive Reach : Archetype → Archetype → Prop where
  | refl (a) : Reach a a
  | step {a b c} : EvidenceEdge a b → Reach b c → Reach a c

theorem reach_trans {a b c : Archetype} (hab : Reach a b) (hbc : Reach b c) :
    Reach a c := by
  induction hab generalizing c with
  | refl => exact hbc
  | step h rest ih => exact .step h (ih hbc)

private theorem layer_le_reach {a b : Archetype} (h : Reach a b) :
    layer a ≤ layer b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step edge rest ih => exact (layer_lt_edge edge).le.trans ih

private theorem layer_lt_reach_of_ne {a b : Archetype} (h : Reach a b)
    (hne : a ≠ b) : layer a < layer b := by
  induction h with
  | refl => exact False.elim (hne rfl)
  | step edge rest ih =>
      exact (layer_lt_edge edge).trans_le (layer_le_reach rest)

instance : PartialOrder Archetype where
  le := Reach
  le_refl := Reach.refl
  le_trans := fun _ _ _ hab hbc => reach_trans hab hbc
  le_antisymm := by
    intro a b hab hba
    by_contra hne
    exact (Nat.not_lt_of_ge (layer_lt_reach_of_ne hba (Ne.symm hne)).le)
      (layer_lt_reach_of_ne hab hne)

theorem reach_acyclic {a b : Archetype} (hab : Reach a b) (hba : Reach b a) :
    a = b := le_antisymm hab hba

end InfoGeometry.Clifford.Cl11CanonicalArchetypePosetV2
