import InfoGeometry.Attention.MetriplecticAttentionDynamics
import InfoGeometry.Attention.CurvatureHolonomyLieBracket
import InfoGeometry.Attention.MultiHeadSymplecticReduction
import InfoGeometry.Attention.AttentionMetriplecticPoset
import InfoGeometry.Attention.AttentionCurvatureHolonomy
import InfoGeometry.Attention.ResidualMetriplecticFlow
import InfoGeometry.Attention.ContinuousLyapunovFlow
import InfoGeometry.Attention.SymplecticDefectInvariance
import InfoGeometry.Automorphic.ModularMetriplecticDual
import InfoGeometry.NumberTheory.ZagierMellinMatrix
import InfoGeometry.Motivic.PolylogarithmicUnipotentMotive

namespace InfoGeometry.Attention.MetriplecticAttentionTests

open Matrix
open InfoGeometry.Attention.MetriplecticAttentionDynamics
open InfoGeometry.Attention.CurvatureHolonomyLieBracket
open InfoGeometry.Attention.MultiHeadSymplecticReduction
open InfoGeometry.Attention.AttentionMetriplecticPoset
open InfoGeometry.Motivic.PolylogarithmicUnipotentMotive

/-- Concrete test matrix representing a normalized softmax attention head. -/
def testSoftmaxMatrix : Mat2R :=
  !![0.6, 0.4;
     0.3, 0.7]

/-- Test 1: Metriplectic splitting on concrete matrix. -/
theorem test_metriplectic_split :
    testSoftmaxMatrix = diag_core testSoftmaxMatrix + chiral_bipolar testSoftmaxMatrix := by
  exact metriplectic_operator_split testSoftmaxMatrix

/-- Test 2: Frobenius orthogonality on concrete matrix. -/
theorem test_frobenius_orthogonality :
    frobenius_inner (diag_core testSoftmaxMatrix) (chiral_bipolar testSoftmaxMatrix) = 0 := by
  exact dissipative_chiral_orthogonal testSoftmaxMatrix

/-- Test 3: Casimir trace invariance on concrete matrix. -/
theorem test_casimir_invariance :
    Matrix.trace (G_grading * chiral_bipolar testSoftmaxMatrix) = 0 := by
  exact chiral_transport_casimir_invariant testSoftmaxMatrix

/-- Test 4: Positive entropy trace for softmax. -/
theorem test_positive_entropy_trace :
    0 < Matrix.trace (diag_core testSoftmaxMatrix) := by
  apply softmax_trace_strictly_positive
  · norm_num [testSoftmaxMatrix]
  · norm_num [testSoftmaxMatrix]

/-- Test 5: Concrete curvature commutator evaluated against area form. -/
def testMatrix2 : Mat2R :=
  !![0.5, 0.2;
     0.8, 0.5]

theorem test_curvature_commutator :
    bracket (chiral_bipolar testSoftmaxMatrix) (chiral_bipolar testMatrix2) =
    (CurvatureHolonomyLieBracket.symplectic_area testSoftmaxMatrix testMatrix2) • G_grading := by
  exact bipolar_commutator_eq_symplectic_area_grading testSoftmaxMatrix testMatrix2

/-- Test 6: Symplectic structure squaring to -1. -/
theorem test_J_symp_sq : J_symp * J_symp = - 1 :=
  J_symp_sq

/-- Test 7: Causal root theorem for the poset. -/
theorem test_metriplectic_root :
    metriplecticSplit ≤ MetriplecticArchetype.multiHeadSymplecticReduction := by
  exact metriplecticSplit_is_root _

/-- Test 8: Residual step represented by propagator multiplication. -/
theorem test_residual_step (x : Fin 2 → ℝ) :
    ResidualMetriplecticFlow.residual_step testSoftmaxMatrix x =
    (ResidualMetriplecticFlow.layer_propagator testSoftmaxMatrix) *ᵥ x := by
  exact ResidualMetriplecticFlow.residual_step_eq_propagator_mul testSoftmaxMatrix x

/-- Test 9: Energy change formula on residual step. -/
theorem test_residual_energy_change (x : Fin 2 → ℝ) :
    ResidualMetriplecticFlow.energy_change testSoftmaxMatrix x =
    2 * ResidualMetriplecticFlow.dot_product x (testSoftmaxMatrix *ᵥ x) +
    ResidualMetriplecticFlow.norm_sq (testSoftmaxMatrix *ᵥ x) := by
  exact ResidualMetriplecticFlow.residual_energy_change_exact testSoftmaxMatrix x

/-- Test 10: Curvature squaring to scalar invariant. -/
theorem test_holonomy_square_scalar :
    (AttentionCurvatureHolonomy.commutator (AttentionCurvatureHolonomy.chiral_bipolar testSoftmaxMatrix)
      (AttentionCurvatureHolonomy.chiral_bipolar testMatrix2)) *
    (AttentionCurvatureHolonomy.commutator (AttentionCurvatureHolonomy.chiral_bipolar testSoftmaxMatrix)
      (AttentionCurvatureHolonomy.chiral_bipolar testMatrix2)) =
    ((AttentionCurvatureHolonomy.symplectic_area testSoftmaxMatrix testMatrix2) ^ 2) • (1 : Mat2R) := by
  exact AttentionCurvatureHolonomy.chiral_curvature_sq_scalar testSoftmaxMatrix testMatrix2

/-!
# Regression Tests: Dynamical Residual Flow & Energy Flux Separation
-/

/-- Test Matrix 1: Balanced Skew-Symmetric Cross-Attention (m = 2, M₀₁ = 2, M₁₀ = -2).
    Diagonal dissipation entries: M₀₀ = -0.5, M₁₁ = -0.3. -/
def M_test_skew : Mat2R :=
  !![-0.5,  2.0;
     -2.0, -0.3]

/-- Test State vector x = (3, 4). -/
def x_test : Fin 2 → ℝ := ![3.0, 4.0]

/-- Test 11: Verification of Pure Diagonal Linear Energy Flux. -/
theorem test_linear_energy_flux_evaluation :
    ResidualMetriplecticFlow.dot_product x_test (M_test_skew *ᵥ x_test) = -9.3 := by
  have h_skew : M_test_skew 0 1 = - M_test_skew 1 0 := by
    dsimp [M_test_skew]
    ring
  rw [ResidualMetriplecticFlow.linear_energy_flux_is_purely_diagonal M_test_skew x_test h_skew]
  dsimp [M_test_skew, x_test]
  ring

/-- Test 12: Verification of Exact Total Energy Change (ΔE = 2⟨x, Mx⟩ + ‖Mx‖²). -/
theorem test_residual_energy_change_exact_evaluation :
    ResidualMetriplecticFlow.energy_change M_test_skew x_test =
    2 * ResidualMetriplecticFlow.dot_product x_test (M_test_skew *ᵥ x_test) +
    ResidualMetriplecticFlow.norm_sq (M_test_skew *ᵥ x_test) := by
  exact ResidualMetriplecticFlow.residual_energy_change_exact M_test_skew x_test

/-- Test 13: Verification of the Propagator Trace Casimir Invariance.
    tr(G · T(M)) = M₀₀ - M₁₁ = -0.5 - (-0.3) = -0.2. -/
theorem test_propagator_casimir_trace_evaluation :
    Matrix.trace (G_grading * ResidualMetriplecticFlow.layer_propagator M_test_skew) = -0.2 := by
  rw [ResidualMetriplecticFlow.residual_propagator_casimir_trace M_test_skew]
  dsimp [M_test_skew]
  ring

/-- Test 14: Verification of Work-Free Chiral Transport.
    ⟨x, C(M)x⟩ = 0 for the skew-symmetric cross-coupling. -/
theorem test_chiral_transport_work_free :
    ResidualMetriplecticFlow.dot_product x_test (ResidualMetriplecticFlow.chiral_bipolar M_test_skew *ᵥ x_test) = 0 := by
  have h_skew : M_test_skew 0 1 = - M_test_skew 1 0 := by
    dsimp [M_test_skew]
    ring
  exact ResidualMetriplecticFlow.chiral_transport_orthogonal_to_state M_test_skew x_test h_skew

/-- Test 15: Continuous Lyapunov strictly negative decay rate. -/
theorem test_continuous_lyapunov_strictly_negative :
    ∀ (dV norm_val α : ℝ),
      dV ≤ -2 * α * norm_val →
      0 < α →
      0 < norm_val →
      dV < 0 :=
  ContinuousLyapunovFlow.continuous_lyapunov_strictly_negative

theorem test_motivic_causal_chain :
    polylogOne ≤ oddsRatioDeriv ∧
    oddsRatioDeriv ≤ motivicNilpotent ∧
    motivicNilpotent ≤ dilogarithmSeam ∧
    dilogarithmSeam ≤ carnotShannonUnification := by
  exact motivic_chain

theorem test_motivic_connection_cubed_zero (ω₀ ω₁ : ℝ) :
    (PolylogarithmicUnipotentMotive.connection ω₀ ω₁) ^ 3 = 0 := by
  exact PolylogarithmicUnipotentMotive.connection_cubed_zero ω₀ ω₁

theorem test_motivic_seam_identity :
    PolylogarithmicUnipotentMotive.seamValue =
      (Real.pi ^ 2 / 2) * (1 / 6) - (1 / 2) * (Real.log 2) ^ 2 := by
  exact PolylogarithmicUnipotentMotive.seam_value_as_carnot_shannon

/-!
# Regression Tests: Symplectic Defect Invariance, Gross-Zagier Mass & Zagier Mellin Matrix
-/

/-- Test Matrix with distinct non-symmetric entries. -/
def A_test : Mat2R :=
  !![0.8, 0.4;
     0.2, 0.6]

-- Test 16: Verification of the Fundamental Symplectic Defect Identity
theorem test_symplectic_defect_identity_numeric :
    A_testᵀ * SymplecticDefectInvariance.J_symp + SymplecticDefectInvariance.J_symp * A_test =
    (Matrix.trace A_test) • SymplecticDefectInvariance.J_symp := by
  exact SymplecticDefectInvariance.transpose_mul_J_add_J_mul A_test

-- Test 17: Traceless projection belongs strictly to sp(2, ℝ)
theorem test_traceless_projection_is_symplectic :
    (SymplecticDefectInvariance.traceless_proj A_test)ᵀ * SymplecticDefectInvariance.J_symp +
    SymplecticDefectInvariance.J_symp * (SymplecticDefectInvariance.traceless_proj A_test) = 0 := by
  exact SymplecticDefectInvariance.traceless_proj_is_symplectic A_test

-- Test 18: Concrete Tetrad Coordinates Reconstruction
theorem test_tetrad_decomposition_numeric :
    let c0 : ℝ := 0.7
    let c1 : ℝ := 0.1
    let c2 : ℝ := 0.3
    let c3 : ℝ := 0.1
    A_test = c0 • SymplecticDefectInvariance.I_2 +
             c1 • SymplecticDefectInvariance.G_grading +
             c2 • SymplecticDefectInvariance.C_symm +
             c3 • SymplecticDefectInvariance.J_symp := by
  intro c0 c1 c2 c3
  dsimp [A_test, c0, c1, c2, c3, SymplecticDefectInvariance.I_2,
         SymplecticDefectInvariance.G_grading, SymplecticDefectInvariance.C_symm,
         SymplecticDefectInvariance.J_symp]
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
               cons_val_zero, cons_val_one, head_cons]
    ring
  }

-- Test 19: Gross-Zagier odd functional equation central vanishing
theorem test_gross_zagier_central_zero (Λ : ℝ → ℝ)
    (h_odd : Automorphic.ModularMetriplecticDual.HasOddFunctionalEquation Λ) :
    Λ (1 / 2) = 0 :=
  Automorphic.ModularMetriplecticDual.odd_functional_equation_vanishes_at_half Λ h_odd

-- Test 20: Zagier matrix pencil inverse identity
theorem test_zagier_matrix_pencil_inverse (t : ℝ) :
    NumberTheory.ZagierMellinMatrix.matrix_pencil t * NumberTheory.ZagierMellinMatrix.resolvent_candidate t = 1 :=
  NumberTheory.ZagierMellinMatrix.matrix_pencil_inverse t

#print axioms metriplectic_operator_split
#print axioms dissipative_chiral_orthogonal
#print axioms chiral_transport_casimir_invariant
#print axioms metriplectic_dirac_dispersion
#print axioms bipolar_commutator_eq_symplectic_area_grading
#print axioms dirac_hamiltonian_is_infinitesimal_symplectic
#print axioms ResidualMetriplecticFlow.residual_step_eq_propagator_mul
#print axioms ResidualMetriplecticFlow.linear_energy_flux_is_purely_diagonal
#print axioms AttentionCurvatureHolonomy.chiral_curvature_sq_scalar
#print axioms ContinuousLyapunovFlow.deriv_norm_sq_eq_two_dot
#print axioms ContinuousLyapunovFlow.continuous_lyapunov_derivative_le
#print axioms SymplecticDefectInvariance.transpose_mul_J_add_J_mul
#print axioms SymplecticDefectInvariance.operator_tetrad_decomposition
#print axioms Automorphic.ModularMetriplecticDual.gross_zagier_dirac_mass_shell
#print axioms NumberTheory.ZagierMellinMatrix.matrix_pencil_inverse

end InfoGeometry.Attention.MetriplecticAttentionTests
