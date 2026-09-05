import InfoGeometry.Physics.NuclearWignerSupermultipletSymmetry
import InfoGeometry.Algebra.AffineOperatorFrame
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Spin affine frames: Casimir identities and the obstruction to squeezing

The spin matrices and ladders are the existing nuclear Wigner SU(2) owner.
We do not construct another Pauli basis. We prove exactly which complex
Bogoliubov-shaped ladder changes preserve the full fixed-Cartan relations.

The scalar rho-shift identities below are not a construction of the
Harish-Chandra isomorphism or a classification of the enveloping center.
-/

noncomputable section

namespace InfoGeometry.Physics.SpinAffineCasimirRigidity

open InfoGeometry.Physics.NuclearWignerSupermultiplet
open InfoGeometry.Algebra.AffineOperatorFrame
open scoped BigOperators

abbrev SpinMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- The indexed Cartesian frame uses the already installed Pauli matrices. -/
def spinFrame : Fin 3 → SpinMatrix :=
  ![(1 / 2 : ℂ) • pauli1, (1 / 2 : ℂ) • pauli2, isospin3]

theorem spinFrame_casimir : sumSquares spinFrame =
    (3 / 4 : ℂ) • (1 : SpinMatrix) := by
  simpa [sumSquares, spinFrame, isospin3, Fin.sum_univ_three] using isospin_casimir

/-- Spin-weight normalization: rho is one half in the S_z coordinate. -/
theorem casimir_rho_shift (s : ℂ) :
    s * (s + 1) = (s + 1 / 2) ^ 2 - 1 / 4 := by ring

theorem casimir_dot_reflection (s : ℂ) :
    (-s - 1) * ((-s - 1) + 1) = s * (s + 1) := by ring

theorem dot_reflection_involutive (s : ℂ) : -(-s - 1) - 1 = s := by ring

/-- The operator Casimir normalization agrees with the actual existing ladder matrices. -/
theorem spin_half_ladder_casimir :
    isospin3 * isospin3 + isospin3 + isospinMinus * isospinPlus =
      (3 / 4 : ℂ) • (1 : SpinMatrix) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [isospin3, isospinMinus, isospinPlus, pauli1, pauli2, pauli3,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- General affine inversion recovers this exact spin Casimir. -/
theorem affine_spin_casimir (M : FrameMatrixˣ) (b : Fin 3 → ℝ) :
    operatorQuadratic
      ((↑(M⁻¹) : FrameMatrix).transpose * (↑(M⁻¹) : FrameMatrix))
      (affineFrame (↑M) b spinFrame - centralOffset b) =
        (3 / 4 : ℂ) • (1 : SpinMatrix) := by
  rw [inverse_metric_quadratic, spinFrame_casimir]

/-- Bogoliubov-shaped mixing of the existing spin raising/lowering operators. -/
def mixedPlus (u v : ℂ) : SpinMatrix := u • isospinPlus + v • isospinMinus

def mixedMinus (u v : ℂ) : SpinMatrix := star v • isospinPlus + star u • isospinMinus

/-- The ladder-ladder bracket alone only tests the indefinite coefficient norm. -/
theorem mixed_ladder_bracket (u v : ℂ) :
    mixedPlus u v * mixedMinus u v - mixedMinus u v * mixedPlus u v =
      ((Complex.normSq u - Complex.normSq v : ℝ) : ℂ) • ((2 : ℂ) • isospin3) := by
  funext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [mixedPlus, mixedMinus, isospinPlus, isospinMinus, isospin3,
      pauli1, pauli2, pauli3, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

/-- The omitted Cartan bracket has a nonzero lowering component. -/
theorem mixed_cartan_defect (u v : ℂ) :
    isospin3 * mixedPlus u v - mixedPlus u v * isospin3 - mixedPlus u v =
      (-2 * v) • isospinMinus := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedPlus, isospinPlus, isospinMinus, isospin3,
      pauli1, pauli2, pauli3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Exact no-squeeze theorem for a fixed spin Cartan: mixing must vanish. -/
theorem mixed_cartan_iff (u v : ℂ) :
    isospin3 * mixedPlus u v - mixedPlus u v * isospin3 = mixedPlus u v ↔ v = 0 := by
  constructor
  · intro h
    have hd := mixed_cartan_defect u v
    rw [h, sub_self] at hd
    have hv := congrArg (fun X : SpinMatrix => X 1 0) hd
    norm_num [isospinMinus, pauli1, pauli2, Matrix.mul_apply, Fin.sum_univ_two] at hv
    linear_combination (1 / 2 : ℂ) * hv
  · rintro rfl
    have hd := mixed_cartan_defect u 0
    simpa only [mul_zero, zero_smul, sub_eq_zero] using hd

/-- Within this ansatz, both independent relations force only a phase rotation. -/
theorem fixed_cartan_spin_relations_iff (u v : ℂ) :
    (isospin3 * mixedPlus u v - mixedPlus u v * isospin3 = mixedPlus u v ∧
      mixedPlus u v * mixedMinus u v - mixedMinus u v * mixedPlus u v =
        (2 : ℂ) • isospin3) ↔ v = 0 ∧ Complex.normSq u = 1 := by
  constructor
  · rintro ⟨hH, hL⟩
    have hv := (mixed_cartan_iff u v).1 hH
    subst v
    refine ⟨rfl, ?_⟩
    rw [mixed_ladder_bracket] at hL
    have h00 := congrArg (fun X : SpinMatrix => (X 0 0).re) hL
    simpa [isospin3, pauli3] using h00
  · rintro ⟨rfl, hu⟩
    constructor
    · exact (mixed_cartan_iff u 0).2 rfl
    · rw [mixed_ladder_bracket, hu]
      norm_num

/-- An exact nontrivial hyperbolic pair preserves one bracket and fails the other. -/
theorem hyperbolic_counterexample :
    (mixedPlus (5/4) (3/4) * mixedMinus (5/4) (3/4) -
        mixedMinus (5/4) (3/4) * mixedPlus (5/4) (3/4) = (2 : ℂ) • isospin3) ∧
      (isospin3 * mixedPlus (5/4) (3/4) - mixedPlus (5/4) (3/4) * isospin3 ≠
        mixedPlus (5/4) (3/4)) := by
  constructor
  · rw [mixed_ladder_bracket]
    norm_num [Complex.normSq_apply]
  · rw [mixed_cartan_iff]
    norm_num

/-- The elementary transverse change and its inverse are plain linear algebra. -/
theorem transverse_inverse (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    let p := mixedPlus ((a+b)/2) ((a-b)/2)
    let m := ((a-b)/2) • isospinPlus + ((a+b)/2) • isospinMinus
    ((a+b)/(2*a*b)) • p - ((a-b)/(2*a*b)) • m = isospinPlus := by
  dsimp [mixedPlus]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [isospinPlus, isospinMinus, pauli1, pauli2] <;>
    field_simp [ha, hb] <;> ring

/-- Scalar displacements change the trace; similarity transformations do not. -/
theorem trace_scalar_shift (X : SpinMatrix) (b : ℂ) :
    Matrix.trace (X + b • (1 : SpinMatrix)) = Matrix.trace X + 2 * b := by
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

/-- No nonzero scalar shift is any similarity, hence not a unitary similarity. -/
theorem no_similarity_scalar_shift (U : SpinMatrixˣ) (X : SpinMatrix)
    (b : ℂ) (hb : b ≠ 0) :
    (↑U : SpinMatrix) * X * (↑(U⁻¹) : SpinMatrix) ≠ X + b • (1 : SpinMatrix) := by
  intro h
  have ht := congrArg Matrix.trace h
  have hu : Matrix.trace ((↑U : SpinMatrix) * X * (↑(U⁻¹) : SpinMatrix)) =
      Matrix.trace X := by
    rw [Matrix.trace_mul_comm, ← mul_assoc]
    simp
  rw [hu, trace_scalar_shift] at ht
  apply hb
  linear_combination (-1 / 2 : ℂ) * ht

end InfoGeometry.Physics.SpinAffineCasimirRigidity
