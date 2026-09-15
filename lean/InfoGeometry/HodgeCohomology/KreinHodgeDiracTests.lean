import InfoGeometry.HodgeCohomology.KreinHodgeDirac
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace InfoGeometry.HodgeCohomology.KreinHodgeDirac.Tests

noncomputable section

abbrev Plane := ℝ × ℝ

def neutralPairing : LinearMap.BilinForm ℝ Plane :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight (LinearMap.snd ℝ ℝ ℝ) +
    (LinearMap.snd ℝ ℝ ℝ).smulRight (LinearMap.fst ℝ ℝ ℝ)

def fundamentalSymmetry : Module.End ℝ Plane :=
  (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap

def nullOperator : Module.End ℝ Plane :=
  (LinearMap.snd ℝ ℝ ℝ).smulRight (1, 0)

theorem neutralPairing_apply (left right : Plane) :
    neutralPairing left right = left.1 * right.2 + left.2 * right.1 := by
  rfl

theorem neutralPairing_symmetric : neutralPairing.IsSymm := by
  constructor
  intro left right
  simp only [neutralPairing_apply]
  ring

theorem neutralPairing_nondegenerate : neutralPairing.Nondegenerate := by
  constructor
  · intro state orthogonal
    have first := orthogonal (0, 1)
    have second := orthogonal (1, 0)
    simp only [neutralPairing_apply, mul_one, mul_zero, zero_add, add_zero] at first second
    exact Prod.ext first second
  · intro state orthogonal
    have first := orthogonal (0, 1)
    have second := orthogonal (1, 0)
    simp only [neutralPairing_apply, one_mul, zero_mul, zero_add, add_zero] at first second
    exact Prod.ext first second

theorem fundamentalSymmetry_involutive : fundamentalSymmetry * fundamentalSymmetry = 1 := by
  apply LinearMap.ext
  intro state
  rfl

theorem fundamentalSymmetry_adjoint :
    LinearMap.IsAdjointPair neutralPairing neutralPairing
      fundamentalSymmetry fundamentalSymmetry := by
  intro left right
  change left.2 * right.2 + left.1 * right.1 = left.1 * right.1 + left.2 * right.2
  ring

theorem fundamentalSymmetry_positive (state : Plane) (nonzero : state ≠ 0) :
    0 < neutralPairing state (fundamentalSymmetry state) := by
  change 0 < state.1 * state.1 + state.2 * state.2
  have not_both_zero : state.1 ≠ 0 ∨ state.2 ≠ 0 := by
    by_contra both
    push_neg at both
    exact nonzero (Prod.ext both.1 both.2)
  rcases not_both_zero with first | second
  · nlinarith [sq_pos_of_ne_zero first, sq_nonneg state.2]
  · nlinarith [sq_pos_of_ne_zero second, sq_nonneg state.1]

theorem pairing_is_indefinite :
    neutralPairing (1, 1) (1, 1) = 2 ∧
    neutralPairing (1, -1) (1, -1) = -2 ∧
    neutralPairing (1, 0) (1, 0) = 0 := by
  norm_num [neutralPairing_apply]

theorem nullOperator_adjoint :
    LinearMap.IsAdjointPair neutralPairing neutralPairing nullOperator nullOperator := by
  intro left right
  simp [neutralPairing_apply, nullOperator]

theorem nullOperator_square : nullOperator * nullOperator = 0 := by
  apply LinearMap.ext
  intro state
  simp [nullOperator]

theorem nullOperator_kernel_counterexample :
    LinearMap.ker (nullOperator * nullOperator) ≠ LinearMap.ker nullOperator := by
  intro equal_kernels
  have in_square : (0, 1) ∈ LinearMap.ker (nullOperator * nullOperator) := by
    rw [nullOperator_square]
    simp
  rw [equal_kernels] at in_square
  simp [LinearMap.mem_ker, nullOperator] at in_square

theorem nullOperator_not_commuting :
    nullOperator * fundamentalSymmetry ≠ fundamentalSymmetry * nullOperator := by
  intro commutes
  have at_state := congrArg (fun operator : Module.End ℝ Plane => (operator (1, 0)).1) commutes
  norm_num [Module.End.mul_apply, nullOperator, fundamentalSymmetry] at at_state

theorem nullOperator_not_reference_self_adjoint :
    ¬LinearMap.IsAdjointPair (neutralPairing.compl₂ fundamentalSymmetry)
      (neutralPairing.compl₂ fundamentalSymmetry) nullOperator nullOperator := by
  intro adjunction
  have relation := adjunction (0, 1) (1, 0)
  norm_num [LinearMap.compl₂_apply, neutralPairing_apply,
    nullOperator, fundamentalSymmetry] at relation

theorem hodge_counterexample :
    (nullOperator + nullOperator) * (nullOperator + nullOperator) = 0 ∧
    (nullOperator + nullOperator) (0, 1) ≠ 0 := by
  constructor
  · rw [dirac_sq_eq_laplacian neutralPairing neutralPairing_nondegenerate
      nullOperator nullOperator nullOperator_adjoint nullOperator_square]
    rw [nullOperator_square, add_zero]
  · norm_num [nullOperator]

example (state : Plane) :
    neutralPairing ((nullOperator * nullOperator) state) state =
      neutralPairing (nullOperator state) (nullOperator state) :=
  signed_square_energy neutralPairing nullOperator nullOperator_adjoint state

example : LinearMap.ker (fundamentalSymmetry * fundamentalSymmetry) =
    LinearMap.ker fundamentalSymmetry :=
  square_kernel_eq_of_symmetry_positive neutralPairing fundamentalSymmetry
    fundamentalSymmetry fundamentalSymmetry_adjoint rfl fundamentalSymmetry_positive

def mirror : Module.End ℝ Plane :=
  (LinearMap.fst ℝ ℝ ℝ).prod (-LinearMap.snd ℝ ℝ ℝ)

theorem mirror_involutive : mirror * mirror = 1 := by
  apply LinearMap.ext
  intro state
  simp [mirror]

theorem mirror_anti_isometry (left right : Plane) :
    neutralPairing (mirror left) (mirror right) = -neutralPairing left right := by
  simp [neutralPairing_apply, mirror]
  ring

example : LinearMap.IsAdjointPair neutralPairing neutralPairing
    (mirror * nullOperator * mirror : Module.End ℝ Plane)
    (mirror * nullOperator * mirror : Module.End ℝ Plane) :=
  anti_isometry_transports_adjunction neutralPairing mirror nullOperator nullOperator
    mirror_involutive mirror_anti_isometry nullOperator_adjoint

#print axioms adjoint_relative_to_symmetry
#print axioms codifferential_sq_zero
#print axioms dirac_sq_eq_laplacian
#print axioms signed_laplacian_energy
#print axioms signed_hodge_dirac_energy
#print axioms square_kernel_eq_of_image_anisotropic
#print axioms square_kernel_eq_of_symmetry_positive
#print axioms neutralPairing_nondegenerate
#print axioms fundamentalSymmetry_positive
#print axioms nullOperator_kernel_counterexample
#print axioms hodge_counterexample
#print axioms anti_isometry_transports_adjunction
#print axioms nullOperator_not_reference_self_adjoint

end

end InfoGeometry.HodgeCohomology.KreinHodgeDirac.Tests
