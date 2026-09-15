import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Data.Real.Basic

namespace InfoGeometry.HodgeCohomology.KreinHodgeDirac

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space]
variable (pairing : LinearMap.BilinForm ℝ Space)

theorem adjoint_relative_to_symmetry
    (symmetry operator referenceAdjoint : Module.End ℝ Space)
    (involutive : symmetry * symmetry = 1)
    (adjunction : LinearMap.IsAdjointPair (pairing.compl₂ symmetry)
      (pairing.compl₂ symmetry) operator referenceAdjoint) :
    LinearMap.IsAdjointPair pairing pairing operator
      (symmetry * referenceAdjoint * symmetry) := by
  intro left right
  have symmetry_sq : symmetry (symmetry right) = right :=
    LinearMap.congr_fun involutive right
  have relation := adjunction left (symmetry right)
  change pairing (operator left) (symmetry (symmetry right)) =
    pairing left (symmetry (referenceAdjoint (symmetry right))) at relation
  simpa only [symmetry_sq, Module.End.mul_apply] using relation

theorem adjoint_unique (nondegenerate : pairing.Nondegenerate)
    (operator firstAdjoint secondAdjoint : Module.End ℝ Space)
    (first : LinearMap.IsAdjointPair pairing pairing operator firstAdjoint)
    (second : LinearMap.IsAdjointPair pairing pairing operator secondAdjoint) :
    firstAdjoint = secondAdjoint := by
  ext state
  apply sub_eq_zero.mp
  apply nondegenerate.2
  intro test
  rw [map_sub, ← first, ← second, sub_self]

theorem anti_isometry_transports_adjunction
    (mirror operator metricAdjoint : Module.End ℝ Space)
    (involutive : mirror * mirror = 1)
    (anti_isometry : ∀ left right,
      pairing (mirror left) (mirror right) = -pairing left right)
    (adjunction : LinearMap.IsAdjointPair pairing pairing operator metricAdjoint) :
    LinearMap.IsAdjointPair pairing pairing (mirror * operator * mirror)
      (mirror * metricAdjoint * mirror) := by
  intro left right
  have mirror_sq (state : Space) : mirror (mirror state) = state :=
    LinearMap.congr_fun involutive state
  change pairing (mirror (operator (mirror left))) right =
    pairing left (mirror (metricAdjoint (mirror right)))
  calc
    pairing (mirror (operator (mirror left))) right =
        -pairing (operator (mirror left)) (mirror right) := by
      simpa only [mirror_sq] using anti_isometry (operator (mirror left)) (mirror right)
    _ = -pairing (mirror left) (metricAdjoint (mirror right)) := by rw [adjunction]
    _ = pairing left (mirror (metricAdjoint (mirror right))) := by
      have relation := anti_isometry (mirror left) (metricAdjoint (mirror right))
      simpa only [mirror_sq] using relation.symm

theorem reverse_adjunction (symmetric : pairing.IsSymm)
    (differential codifferential : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing differential codifferential) :
    LinearMap.IsAdjointPair pairing pairing codifferential differential := by
  intro left right
  rw [symmetric.eq (codifferential left) right, ← adjunction,
    symmetric.eq (differential right) left]

theorem codifferential_sq_zero (nondegenerate : pairing.Nondegenerate)
    (differential codifferential : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing differential codifferential)
    (nilpotent : differential * differential = 0) :
    codifferential * codifferential = 0 := by
  ext state
  apply nondegenerate.2
  intro test
  change pairing test (codifferential (codifferential state)) = 0
  rw [← adjunction, ← adjunction]
  have square_zero : differential (differential test) = 0 :=
    LinearMap.congr_fun nilpotent test
  simp [square_zero]

theorem dirac_self_adjoint (symmetric : pairing.IsSymm)
    (differential codifferential : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing differential codifferential) :
    LinearMap.IsAdjointPair pairing pairing (differential + codifferential)
      (differential + codifferential) := by
  intro left right
  change pairing (differential left + codifferential left) right =
    pairing left (differential right + codifferential right)
  simp only [map_add, LinearMap.add_apply]
  rw [adjunction left right,
    reverse_adjunction pairing symmetric differential codifferential adjunction left right]
  exact add_comm _ _

theorem dirac_sq_eq_laplacian (nondegenerate : pairing.Nondegenerate)
    (differential codifferential : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing differential codifferential)
    (nilpotent : differential * differential = 0) :
    (differential + codifferential) * (differential + codifferential) =
      differential * codifferential + codifferential * differential := by
  rw [add_mul, mul_add, mul_add, nilpotent,
    codifferential_sq_zero pairing nondegenerate differential codifferential adjunction nilpotent]
  simp

theorem signed_laplacian_energy (symmetric : pairing.IsSymm)
    (differential codifferential : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing differential codifferential)
    (state : Space) :
    pairing ((differential * codifferential + codifferential * differential) state) state =
      pairing (differential state) (differential state) +
        pairing (codifferential state) (codifferential state) := by
  simp only [LinearMap.add_apply, Module.End.mul_apply, pairing.map_add₂]
  rw [adjunction (codifferential state) state,
    reverse_adjunction pairing symmetric differential codifferential adjunction
      (differential state) state]
  exact add_comm _ _

theorem signed_square_energy (operator : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing operator operator) (state : Space) :
    pairing ((operator * operator) state) state = pairing (operator state) (operator state) :=
  adjunction (operator state) state

theorem signed_hodge_dirac_energy (symmetric : pairing.IsSymm)
    (nondegenerate : pairing.Nondegenerate)
    (differential codifferential : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing differential codifferential)
    (nilpotent : differential * differential = 0) (state : Space) :
    pairing ((differential * codifferential + codifferential * differential) state) state =
      pairing ((differential + codifferential) state) ((differential + codifferential) state) := by
  rw [← dirac_sq_eq_laplacian pairing nondegenerate differential codifferential
    adjunction nilpotent]
  exact signed_square_energy pairing (differential + codifferential)
    (dirac_self_adjoint pairing symmetric differential codifferential adjunction) state

theorem square_zero_implies_isotropic_image (operator : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing operator operator)
    (state : Space) (harmonic : (operator * operator) state = 0) :
    pairing (operator state) (operator state) = 0 := by
  rw [← signed_square_energy pairing operator adjunction, harmonic]
  simp

theorem square_kernel_eq_of_image_anisotropic (operator : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing operator operator)
    (image_anisotropic : ∀ state, pairing (operator state) (operator state) = 0 →
      operator state = 0) :
    LinearMap.ker (operator * operator) = LinearMap.ker operator := by
  ext state
  constructor
  · intro harmonic
    exact image_anisotropic state
      (square_zero_implies_isotropic_image pairing operator adjunction state harmonic)
  · intro vacuum
    change operator (operator state) = 0
    change operator state = 0 at vacuum
    rw [vacuum, map_zero]

theorem symmetry_weighted_energy (symmetry operator : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing operator operator)
    (commutes : operator * symmetry = symmetry * operator) (state : Space) :
    pairing ((operator * operator) state) (symmetry state) =
      pairing (operator state) (symmetry (operator state)) := by
  change pairing (operator (operator state)) (symmetry state) = _
  rw [adjunction]
  rw [show operator (symmetry state) = symmetry (operator state) from
    LinearMap.congr_fun commutes state]

theorem square_kernel_eq_of_symmetry_positive (symmetry operator : Module.End ℝ Space)
    (adjunction : LinearMap.IsAdjointPair pairing pairing operator operator)
    (commutes : operator * symmetry = symmetry * operator)
    (positive : ∀ state, state ≠ 0 → 0 < pairing state (symmetry state)) :
    LinearMap.ker (operator * operator) = LinearMap.ker operator := by
  ext state
  constructor
  · intro harmonic
    have energy := symmetry_weighted_energy pairing symmetry operator adjunction commutes state
    change (operator * operator) state = 0 at harmonic
    rw [harmonic] at energy
    simp only [map_zero, LinearMap.zero_apply] at energy
    by_contra nonzero
    exact (ne_of_gt (positive (operator state) nonzero)) energy.symm
  · intro vacuum
    change operator (operator state) = 0
    change operator state = 0 at vacuum
    rw [vacuum, map_zero]

end InfoGeometry.HodgeCohomology.KreinHodgeDirac
