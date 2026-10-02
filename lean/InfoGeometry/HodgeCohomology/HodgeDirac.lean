import InfoGeometry.EmergentGeometry.HodgeDiracFactorization
import Mathlib.Analysis.InnerProductSpace.Adjoint

open scoped InnerProductSpace

namespace InfoGeometry.HodgeCohomology.HodgeDirac

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

section AdjointPair

variable (differential codifferential : Space →ₗ[ℝ] Space)
variable (adjunction : ∀ left right,
  ⟪differential left, right⟫_ℝ = ⟪left, codifferential right⟫_ℝ)

include adjunction

theorem reverse_adjunction (left right : Space) :
    ⟪codifferential left, right⟫_ℝ = ⟪left, differential right⟫_ℝ := by
  calc
    ⟪codifferential left, right⟫_ℝ = ⟪right, codifferential left⟫_ℝ :=
      real_inner_comm right (codifferential left)
    _ = ⟪differential right, left⟫_ℝ := (adjunction right left).symm
    _ = ⟪left, differential right⟫_ℝ := real_inner_comm left (differential right)

theorem hodgeDirac_isSymmetric : (differential + codifferential).IsSymmetric := by
  intro left right
  simp only [LinearMap.add_apply, inner_add_left, inner_add_right]
  rw [adjunction, reverse_adjunction differential codifferential adjunction, add_comm]

theorem codifferential_sq_zero (nilpotent : differential * differential = 0) :
    codifferential * codifferential = 0 := by
  ext state
  apply ext_inner_left ℝ
  intro test
  change ⟪test, codifferential (codifferential state)⟫_ℝ = ⟪test, 0⟫_ℝ
  rw [← adjunction, ← adjunction]
  have square_zero : differential (differential test) = 0 :=
    LinearMap.congr_fun nilpotent test
  rw [square_zero, inner_zero_left, inner_zero_right]

theorem hodgeDirac_sq_eq_laplacian (nilpotent : differential * differential = 0) :
    (differential + codifferential) * (differential + codifferential) =
      differential * codifferential + codifferential * differential := by
  rw [add_mul, mul_add, mul_add, nilpotent,
    codifferential_sq_zero differential codifferential adjunction nilpotent]
  simp

theorem laplacian_energy (state : Space) :
    ⟪(differential * codifferential + codifferential * differential) state, state⟫_ℝ =
      ‖differential state‖ ^ 2 + ‖codifferential state‖ ^ 2 := by
  simp only [LinearMap.add_apply, Module.End.mul_apply, inner_add_left]
  rw [adjunction (codifferential state) state,
    reverse_adjunction differential codifferential adjunction (differential state) state,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, add_comm]

theorem harmonic_iff_closed_and_coclosed (state : Space) :
    (differential * codifferential + codifferential * differential) state = 0 ↔
      differential state = 0 ∧ codifferential state = 0 := by
  constructor
  · intro harmonic
    have energy := laplacian_energy differential codifferential adjunction state
    rw [harmonic, inner_zero_left] at energy
    have differential_zero : ‖differential state‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖codifferential state‖]
    have codifferential_zero : ‖codifferential state‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖differential state‖]
    exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp differential_zero),
      norm_eq_zero.mp (sq_eq_zero_iff.mp codifferential_zero)⟩
  · rintro ⟨closed, coclosed⟩
    simp [Module.End.mul_apply, closed, coclosed]

theorem hodge_energy_coherence (nilpotent : differential * differential = 0) (state : Space) :
    ⟪(differential * codifferential + codifferential * differential) state, state⟫_ℝ =
      ‖(differential + codifferential) state‖ ^ 2 := by
  rw [← hodgeDirac_sq_eq_laplacian differential codifferential adjunction nilpotent]
  exact EmergentGeometry.HodgeDiracFactorization.square_energy_identity _
    (hodgeDirac_isSymmetric differential codifferential adjunction) state

theorem hodge_kernel_eq (nilpotent : differential * differential = 0) :
    LinearMap.ker (differential * codifferential + codifferential * differential) =
      LinearMap.ker (differential + codifferential) := by
  rw [← hodgeDirac_sq_eq_laplacian differential codifferential adjunction nilpotent]
  exact EmergentGeometry.HodgeDiracFactorization.square_kernel_eq _
    (hodgeDirac_isSymmetric differential codifferential adjunction)

theorem coclosed_exact_eq_zero (primitive state : Space)
    (exact_state : differential primitive = state) (coclosed : codifferential state = 0) :
    state = 0 := by
  have energy : ⟪state, state⟫_ℝ = 0 := by
    calc
      ⟪state, state⟫_ℝ = ⟪differential primitive, state⟫_ℝ := by rw [exact_state]
      _ = ⟪primitive, codifferential state⟫_ℝ := adjunction _ _
      _ = 0 := by rw [coclosed, inner_zero_right]
  exact inner_self_eq_zero.mp energy

end AdjointPair

section NativeAdjoint

variable [FiniteDimensional ℝ Space]

theorem native_adjunction (differential : Space →ₗ[ℝ] Space) (left right : Space) :
    ⟪differential left, right⟫_ℝ = ⟪left, differential.adjoint right⟫_ℝ :=
  (differential.adjoint_inner_right left right).symm

theorem native_hodge_kernel_eq (differential : Space →ₗ[ℝ] Space)
    (nilpotent : differential * differential = 0) :
    LinearMap.ker (differential * differential.adjoint + differential.adjoint * differential) =
      LinearMap.ker (differential + differential.adjoint) :=
  hodge_kernel_eq differential differential.adjoint (native_adjunction differential) nilpotent

end NativeAdjoint

end InfoGeometry.HodgeCohomology.HodgeDirac
