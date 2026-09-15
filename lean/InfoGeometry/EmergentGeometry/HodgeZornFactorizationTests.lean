import InfoGeometry.EmergentGeometry.HodgeDiracFactorization
import InfoGeometry.EmergentGeometry.ZornChiralPotential

open scoped InnerProductSpace
open InfoGeometry.EmergentGeometry.HodgeDiracFactorization
open InfoGeometry.EmergentGeometry.ZornChiralPotential
open InfoGeometry.Algebra

example {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    (operator : Space →ₗ[ℝ] Space) (symmetric : operator.IsSymmetric) :
    LinearMap.ker (operator * operator) = LinearMap.ker operator :=
  square_kernel_eq operator symmetric

example : ¬ Function.Injective (fun state : ℝ =>
    Real.sqrt ⟪(LinearMap.id : ℝ →ₗ[ℝ] ℝ) state, state⟫_ℝ) := by
  intro injective
  have equal : Real.sqrt ⟪(1 : ℝ), 1⟫_ℝ = Real.sqrt ⟪(-1 : ℝ), -1⟫_ℝ := by
    norm_num
  have states : (1 : ℝ) = -1 := injective equal
  norm_num at states

example :
    let shift : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
      (LinearMap.inl ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ ℝ)
    (shift * shift) (0, 1) = 0 ∧ shift (0, 1) ≠ 0 := by
  norm_num

example :
    Real.sqrt (ZornMatrix.zornNorm (positiveSlice (-3) 0) - Vec3.dot (0 : Vec3 ℝ) 0) = 3 := by
  rw [sqrt_sub_spatial]
  norm_num

example : (positiveSlice 1 ![1, 0, 0]).zornNorm = 2 := by
  norm_num [positiveSlice_norm, Vec3.dot, Matrix.cons_val_two]

example : ∃ element : ZornMatrix ℝ, element.zornNorm < 0 :=
  zornNorm_can_be_negative

#print axioms square_energy_identity
#print axioms square_energy_nonneg
#print axioms square_apply_eq_zero_iff
#print axioms square_kernel_eq
#print axioms sqrt_square_energy
#print axioms sqrt_square_energy_smul
#print axioms positiveSlice_norm
#print axioms positiveSlice_norm_nonneg
#print axioms sqrt_sub_spatial
#print axioms sqrt_sub_spatial_of_nonneg
#print axioms positiveSlice_norm_not_injective
#print axioms zornNorm_can_be_negative
