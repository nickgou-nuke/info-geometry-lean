import InfoGeometry.HodgeCohomology.KernelSquareCriterion
import InfoGeometry.HodgeCohomology.KreinHodgeDiracBounded

/-!
# Exact criterion for the bounded Krein Hodge kernel identity

Contract: retain the native bounded operators and indefinite adjoint. For a
square-zero differential d, the kernel equality for its Hodge Laplacian holds
exactly when the range and kernel of d + d♯ are disjoint. Symmetry commutation
is an existing sufficient condition, not a replacement definition of adjoint.
Dependencies: native factorization → algebraic kernel-square criterion.
-/
namespace InfoGeometry.HodgeCohomology.KreinHodgeKernelCriterion

open InfoGeometry.Krein KreinSpace KreinHodgeDiracBounded

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable [CompleteSpace Space] [KreinSpace Space]

theorem hodge_kernel_eq_iff (d : Space →L[ℝ] Space) (hd : d * d = 0) :
    LinearMap.ker (d * kreinAdjoint d + kreinAdjoint d * d).toLinearMap =
        LinearMap.ker (d + kreinAdjoint d).toLinearMap ↔
      Disjoint (LinearMap.range (d + kreinAdjoint d).toLinearMap)
        (LinearMap.ker (d + kreinAdjoint d).toLinearMap) := by
  rw [← krein_hodge_factorization d hd]
  exact kernel_square_eq_iff (d + kreinAdjoint d).toLinearMap

/-- A square-zero Krein-self-adjoint operator commuting with the fundamental
symmetry must vanish. This rules out the null example under that hypothesis. -/
theorem square_zero_eq_zero_of_commutes_symmetry (D : Space →L[ℝ] Space)
    (hD : IsKreinSelfAdjoint D) (hJ : D * jCLM = jCLM * D)
    (hzero : D * D = 0) : D = 0 := by
  have hk := krein_square_kernel_eq_of_commutes_symmetry D hD hJ
  have hz : D.toLinearMap.comp D.toLinearMap = 0 :=
    congrArg ContinuousLinearMap.toLinearMap hzero
  have he := (square_zero_kernel_stable_iff D.toLinearMap hz).mp hk
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun f : Space →ₗ[ℝ] Space => f x) he

end InfoGeometry.HodgeCohomology.KreinHodgeKernelCriterion
