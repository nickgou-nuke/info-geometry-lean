import InfoGeometry.Projective.TwistorConfigurationSpace
import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham
import InfoGeometry.Projective.ProjectiveLogarithmicBoundaryGeometry

/-!
# Concrete coefficient layer for the `d log Q` packet

This owner records the coefficient of the logarithmic form on the finite
non-isotropic configuration carrier.  It deliberately does not introduce a
manifold-valued differential form: the coefficient is the exact algebraic
readout `1 / Q(x_i - x_j)`.
-/

namespace InfoGeometry.Projective.Conf3ConcreteDLog

open InfoGeometry.Projective.TwistorConfigurationSpace
open InfoGeometry.Projective.KleinQuadric.DeRhamMotive
open InfoGeometry.Projective.ProjectiveLogarithmicBoundaryGeometry

noncomputable section

/-- The coefficient of the logarithmic form attached to an ordered pair. -/
def dlogCoefficient (X : FQ3) (i j : Fin 3) : ℂ :=
  1 / X.separation i j

/-- The real-valued logarithmic potential on the non-isotropic complement. -/
noncomputable def logPotential (X : FQ3) (i j : Fin 3) : ℝ :=
  Real.log ‖X.separation i j‖

theorem exp_logPotential (X : FQ3) (i j : Fin 3) (hij : i ≠ j) :
    Real.exp (logPotential X i j) = ‖X.separation i j‖ := by
  unfold logPotential
  rw [Real.exp_log]
  exact norm_pos_iff.mpr (X.pairwise_non_isotropic i j hij)

theorem logPotential_permute
    (σ : Equiv.Perm (Fin 3)) (X : FQ3) (i j : Fin 3) :
    logPotential (X.permute σ) i j = logPotential X (σ i) (σ j) := by
  unfold logPotential
  rw [FQ3.separation_permute]

/-- The scalar coefficient of the ordinary configuration-space form
    `d log (z_i - z_j)`. -/
def linearDLogCoefficient (z : Fin 3 → ℂ) (i j : Fin 3) : ℂ :=
  1 / (z i - z j)

theorem linearDLogCoefficient_arnold
    (z : Fin 3 → ℂ)
    (h₁₂ : z 0 ≠ z 1) (h₂₃ : z 1 ≠ z 2) (h₃₁ : z 2 ≠ z 0) :
    linearDLogCoefficient z 0 1 * linearDLogCoefficient z 1 2 +
      linearDLogCoefficient z 1 2 * linearDLogCoefficient z 2 0 +
      linearDLogCoefficient z 2 0 * linearDLogCoefficient z 0 1 = 0 := by
  unfold linearDLogCoefficient
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (euler_partial_fraction_identity (z 0) (z 1) (z 2) h₁₂ h₂₃ h₃₁)

/- The concrete configuration coefficient uses exactly the repository's
   canonical scalar `d log` kernel; no second logarithmic API is introduced. -/
theorem dlogCoefficient_eq_grothendieck_dlog
    (X : FQ3) (i j : Fin 3) :
    dlogCoefficient X i j = grothendieck_dlog (X.separation i j) := by
  rfl

/-- The concrete logarithmic coefficient is equivariant under relabelling. -/
theorem dlogCoefficient_permute
    (σ : Equiv.Perm (Fin 3)) (X : FQ3) (i j : Fin 3) :
    dlogCoefficient (X.permute σ) i j = dlogCoefficient X (σ i) (σ j) := by
  unfold dlogCoefficient
  rw [FQ3.separation_permute]

/-- Reversing an edge does not change its quadratic logarithmic coefficient. -/
theorem dlogCoefficient_symm (X : FQ3) (i j : Fin 3) :
    dlogCoefficient X i j = dlogCoefficient X j i := by
  unfold dlogCoefficient
  simpa [FQ3.separation] using congrArg (fun z : ℂ => 1 / z)
    (quadSeparation_comm (X.points i) (X.points j))

/-- Every coefficient attached to a genuine ordered edge is defined. -/
theorem dlogCoefficient_ne_zero (X : FQ3) (i j : Fin 3) (hij : i ≠ j) :
    dlogCoefficient X i j ≠ 0 := by
  unfold dlogCoefficient
  simp [one_div, X.pairwise_non_isotropic i j hij]

end
end InfoGeometry.Projective.Conf3ConcreteDLog
