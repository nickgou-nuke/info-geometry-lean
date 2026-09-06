import Mathlib.Tactic
import InfoGeometry.External.Auto.KanCayley
import InfoGeometry.External.Auto.DeterminantSupergrading
import InfoGeometry.External.Auto.KreinDeterminantAnalyticity

noncomputable section

open Matrix

namespace InfoGeometry.Canonical.KANLogDetUnification

/--
The concrete K/A/N dictionary in `M₂(ℂ)`:

* `KPart θ` is the compact phase block.
* `APart β` is the logarithmic scale block.
* `NPart z` is the unipotent boundary block.
* `NPart z - I` is nilpotent and has zero determinant.
* The whole KAN product has determinant one, hence is an algebraic analytic
  flow in the determinant sense.
-/
theorem complex_scale_boundary_unification (θ β : ℝ) (z : ℂ) :
    (KPart θ).det = 1 ∧
      (APart β).det = 1 ∧
      (NPart z).det = 1 ∧
      (KPart θ * APart β * NPart z).det = 1 ∧
      nilpotentShear z * nilpotentShear z = 0 ∧
      (nilpotentShear z).det = 0 := by
  exact ⟨det_KPart θ, det_APart β, det_NPart z, det_KAN θ β z,
    nilpotentShear_sq z, det_nilpotentShear z⟩

/--
The real doubled atom supplies the determinant-sign grading:

`J` and `ε` are odd determinant-sign operators, while their product
`K = Jε` is even and squares to `-I`.  This is the concrete real operator
replacement for treating the imaginary unit as a scalar primitive.
-/
theorem real_doubled_hypercomplex_atom :
    modular_j.det = -1 ∧
      chiralParity.det = -1 ∧
      emergentK.det = 1 ∧
      emergentK * emergentK = -(1 : M2R) ∧
      superGrade emergentK = (1 : SignType) := by
  exact ⟨modular_j_det, chiralParity_det, emergentK_det, emergentK_sq,
    superGrade_emergentK⟩

/--
The real log-determinant property from `KreinDeterminantAnalyticity`:
the explicit trace-zero hyperbolic scale flow has determinant one and
therefore zero log-volume.
-/
theorem trace_zero_scale_has_zero_log_volume (θ : ℝ) :
    InfoGeometry.Quantum.KreinDeterminantAnalyticity.IsAnalyticFlow2
        (InfoGeometry.Quantum.KreinDeterminantAnalyticity.hyperbolicFlow θ) ∧
      InfoGeometry.Quantum.KreinDeterminantAnalyticity.logVolume
        (InfoGeometry.Quantum.KreinDeterminantAnalyticity.hyperbolicFlow θ) = 0 := by
  exact ⟨InfoGeometry.Quantum.KreinDeterminantAnalyticity.hyperbolicFlow_analytic θ,
    InfoGeometry.Quantum.KreinDeterminantAnalyticity.logVolume_hyperbolic θ⟩

end InfoGeometry.Canonical.KANLogDetUnification
