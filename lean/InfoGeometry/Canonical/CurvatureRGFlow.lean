import InfoGeometry.Canonical.RGFlow
import Mathlib.Analysis.Calculus.MeanValue

namespace CurvatureRGFlow

open InfoGeometry.Canonical.RGFlow
open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
A Curvature RG Flow.
Models the evolution of the Total Scalar Curvature R as a function 
of the information scale Λ.
-/
def ScalarCurvatureFlow (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  ℝ → ℝ -- Λ ↦ R(Λ)

/--
The Beta Function for Information Curvature.
β(R) = ∂R/∂Λ.
In Information Geometry, this corresponds to the 'Learning Ricci Flow'.
-/
noncomputable def curvatureBetaFunction (flow : ScalarCurvatureFlow E) (scale : ℝ) : ℝ :=
  deriv flow scale

omit [FiniteDimensional ℝ E] in
/--
Theorem: A belief manifold at an RG fixed point (scale-invariant)
must have constant scalar curvature with respect to the scale.
-/
theorem curvature_invariant_at_fixed_point (flow : ScalarCurvatureFlow E) (scale0 : ℝ)
    (h_diff : Differentiable ℝ flow) (h_fixed : ∀ s, curvatureBetaFunction flow s = 0) :
    ∃ (c : ℝ), ∀ s, flow s = c := by
  have hfderiv_zero : ∀ s, fderiv ℝ flow s = 0 := by
    intro s
    have hs : deriv flow s = 0 := h_fixed s
    simpa [hs] using (toSpanSingleton_deriv (𝕜 := ℝ) (f := flow) (x := s)).symm
  refine ⟨flow scale0, ?_⟩
  intro s
  have hconst := is_const_of_fderiv_eq_zero (f := flow) h_diff hfderiv_zero s scale0
  simpa using hconst

/--
The Einstein-Hilbert Action Flow.
Describes how the inference cost of manifold tension flows with scale.
-/
noncomputable def einsteinHilbertFlow (flow : ScalarCurvatureFlow E) (scale : ℝ) : ℝ :=
  flow scale -- S_EH(Λ) = R(Λ)

end CurvatureRGFlow
