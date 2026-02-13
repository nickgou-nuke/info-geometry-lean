import InfoGeometry.Prequantum.Scaling
import InfoGeometry.Projective.Rays
import Mathlib

section KreinClifford

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bundle-level packaging over projective spinor rays. -/
structure ProjectivePrequantumBundle where
  base : ProjectiveState (E := E)
  data : PrequantumData

/-- Scalarized holonomy scale attached to prequantum connection data. -/
def PrequantumData.holonomyScale (P : PrequantumData) : ℝ :=
  P.curvatureScale

theorem PrequantumData.holonomyScale_eq_omega_over_hbar
    (P : PrequantumData) :
    P.holonomyScale = P.omegaScale / P.hbar :=
  P.curvature_law

end KreinClifford
