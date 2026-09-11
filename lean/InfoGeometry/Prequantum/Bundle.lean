import InfoGeometry.Prequantum.Scaling
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.Rays

open InfoGeometry.Projective

/-!
# InfoGeometry.Prequantum.Bundle

Bundle-level packaging of prequantum data over projective doubled-state rays.
-/

/-- Scalarized holonomy scale attached to prequantum connection data. -/
def PrequantumData.holonomyScale (P : PrequantumData) : ℝ :=
  P.curvatureScale

theorem PrequantumData.holonomyScale_eq_omega_over_hbar
    (P : PrequantumData) :
    P.holonomyScale = P.omegaScale / P.hbar :=
  P.curvature_relation

namespace InfoGeometry.Prequantum

section KreinClifford

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bundle-level packaging over projective spinor rays. -/
structure ProjectivePrequantumBundle where
  base : ProjectiveState E
  data : PrequantumData

variable {E} -- Now make E implicit for functions

@[ext] theorem ProjectivePrequantumBundle.ext
    {P Q : ProjectivePrequantumBundle E}
    (hBase : P.base = Q.base)
    (hData : P.data = Q.data) :
    P = Q := by
  cases P
  cases Q
  cases hBase
  cases hData
  rfl

namespace ProjectivePrequantumBundle

/-- Gauge transform: rescale `ℏ` by `c` at fixed projective base ray. -/
noncomputable def gauge (c : PrequantumData.Gauge)
    (P : ProjectivePrequantumBundle E) :
    ProjectivePrequantumBundle E :=
  { base := P.base
    data := P.data.rescaleHbar (c : ℝ) (Units.ne_zero c) }

noncomputable instance : SMul PrequantumData.Gauge (ProjectivePrequantumBundle E) :=
  ⟨gauge⟩

noncomputable instance : MulAction PrequantumData.Gauge (ProjectivePrequantumBundle E) where
  smul := SMul.smul
  one_smul := by
    intro P
    apply ProjectivePrequantumBundle.ext
    · rfl
    · change ((1 : PrequantumData.Gauge) • P.data) = P.data
      simp
  mul_smul := by
    intro u v P
    apply ProjectivePrequantumBundle.ext
    · rfl
    · change (((u * v) : PrequantumData.Gauge) • P.data) = u • (v • P.data)
      simpa using (mul_smul u v P.data)

end ProjectivePrequantumBundle

end KreinClifford

end InfoGeometry.Prequantum
