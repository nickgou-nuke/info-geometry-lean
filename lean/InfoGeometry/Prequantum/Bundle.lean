import InfoGeometry.Prequantum.Scaling
import InfoGeometry.Projective.Rays

/-!
# InfoGeometry.Prequantum.Bundle

Bundle-level packaging of prequantum data over projective doubled-state rays.
-/

namespace InfoGeometry.Prequantum.Bundle
end InfoGeometry.Prequantum.Bundle

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bundle-level packaging over projective spinor rays. -/
structure ProjectivePrequantumBundle where
  base : ProjectiveState (E := E)
  data : PrequantumData

@[ext] theorem ProjectivePrequantumBundle.ext
    {P Q : ProjectivePrequantumBundle (E := E)}
    (hBase : P.base = Q.base)
    (hData : P.data = Q.data) :
    P = Q := by
  cases P
  cases Q
  cases hBase
  cases hData
  rfl

/-- Scalarized holonomy scale attached to prequantum connection data. -/
def PrequantumData.holonomyScale (P : PrequantumData) : ℝ :=
  P.curvatureScale

theorem PrequantumData.holonomyScale_eq_omega_over_hbar
    (P : PrequantumData) :
    P.holonomyScale = P.omegaScale / P.hbar :=
  P.curvature_law

namespace ProjectivePrequantumBundle

/-- Gauge transform: rescale `ℏ` by `c` at fixed projective base ray. -/
noncomputable def gauge (c : Gauge)
    (P : ProjectivePrequantumBundle (E := E)) :
    ProjectivePrequantumBundle (E := E) :=
  { base := P.base
    data := P.data.rescaleHbar (c : ℝ) (Units.ne_zero c) }

noncomputable instance : SMul Gauge (ProjectivePrequantumBundle (E := E)) :=
  ⟨gauge (E := E)⟩

noncomputable instance : MulAction Gauge (ProjectivePrequantumBundle (E := E)) where
  one_smul := by
    intro P
    apply ProjectivePrequantumBundle.ext
    · rfl
    · change ((1 : Gauge) • P.data) = P.data
      simp
  mul_smul := by
    intro u v P
    apply ProjectivePrequantumBundle.ext
    · rfl
    · change (((u * v) : Gauge) • P.data) = u • (v • P.data)
      simpa using (mul_smul u v P.data)

end ProjectivePrequantumBundle

end KreinClifford
