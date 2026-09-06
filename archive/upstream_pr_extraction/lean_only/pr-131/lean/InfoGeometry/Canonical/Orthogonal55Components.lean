import InfoGeometry.Canonical.OrthogonalGroup55

noncomputable section
namespace InfoGeometry.Canonical.O55Representation

open Matrix

def orthogonal55Det : OrthogonalGroup55 →* ℝˣ :=
  (Matrix.GeneralLinearGroup.det : GL10 →* ℝˣ).comp
    OrthogonalGroup55.subtype

def specialOrthogonal55 : Subgroup OrthogonalGroup55 :=
  orthogonal55Det.ker

def coordinateReflectionElement : OrthogonalGroup55 :=
  ⟨coordinateReflectionGL, coordinateReflection_mem_orthogonal55⟩

theorem orthogonal55_det_sign (g : OrthogonalGroup55) :
    ((g : GL10) : O55Matrix).det = 1 ∨
      ((g : GL10) : O55Matrix).det = -1 := by
  exact orthogonal55_det_eq_one_or_neg_one g.2

theorem coordinateReflectionElement_det :
    coordinateReflectionElement.1.det = (-1 : ℝˣ) := by
  apply Units.ext
  change ((coordinateReflectionGL : GL10).det : ℝ) = -1
  norm_num [Matrix.GeneralLinearGroup.det, coordinateReflectionGL,
    coordinateReflection, Matrix.det_diagonal, Finset.prod_ite]

theorem coordinateReflectionElement_not_mem_special :
    coordinateReflectionElement ∉ specialOrthogonal55 := by
  intro h
  have hdet : orthogonal55Det coordinateReflectionElement = 1 :=
    (MonoidHom.mem_ker.mp h)
  change coordinateReflectionElement.1.det = 1 at hdet
  rw [coordinateReflectionElement_det] at hdet
  norm_num at hdet

theorem specialOrthogonal55_det_eq_one
    {g : OrthogonalGroup55} (hg : g ∈ specialOrthogonal55) :
    (g : GL10).det = 1 := by
  have hdet : orthogonal55Det g = 1 := MonoidHom.mem_ker.mp hg
  change g.1.det = 1 at hdet
  exact hdet

theorem orthogonal55_det_eq_one_or_neg_one_units (g : OrthogonalGroup55) :
    (g : GL10).det = 1 ∨ (g : GL10).det = -1 := by
  rcases orthogonal55_det_sign g with h | h
  · left
    apply Units.ext
    simpa using h
  · right
    apply Units.ext
    simpa using h

end InfoGeometry.Canonical.O55Representation
