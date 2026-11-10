import InfoGeometry.Assumptions.Determinant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.LogSum

/-!
# Axioms

Compatibility facade over `InfoGeometry.Assumptions`.
-/

namespace InfoGeometry.Axioms

export InfoGeometry.Projective (
  logSum_inequality
)

export InfoGeometry.Assumptions.Determinant (
  detHom
  ker_det_eq_SL
  logAbsDet
  jacDet
  jacDet_comp
  jacobian_functoriality
)

universe u v

abbrev «GL» (R : Type u) (V : Type v) [CommRing R] [Fintype V] [DecidableEq V] :=
  InfoGeometry.Assumptions.Determinant.GL R V

noncomputable abbrev «SL» (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :=
  InfoGeometry.Assumptions.Determinant.SL R V

end InfoGeometry.Axioms
