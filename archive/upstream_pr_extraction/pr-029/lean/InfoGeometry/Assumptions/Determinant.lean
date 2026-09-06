import Architect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Instances.Matrix

/-!
# Assumptions.Determinant

Determinant/group interface now aligned with mathlib objects:
- `GL` as `Matrix.GeneralLinearGroup`
- `detHom` as `Matrix.GeneralLinearGroup.det`
- `SL` as `Matrix.SpecialLinearGroup`
-/

namespace InfoGeometry.Assumptions.Determinant

universe u v

/-- Canonical matrix general linear group. -/
abbrev «GL» (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :=
  Matrix.GeneralLinearGroup V R

/-- Determinant homomorphism `GL(V) →* Rˣ`. -/
noncomputable abbrev detHom (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    «GL» R V →* Rˣ :=
  Matrix.GeneralLinearGroup.det

/-- Canonical matrix special linear group. -/
abbrev «SL» (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    Type _ :=
  Matrix.SpecialLinearGroup V R

/-- Characterization of `SL` as determinant-1 matrices inside `GL`. -/
theorem ker_det_eq_SL (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    Set.range (Matrix.SpecialLinearGroup.toGL : «SL» R V → «GL» R V) =
      detHom R V ⁻¹' {1} := by
  simpa [detHom] using (Matrix.SpecialLinearGroup.range_toGL (n := V) (A := R))

/-- Draft logarithmic absolute determinant. -/
@[blueprint "def:determinant-log-abs"]
noncomputable def logAbsDet (V : Type v)
    [Fintype V] [DecidableEq V] : «GL» ℝ V → ℝ := fun g =>
  Real.log (|((detHom ℝ V g : ℝˣ) : ℝ)|)

/-- Jacobian determinant helper (`det` on linear automorphisms). -/
@[blueprint "def:determinant-jac"]
noncomputable abbrev jacDet (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    «GL» R V →* Rˣ :=
  detHom R V

/-- Jacobian chain rule for linear automorphisms. -/
theorem jacDet_comp (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V]
    (f g : «GL» R V) :
    jacDet R V (f * g) = jacDet R V f * jacDet R V g := by
  change detHom R V (f * g) = detHom R V f * detHom R V g
  exact (detHom R V).map_mul f g

/-- Named alias for multiplicative functoriality of the Jacobian determinant. -/
theorem jacobian_functoriality (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V]
    (f g : «GL» R V) :
    jacDet R V (f * g) = jacDet R V f * jacDet R V g :=
  jacDet_comp R V f g

end InfoGeometry.Assumptions.Determinant
