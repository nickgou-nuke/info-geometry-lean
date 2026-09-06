import Architect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Assumptions.Determinant

Determinant/group interface now aligned with mathlib objects:
- `GL` as invertible matrices `Units (Matrix V V R)`
- `detHom` as determinant homomorphism on matrix units
- `SL` as kernel of determinant
-/

namespace InfoGeometry.Assumptions.Determinant

universe u v

/-- Matrix-route general linear group: invertible matrices. -/
abbrev GL (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :=
  Units (Matrix V V R)

/-- Determinant monoid hom on square matrices. -/
noncomputable def detMonoidHom (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] : Matrix V V R →* R where
  toFun := Matrix.det
  map_one' := Matrix.det_one
  map_mul' := Matrix.det_mul

/-- Determinant homomorphism `GL(V) →* Rˣ`. -/
noncomputable def detHom (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    GL R V →* Rˣ :=
  Units.map (detMonoidHom R V)

/-- Special linear group as kernel of determinant. -/
noncomputable def SL (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    Subgroup (GL R V) :=
  (detHom R V).ker

/-- Kernel characterization (`ker det = SL`) by definition. -/
theorem ker_det_eq_SL (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    (detHom R V).ker = SL R V := rfl

/-- Draft logarithmic absolute determinant. -/
@[blueprint "def:determinant-log-abs"]
noncomputable def logAbsDet (V : Type v)
    [Fintype V] [DecidableEq V] : GL ℝ V → ℝ := fun g =>
  Real.log (|((detHom ℝ V g : ℝˣ) : ℝ)|)

/-- Jacobian determinant helper (`det` on linear automorphisms). -/
@[blueprint "def:determinant-jac"]
noncomputable abbrev jacDet (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    GL R V →* Rˣ :=
  detHom R V

/-- Jacobian chain rule for linear automorphisms. -/
theorem jacDet_comp (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V]
    (f g : GL R V) :
    jacDet R V (f * g) = jacDet R V f * jacDet R V g := by
  change detHom R V (f * g) = detHom R V f * detHom R V g
  exact (detHom R V).map_mul f g

/-- Named alias for multiplicative functoriality of the Jacobian determinant. -/
theorem jacobian_functoriality (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V]
    (f g : GL R V) :
    jacDet R V (f * g) = jacDet R V f * jacDet R V g :=
  jacDet_comp R V f g

end InfoGeometry.Assumptions.Determinant
