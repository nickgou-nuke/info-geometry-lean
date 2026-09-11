import Architect
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Instances.Matrix

/-!
# InfoGeometry.Canonical.DeterminantCore

Canonical determinant/group interface aligned with mathlib objects.
-/

namespace InfoGeometry.Canonical.Determinant

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
    [CommRing R] [Fintype V] [DecidableEq V] : Type _ :=
  Matrix.SpecialLinearGroup V R

/-- Characterization of `SL` as determinant-1 matrices inside `GL`. -/
theorem range_toGL_eq_preimage_one (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    Set.range (Matrix.SpecialLinearGroup.toGL : «SL» R V → «GL» R V) =
      detHom R V ⁻¹' {1} := by
  simpa [detHom] using (Matrix.SpecialLinearGroup.range_toGL (n := V) (A := R))

/-- Logarithmic absolute determinant on `GL(ℝ)`. -/
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
theorem jac_det_comp (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V]
    (f g : «GL» R V) :
    jacDet R V (f * g) = jacDet R V f * jacDet R V g := by
  change detHom R V (f * g) = detHom R V f * detHom R V g
  exact (detHom R V).map_mul f g

/-- Log absolute determinant is additive on linear automorphisms. -/
theorem logAbsDet_mul (V : Type v)
    [Fintype V] [DecidableEq V]
    (f g : «GL» ℝ V) :
    logAbsDet V (f * g) = logAbsDet V f + logAbsDet V g := by
  have hf0 : ((detHom ℝ V f : ℝˣ) : ℝ) ≠ 0 := Units.ne_zero _
  have hg0 : ((detHom ℝ V g : ℝˣ) : ℝ) ≠ 0 := Units.ne_zero _
  calc
    logAbsDet V (f * g)
        = Real.log (|((detHom ℝ V (f * g) : ℝˣ) : ℝ)|) := rfl
    _ = Real.log (|(((detHom ℝ V f : ℝˣ) : ℝ) * (((detHom ℝ V g : ℝˣ) : ℝ)))|) := by
          rw [(detHom ℝ V).map_mul]
          rfl
    _ = Real.log (|((detHom ℝ V f : ℝˣ) : ℝ)| * |((detHom ℝ V g : ℝˣ) : ℝ)|) := by
          rw [abs_mul]
    _ = Real.log (|((detHom ℝ V f : ℝˣ) : ℝ)|)
        + Real.log (|((detHom ℝ V g : ℝˣ) : ℝ)|) := by
          exact Real.log_mul (abs_ne_zero.mpr hf0) (abs_ne_zero.mpr hg0)
    _ = logAbsDet V f + logAbsDet V g := by
          rfl

/-- Inversion negates the logarithmic absolute determinant. -/
@[simp] theorem logAbsDet_inv (V : Type v)
    [Fintype V] [DecidableEq V] (f : «GL» ℝ V) :
    logAbsDet V f⁻¹ = -logAbsDet V f := by
  simp [logAbsDet]

end InfoGeometry.Canonical.Determinant
