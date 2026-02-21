import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

/-!
# Assumptions.Determinant

Assumption-backed interface for determinant/group wrapper drafts extracted from
the historical `InfoGeometry/New.lean`.
-/

namespace InfoGeometry.Assumptions.Determinant

universe u v

/-- Draft general linear group wrapper. -/
def GL (R : Type u) (V : Type v) : Type (max u v) := ULift.{v} (R × V)

/-- Draft special linear subgroup wrapper. -/
def SL (R : Type u) (V : Type v) : Type (max u v) := GL R V

/-- Draft determinant homomorphism placeholder. -/
def detHom (R : Type u) (V : Type v) : GL R V → R := fun g => g.down.1

/-- Draft kernel characterization placeholder (`ker det = SL`). -/
def ker_det_eq_SL (R : Type u) (V : Type v) : Prop := SL R V = GL R V

/-- Draft logarithmic absolute determinant. -/
noncomputable def logAbsDet (V : Type v) : GL ℝ V → ℝ := fun g =>
  Real.log (|detHom ℝ V g|)

/-- Draft Jacobian determinant helper. -/
def jacDet (R : Type u) (V : Type v) : GL R V → R := detHom R V

/-- Draft Jacobian functoriality/composition marker. -/
def jacDet_comp (R : Type u) (V : Type v) (f g : GL R V) : Prop :=
  jacDet R V f = jacDet R V f ∧ jacDet R V g = jacDet R V g

/-- Draft Jacobian functoriality for maps marker. -/
def jacobian_functoriality {M : Type v} (f g : M → M) : Prop :=
  (fun x => g (f x)) = (fun x => g (f x))

end InfoGeometry.Assumptions.Determinant
