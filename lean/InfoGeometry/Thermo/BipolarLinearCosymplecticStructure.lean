import InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Thermo.BipolarPoissonAlgebra
import Mathlib

/-!
# Linear cosymplectic structure behind the bipolar GENERIC model

The reversible map `L : V* -> V` is the sharp map of a rank-two Poisson tensor;
it is not by itself a cosymplectic structure.  On the three-coordinate carrier
`(eta,theta,a)`, the corresponding constant linear cosymplectic data are

`alpha = d eta`,

`omega = d theta wedge d a`.

Their volume evaluation on `(e_eta,e_theta,e_a)` is one.  The vector `e_eta` is
the Reeb direction, and the existing reversible operator is the inverse of
`omega` on the horizontal plane `ker(d eta)`.
-/

noncomputable section

namespace InfoGeometry.Thermo.BipolarLinearCosymplecticStructure

open InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
open InfoGeometry.Thermo.GenericMetriplecticFlow

/-- Constant horizontal two-form `dtheta wedge da`. -/
def horizontalTwoForm : LinearMap.BilinForm ℝ State3 where
  toFun u := {
    toFun := fun v => u 1 * v 2 - u 2 * v 1
    map_add' := by
      intro v w
      simp
      ring
    map_smul' := by
      intro c v
      simp
      ring
  }
  map_add' := by
    intro u v
    ext w
    simp
    ring
  map_smul' := by
    intro c u
    ext v
    simp
    ring

@[simp] theorem horizontalTwoForm_apply (u v : State3) :
    horizontalTwoForm u v = u 1 * v 2 - u 2 * v 1 :=
  rfl

/-- Skew-symmetry of the horizontal two-form. -/
theorem horizontalTwoForm_skew (u v : State3) :
    horizontalTwoForm u v = -horizontalTwoForm v u := by
  simp [horizontalTwoForm]
  ring

@[simp] theorem horizontalTwoForm_self (u : State3) :
    horizontalTwoForm u u = 0 := by
  simp [horizontalTwoForm]
  ring

/-- Evaluation of `deta wedge (dtheta wedge da)`. -/
def cosymplecticVolume (u v w : State3) : ℝ :=
  etaCovector u * horizontalTwoForm v w -
    etaCovector v * horizontalTwoForm u w +
    etaCovector w * horizontalTwoForm u v

/-- The canonical three-form is nonzero and normalized on the coordinate frame. -/
@[simp] theorem cosymplecticVolume_basis :
    cosymplecticVolume etaBasis3 thetaBasis3 auxiliaryBasis3 = 1 := by
  simp [cosymplecticVolume, horizontalTwoForm,
    etaBasis3, thetaBasis3, auxiliaryBasis3, etaCovector]

/-- Hence the linear cosymplectic volume form is not identically zero. -/
theorem cosymplecticVolume_ne_zero :
    cosymplecticVolume ≠ 0 := by
  intro h
  have hb := congrArg
    (fun f : State3 → State3 → State3 → ℝ =>
      f etaBasis3 thetaBasis3 auxiliaryBasis3) h
  simp at hb

/-- The Reeb direction of the constant pair `(deta,dtheta wedge da)`. -/
def reebVector : State3 := etaBasis3

@[simp] theorem etaCovector_reebVector :
    etaCovector reebVector = 1 := by
  simp [reebVector]

/-- The Reeb direction lies in the kernel of the horizontal two-form. -/
theorem horizontalTwoForm_reeb_left (v : State3) :
    horizontalTwoForm reebVector v = 0 := by
  simp [horizontalTwoForm, reebVector, etaBasis3]

/-- The corresponding right-kernel statement. -/
theorem horizontalTwoForm_reeb_right (v : State3) :
    horizontalTwoForm v reebVector = 0 := by
  simp [horizontalTwoForm, reebVector, etaBasis3]

/-- Coordinate decomposition of the three-dimensional carrier. -/
theorem state3_coordinate_decomposition (v : State3) :
    v = v 0 • etaBasis3 + v 1 • thetaBasis3 +
      v 2 • auxiliaryBasis3 := by
  ext i
  fin_cases i <;>
    simp [etaBasis3, thetaBasis3, auxiliaryBasis3]

/-- Evaluation of a covector in the coordinate frame. -/
theorem covector_state3_coordinate_evaluation
    (β : Covector State3) (v : State3) :
    β v = v 0 * β etaBasis3 + v 1 * β thetaBasis3 +
      v 2 * β auxiliaryBasis3 := by
  rw [state3_coordinate_decomposition v]
  simp only [map_add, map_smul]
  simp [etaBasis3, thetaBasis3, auxiliaryBasis3]

/-- The reversible sharp map inverts the horizontal two-form up to removal of
the Reeb component:

`omega(L beta,v) = beta(v) - beta(Reeb) deta(v)`. -/
theorem horizontalTwoForm_reversibleOperator
    (β : Covector State3) (v : State3) :
    horizontalTwoForm (reversibleOperator β) v =
      β v - β reebVector * etaCovector v := by
  rw [covector_state3_coordinate_evaluation β v]
  simp [horizontalTwoForm, reversibleOperator, reebVector,
    etaBasis3, thetaBasis3, auxiliaryBasis3, etaCovector]
  ring

/-- On the horizontal plane `ker(deta)`, the two-form and Poisson sharp map are
mutual inverses under contraction. -/
theorem horizontalTwoForm_reversibleOperator_of_horizontal
    (β : Covector State3) (v : State3)
    (hv : etaCovector v = 0) :
    horizontalTwoForm (reversibleOperator β) v = β v := by
  rw [horizontalTwoForm_reversibleOperator, hv]
  simp

/-- The eta covector is the Casimir covector of the Poisson sharp map. -/
@[simp] theorem reversibleOperator_etaCovector_zero :
    reversibleOperator etaCovector = 0 := by
  ext i
  fin_cases i <;>
    simp [reversibleOperator, etaCovector, etaBasis3, thetaBasis3,
      auxiliaryBasis3]

/-- The horizontal coordinate pair is canonically normalized. -/
@[simp] theorem horizontalTwoForm_theta_auxiliary :
    horizontalTwoForm thetaBasis3 auxiliaryBasis3 = 1 := by
  simp [horizontalTwoForm, thetaBasis3, auxiliaryBasis3]

@[simp] theorem horizontalTwoForm_auxiliary_theta :
    horizontalTwoForm auxiliaryBasis3 thetaBasis3 = -1 := by
  simp [horizontalTwoForm, thetaBasis3, auxiliaryBasis3]

/-- Compact linear cosymplectic packet. -/
theorem bipolar_linear_cosymplectic_packet :
    cosymplecticVolume etaBasis3 thetaBasis3 auxiliaryBasis3 = 1 ∧
      etaCovector reebVector = 1 ∧
      (∀ v, horizontalTwoForm reebVector v = 0) ∧
      reversibleOperator etaCovector = 0 ∧
      horizontalTwoForm thetaBasis3 auxiliaryBasis3 = 1 := by
  exact ⟨cosymplecticVolume_basis,
    etaCovector_reebVector,
    horizontalTwoForm_reeb_left,
    reversibleOperator_etaCovector_zero,
    horizontalTwoForm_theta_auxiliary⟩

end InfoGeometry.Thermo.BipolarLinearCosymplecticStructure
