import InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
import InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
import InfoGeometry.Algebra.IdempotentCornerCommutant

/-!
# The Cl(5,5) vacuum idempotent and its spinor ideal

The faithful Fock representation identifies the neutral Clifford algebra with
the endomorphism algebra of the `Fin 32` coordinate spinor.  The projection
onto coordinate zero is therefore a rank-one idempotent.  Its principal left
ideal is the spinor module itself.  Transport through the existing neutral
Clifford/Cl(5,5) algebra equivalence gives the corresponding concrete
Cl(5,5) idempotent and ideal.  The coordinate equivalence used by the owner
is not shown here to send coordinate zero to the scalar exterior monomial, so
“vacuum” below names a reference coordinate idempotent.  This file does not
identify distinct grading conventions or assert a chirality split.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge

open InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Algebra.IdempotentCornerCommutant

abbrev CoordSpinor := InfoGeometry.Algebra.FiniteSpin.Vec32R
abbrev NeutralClifford := CliffordAlgebra
  (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
    (E := SplitClifford55ExteriorSpinor.V5))
abbrev NeutralIdeal (e : NeutralClifford) :=
  PrincipalLeftIdeal (R := ℝ) e
abbrev Cl55Ideal (e : Cl55) := PrincipalLeftIdeal (R := ℝ) e

/-- The reference coordinate vector at index zero in the `Fin 32` model. -/
def vacuumCoordinate : CoordSpinor := Pi.single 0 1

/-- Rank-one endomorphism determined by the zeroth coordinate. -/
def coordinateRankOne (v : CoordSpinor) : Module.End ℝ CoordSpinor where
  toFun x := x 0 • v
  map_add' x y := by
    simp [add_smul]
  map_smul' c x := by
    simp [smul_smul]

/-- Rank-one projection onto the reference coordinate. -/
def vacuumProjection : Module.End ℝ CoordSpinor :=
  coordinateRankOne vacuumCoordinate

@[simp] theorem vacuumProjection_apply (x : CoordSpinor) :
    vacuumProjection x = x 0 • vacuumCoordinate := rfl

@[simp] theorem vacuumProjection_vacuum :
    vacuumProjection vacuumCoordinate = vacuumCoordinate := by
  ext i
  simp [vacuumCoordinate, vacuumProjection, coordinateRankOne,
    Pi.single_apply]

theorem vacuumProjection_idempotent :
    vacuumProjection * vacuumProjection = vacuumProjection := by
  apply LinearMap.ext
  intro x
  ext i
  by_cases hx : x 0 = 0
  · simp [vacuumProjection, coordinateRankOne, vacuumCoordinate,
      Pi.single_apply]
  · simp [vacuumProjection, coordinateRankOne, vacuumCoordinate,
      Pi.single_apply]

/-- Pull the vacuum projection back through the Fock representation. -/
def neutralVacuumIdempotent : NeutralClifford :=
  neutralCliffordFockAlgEquiv.symm vacuumProjection

theorem neutralVacuumIdempotent_idempotent :
    neutralVacuumIdempotent * neutralVacuumIdempotent =
      neutralVacuumIdempotent := by
  apply neutralCliffordFockAlgEquiv.injective
  simp [neutralVacuumIdempotent, vacuumProjection_idempotent]

/-- The left ideal of the neutral Clifford vacuum idempotent. -/
def neutralVacuumIdeal : Submodule ℝ NeutralClifford :=
  principalLeftIdealSubmodule (R := ℝ) neutralVacuumIdempotent

/-- Evaluation on the vacuum identifies the Fock-coordinate left ideal with
the coordinate spinor. -/
def neutralVacuumIdealCoordEquiv :
    neutralVacuumIdeal ≃ₗ[ℝ] CoordSpinor where
  toFun x := neutralCliffordFockAlgEquiv x.1 vacuumCoordinate
  invFun v :=
    ⟨neutralCliffordFockAlgEquiv.symm (coordinateRankOne v), by
      apply neutralCliffordFockAlgEquiv.injective
      simpa [neutralVacuumIdempotent] using
        (show coordinateRankOne v * vacuumProjection = coordinateRankOne v from by
          apply LinearMap.ext
          intro x
          ext i
          by_cases hx : x 0 = 0
          · simp [vacuumProjection, coordinateRankOne, vacuumCoordinate,
              hx]
          · simp [vacuumProjection, coordinateRankOne, vacuumCoordinate])
    ⟩
  left_inv x := by
    apply Subtype.ext
    apply neutralCliffordFockAlgEquiv.injective
    rw [neutralCliffordFockAlgEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro z
    have hx : neutralCliffordFockAlgEquiv x.1 * vacuumProjection =
        neutralCliffordFockAlgEquiv x.1 := by
      simpa [neutralVacuumIdempotent] using
        congrArg neutralCliffordFockAlgEquiv.toAlgHom x.2
    have hpoint : neutralCliffordFockAlgEquiv x.1
        (vacuumProjection z) = neutralCliffordFockAlgEquiv x.1 z := by
      have h := congrArg (fun f : Module.End ℝ CoordSpinor => f z) hx
      simpa only [Module.End.mul_apply] using h
    ext i
    rw [← hpoint]
    simp [vacuumProjection, coordinateRankOne, vacuumCoordinate,
      map_smul]
  right_inv v := by
    ext i
    simp [coordinateRankOne, vacuumCoordinate]
  map_add' x y := by
    simp
  map_smul' c x := by
    simp

/-- The neutral Clifford vacuum ideal is the existing exterior spinor, via the
owner's explicit `Fin 32` coordinate equivalence. -/
def neutralVacuumIdealSpinorEquiv :
    neutralVacuumIdeal ≃ₗ[ℝ] Spinor :=
  neutralVacuumIdealCoordEquiv.trans spinorCoordinateEquiv.symm

/-- The left regular action of the neutral Clifford algebra on its vacuum
ideal.  This is the module action whose transported form is the exterior
spinor representation. -/
def neutralVacuumIdealLeftAction (a : NeutralClifford) :
    neutralVacuumIdeal →ₗ[ℝ] neutralVacuumIdeal where
  toFun x := ⟨a * x.1, by
    change (a * x.1) * neutralVacuumIdempotent = a * x.1
    rw [mul_assoc, x.2]
  ⟩
  map_add' x y := by
    apply Subtype.ext
    exact mul_add a x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact Algebra.mul_smul_comm c a x.1

/-- Evaluation on the vacuum intertwines the left-ideal action with the
existing exterior-spinor action. -/
theorem neutralVacuumIdealLeftAction_intertwines
    (a : NeutralClifford) (x : neutralVacuumIdeal) :
    neutralVacuumIdealSpinorEquiv (neutralVacuumIdealLeftAction a x) =
      neutralCliffordRep a (neutralVacuumIdealSpinorEquiv x) := by
  apply spinorCoordinateEquiv.injective
  simp only [neutralVacuumIdealSpinorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change neutralCliffordFockAlgEquiv (a * x.1) vacuumCoordinate =
    spinorCoordinateEquiv
      (neutralCliffordRep a
        (spinorCoordinateEquiv.symm
          (neutralCliffordFockAlgEquiv x.1 vacuumCoordinate)))
  rw [spinorCoordinateEquiv_intertwines]
  simp only [LinearEquiv.apply_symm_apply]
  rw [← neutralCliffordFockAlgEquiv_toAlgHom]
  exact congrArg (fun f : Module.End ℝ SCoord => f vacuumCoordinate)
    (neutralCliffordFockAlgEquiv.map_mul a x.1)

/-- The same rank-one idempotent, now expressed in the canonical Cl(5,5)
algebra. -/
def cl55VacuumIdempotent : Cl55 :=
  Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv
    neutralVacuumIdempotent

theorem cl55VacuumIdempotent_idempotent :
    cl55VacuumIdempotent * cl55VacuumIdempotent = cl55VacuumIdempotent := by
  rw [cl55VacuumIdempotent, ← map_mul]
  rw [neutralVacuumIdempotent_idempotent]

/-- The Cl(5,5) vacuum ideal. -/
def cl55VacuumIdeal : Submodule ℝ Cl55 :=
  principalLeftIdealSubmodule (R := ℝ) cl55VacuumIdempotent

/-- Transport principal left ideals across an algebra equivalence that carries
one specified idempotent to the other. -/
def leftIdealAlgEquiv {A B : Type*} [Semiring A] [Semiring B]
    [Algebra ℝ A] [Algebra ℝ B] (e : A ≃ₐ[ℝ] B) (a : A) (b : B)
    (hab : e a = b) :
    principalLeftIdealSubmodule (R := ℝ) a ≃ₗ[ℝ]
      principalLeftIdealSubmodule (R := ℝ) b where
  toFun x := ⟨e x.1, by
    change e x.1 * b = e x.1
    rw [← hab, ← map_mul, x.2]
  ⟩
  invFun y := ⟨e.symm y.1, by
    change e.symm y.1 * a = e.symm y.1
    apply e.injective
    have hy : y.1 * b = y.1 := y.2
    simpa only [map_mul, e.apply_symm_apply, hab] using hy
  ⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add e.toAlgHom x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smulₛₗ e.toAlgHom c x.1

/-- The concrete Cl(5,5) vacuum ideal is the exterior spinor module. -/
noncomputable def cl55VacuumIdealNeutralEquiv :
    cl55VacuumIdeal ≃ₗ[ℝ] neutralVacuumIdeal :=
  leftIdealAlgEquiv
    Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.symm
    cl55VacuumIdempotent neutralVacuumIdempotent (by
      change Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.symm
        (Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv
          neutralVacuumIdempotent) = neutralVacuumIdempotent
      exact Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.symm_apply_apply _)

/-- The concrete Cl(5,5) vacuum ideal is the exterior spinor module. -/
noncomputable def cl55VacuumIdealSpinorEquiv : cl55VacuumIdeal ≃ₗ[ℝ] Spinor :=
  cl55VacuumIdealNeutralEquiv.trans neutralVacuumIdealSpinorEquiv

/-- The transported rank-one left ideal has the expected 32-dimensional
spinor carrier. -/
theorem cl55VacuumIdeal_finrank : Module.finrank ℝ cl55VacuumIdeal = 32 := by
  rw [cl55VacuumIdealSpinorEquiv.finrank_eq]
  exact spinor_finrank

/-- The left regular `Cl(5,5)` action on the transported vacuum ideal. -/
def cl55VacuumIdealLeftAction (a : Cl55) :
    cl55VacuumIdeal →ₗ[ℝ] cl55VacuumIdeal where
  toFun x := ⟨a * x.1, by
    change (a * x.1) * cl55VacuumIdempotent = a * x.1
    rw [mul_assoc, x.2]
  ⟩
  map_add' x y := by
    apply Subtype.ext
    exact mul_add a x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact Algebra.mul_smul_comm c a x.1

/-- The transported Cl(5,5) ideal action is exactly the neutral exterior
spinor action after applying the existing quadratic-space isometry. -/
theorem cl55VacuumIdealLeftAction_intertwines
    (a : Cl55) (x : cl55VacuumIdeal) :
    cl55VacuumIdealSpinorEquiv (cl55VacuumIdealLeftAction a x) =
      neutralCliffordRep (Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.symm a)
        (cl55VacuumIdealSpinorEquiv x) := by
  let e := Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv
  have haction : cl55VacuumIdealNeutralEquiv
        (cl55VacuumIdealLeftAction a x) =
      neutralVacuumIdealLeftAction (e.symm a)
        (cl55VacuumIdealNeutralEquiv x) := by
    apply Subtype.ext
    change e.symm (a * x.1) = e.symm a * e.symm x.1
    rw [map_mul]
  change neutralVacuumIdealSpinorEquiv
      (cl55VacuumIdealNeutralEquiv (cl55VacuumIdealLeftAction a x)) = _
  rw [haction]
  exact neutralVacuumIdealLeftAction_intertwines (e.symm a)
    (cl55VacuumIdealNeutralEquiv x)

end InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge

end
