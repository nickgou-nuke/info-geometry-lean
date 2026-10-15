import InfoGeometry.Clifford.Cl55SuperTKK
import InfoGeometry.Clifford.Cl55ContactTKKVacuumIdeal

/-!
# Contact-TKK action on the doubled Krein realization

The contact grading is defined by the contact Euler bivector in
`Cl55ContactTKKVacuumIdeal`.  This module transports that action from the
vacuum ideal to the doubled real carrier used by `Cl55SuperTKK` and proves
that its bracket and grade laws survive transport.  This is a linear carrier
transport only: it does not claim preservation of a Krein pairing, nor does it
identify the contact grading with the separate coordinate tripotent grading.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55ContactTKKKreinBridge

open InfoGeometry.Clifford.Cl55ContactTKKVacuumIdeal
open InfoGeometry.Clifford.Cl55SuperTKK

abbrev ContactBivector :=
  InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55

abbrev VacuumIdeal :=
  InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdeal

/-- The actual contact-TKK action represented on the doubled Krein carrier. -/
def contactKreinAction (X : ContactBivector) :
    Module.End ℝ KreinDouble :=
  (idealKreinEquiv.conjAlgEquiv ℝ)
    (InfoGeometry.Clifford.Cl55ContactTKKVacuumIdeal.tkkVacuumIdealAction X)

/-- The transported contact action intertwines pointwise with the action on
the same Cl(5,5) vacuum ideal. -/
theorem contactKreinAction_intertwines (X : ContactBivector)
    (x : VacuumIdeal) :
    contactKreinAction X (idealKreinEquiv x) =
      idealKreinEquiv
        (InfoGeometry.Clifford.Cl55ContactTKKVacuumIdeal.tkkVacuumIdealAction X x) := by
  simp [contactKreinAction, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply]

/-- Pointwise Jacobi action law on the doubled real carrier. -/
theorem contactKreinAction_bracket_apply (X Y : ContactBivector)
    (u : KreinDouble) :
    contactKreinAction ⁅X, Y⁆ u =
      contactKreinAction X (contactKreinAction Y u) -
        contactKreinAction Y (contactKreinAction X u) := by
  let x : VacuumIdeal := idealKreinEquiv.symm u
  have hu : idealKreinEquiv x = u := idealKreinEquiv.apply_symm_apply u
  rw [← hu]
  simp only [contactKreinAction_intertwines]
  have h := congrArg idealKreinEquiv
    (InfoGeometry.Clifford.Cl55ContactTKKVacuumIdeal.tkkVacuumIdealAction_bracket_apply
      X Y x)
  rw [map_sub] at h
  exact h

/-- The contact-TKK representation preserves the Lie bracket on the
doubled Krein carrier. -/
theorem contactKreinAction_bracket (X Y : ContactBivector) :
    contactKreinAction ⁅X, Y⁆ =
      ⁅contactKreinAction X, contactKreinAction Y⁆ := by
  rw [Ring.lie_def]
  apply LinearMap.ext
  intro u
  simp only [Module.End.mul_apply, LinearMap.sub_apply]
  exact contactKreinAction_bracket_apply X Y u

/-- The contact Euler grade law, evaluated on a doubled Krein vector. -/
theorem contactKreinAction_grade_bracket_apply {k : ℤ}
    {X : ContactBivector}
    (hX : InfoGeometry.Clifford.Cl55ContactTKKVacuumIdeal.IsContactTKKGrade k X)
    (u : KreinDouble) :
    contactKreinAction contactEulerBivector
        (contactKreinAction X u) -
      contactKreinAction X
        (contactKreinAction contactEulerBivector u) =
      (k : ℝ) • contactKreinAction X u := by
  let x : VacuumIdeal := idealKreinEquiv.symm u
  have hu : idealKreinEquiv x = u := idealKreinEquiv.apply_symm_apply u
  rw [← hu]
  simp only [contactKreinAction_intertwines]
  have h := congrArg (fun f : Module.End ℝ VacuumIdeal => f x)
    (InfoGeometry.Clifford.Cl55ContactTKKVacuumIdeal.tkkVacuumIdealAction_grade_bracket hX)
  simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply] at h
  calc
    idealKreinEquiv (tkkVacuumIdealAction contactEulerBivector
        (tkkVacuumIdealAction X x)) -
      idealKreinEquiv (tkkVacuumIdealAction X
        (tkkVacuumIdealAction contactEulerBivector x)) =
        idealKreinEquiv
          (tkkVacuumIdealAction contactEulerBivector
              (tkkVacuumIdealAction X x) -
            tkkVacuumIdealAction X (tkkVacuumIdealAction contactEulerBivector x)) := by
      rw [map_sub]
    _ = idealKreinEquiv ((k : ℝ) • tkkVacuumIdealAction X x) :=
      congrArg idealKreinEquiv h
    _ = (k : ℝ) • idealKreinEquiv (tkkVacuumIdealAction X x) := by
      rw [map_smul]

/-- The actual contact Euler grade equation transports to the doubled Krein
carrier. -/
theorem contactKreinAction_grade_bracket {k : ℤ}
    {X : ContactBivector}
    (hX : InfoGeometry.Clifford.Cl55ContactTKKVacuumIdeal.IsContactTKKGrade k X) :
    ⁅contactKreinAction contactEulerBivector, contactKreinAction X⁆ =
      (k : ℝ) • contactKreinAction X := by
  rw [Ring.lie_def]
  apply LinearMap.ext
  intro u
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  exact contactKreinAction_grade_bracket_apply hX u

end InfoGeometry.Clifford.Cl55ContactTKKKreinBridge

end
