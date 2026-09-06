import InfoGeometry.Clifford.Cl55CARSpinAutomorphism
import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure

/-!
# The `Spin(5,5)` action as an automorphism group of the CAR algebra

The target is the native group of ring equivalences of the full Clifford
algebra.  The CAR relations are preserved because the action is an inner ring
automorphism, not because the coefficient algebra is commutative.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford.ChiralLorentzCARLift
open InfoGeometry.OperatorAlgebra

noncomputable def spinCARAutomorphism :
    Spin55 →* (Cl55 ≃+* Cl55) where
  toFun := spinCliffordRingEquiv
  map_one' := by
    ext x
    simp [spinCliffordRingEquiv]
  map_mul' := by
    intro g h
    ext x
    exact spinCliffordRingEquiv_mul g h x

@[simp] theorem spinCARAutomorphism_apply (g : Spin55) (x : Cl55) :
    spinCARAutomorphism g x = spinCliffordRingEquiv g x :=
  rfl

theorem spinCARAutomorphism_maps_grade_family (g : Spin55) :
    MapsToGradeBetween
      (fun k : ℤ => (cl55GradeSubmodule k : Set Cl55))
      (fun k : ℤ =>
        (spinTransportedCl55GradeSubmodule g k : Set Cl55))
      (fun _ : Unit => spinCARAutomorphism g)
      (fun _ k => k) := by
  simpa only [spinCARAutomorphism_apply] using
    spinTransported_maps_grade_family g

/- The CAR-facing owner exposes the corresponding exact image equality. -/
theorem spinCARAutomorphism_grade_image (g : Spin55) (k : ℤ) :
    (spinCARAutomorphism g : Cl55 ≃+* Cl55) ''
        (cl55GradeSubmodule k : Set Cl55) =
      (spinTransportedCl55GradeSubmodule g k : Set Cl55) := by
  simpa only [spinCARAutomorphism_apply] using
    spinTransported_grade_image g k

theorem spinCARAutomorphism_preserves_car (g : Spin55) (i : Fin 5) :
    spinCARAutomorphism g (annihilation55 i) *
          spinCARAutomorphism g (creation55 i) +
        spinCARAutomorphism g (creation55 i) *
          spinCARAutomorphism g (annihilation55 i) = 1 := by
  simpa only [spinCARAutomorphism_apply] using
    spinCliffordRingEquiv_car_anticommutator g i

theorem spinCARAutomorphism_preserves_indexed_car
    (g : Spin55) (i j : Fin 5) :
    spinCARAutomorphism g (annihilation55 i) *
          spinCARAutomorphism g (creation55 j) +
        spinCARAutomorphism g (creation55 j) *
          spinCARAutomorphism g (annihilation55 i) =
      if i = j then 1 else 0 := by
  simpa only [spinCARAutomorphism_apply] using
    spinCliffordRingEquiv_annihilation55_creation55_anticommutator_eq g i j

theorem spinCARAutomorphism_preserves_quadratic_commutator
    (g : Spin55) (i j k l : Fin 5) :
    spinCARAutomorphism g (mixedGenerator55 i j) *
          spinCARAutomorphism g (mixedGenerator55 k l) -
        spinCARAutomorphism g (mixedGenerator55 k l) *
          spinCARAutomorphism g (mixedGenerator55 i j) =
      (if j = k then spinCARAutomorphism g (mixedGenerator55 i l) else 0) -
        (if i = l then spinCARAutomorphism g (mixedGenerator55 k j) else 0) := by
  simpa only [spinCARAutomorphism_apply] using
    spinTransportedMixedGenerator55_commutator_mixedGenerator g i j k l

end InfoGeometry.Clifford.Clifford55
