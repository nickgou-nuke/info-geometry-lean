/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.EvenInternalComplex
import InfoGeometry.Clifford.Clifford55

/-!
# A concrete internal phase in the native real `Cl(5,5)` even module

The existing positive vectors `e_pos 0` and `e_pos 1` form an orthogonal
normalized plane. Their native Clifford product gives an even square-minus-one
element. This owner instantiates the proved real coordinate/right-action
bridge on that actual carrier; no matrix realization or compatibility fields
are supplied.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55InternalComplex

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.EvenInternalComplex
open InfoGeometry.Clifford.EvenRegularRepresentation
open InfoGeometry.Quantum.RealKCategory

/-- The selected positive coordinate plane in the existing quadratic form. -/
theorem e_pos_zero_ortho_one : Q55.IsOrtho (e_pos 0) (e_pos 1) := by
  norm_num [QuadraticMap.isOrtho_def, Q55_apply, e_pos, Fin.sum_univ_succ]
  norm_num [show (Finset.univ.filter (fun x : Fin 4 => x.succ = 1)).card = 1 by decide]

/-- The actual native even Clifford phase generator. -/
def phaseBivector55 : CliffordAlgebra.even Q55 :=
  planeBivector Q55 (e_pos 0) (e_pos 1)

@[simp] theorem coe_phaseBivector55 :
    (phaseBivector55 : Cl55) = ι55 (e_pos 0) * ι55 (e_pos 1) := rfl

theorem phaseBivector55_sq :
    phaseBivector55 * phaseBivector55 = -(1 : CliffordAlgebra.even Q55) :=
  planeBivector_sq_of_positive_plane Q55 (e_pos 0) (e_pos 1)
    e_pos_zero_ortho_one (Q55_e_pos 0) (Q55_e_pos 1)

/-- The native even module with right bivector phase. -/
abbrev nativeRealK55 : RealKVect :=
  rightRealK Q55 phaseBivector55 phaseBivector55_sq

theorem nativeRealK55_phase_apply (x : CliffordAlgebra.even Q55) :
    nativeRealK55.K x = x * phaseBivector55 := rfl

theorem nativeRealK55_phase_sq :
    nativeRealK55.K.comp nativeRealK55.K =
      -(LinearMap.id : CliffordAlgebra.even Q55 →ₗ[ℝ] CliffordAlgebra.even Q55) :=
  nativeRealK55.K_sq

theorem nativeRealK55_commutes_left (a : CliffordAlgebra.even Q55) :
    (leftRegularLinearMap Q55 a).comp nativeRealK55.K =
      nativeRealK55.K.comp (leftRegularLinearMap Q55 a) :=
  leftRegularLinearMap_comm_rightRegularLinearMap Q55 a phaseBivector55

theorem phasePlane55_intertwines :
    (phasePlaneMap Q55 phaseBivector55).comp coordinateJ =
      nativeRealK55.K.comp (phasePlaneMap Q55 phaseBivector55) :=
  phasePlaneMap_intertwines Q55 phaseBivector55 phaseBivector55_sq

theorem phasePlane55_injective :
    Function.Injective (phasePlaneMap Q55 phaseBivector55) :=
  phasePlaneMap_injective Q55 phaseBivector55 phaseBivector55_sq

/-- Clifford parity fixes this bivector; it does not conjugate its complex phase. -/
theorem involute_phaseBivector55 :
    CliffordAlgebra.involute (phaseBivector55 : Cl55) = (phaseBivector55 : Cl55) :=
  involute_planeBivector Q55 (e_pos 0) (e_pos 1)

theorem reverse_phaseBivector55 :
    CliffordAlgebra.reverse (phaseBivector55 : Cl55) = -(phaseBivector55 : Cl55) :=
  reverse_planeBivector Q55 (e_pos 0) (e_pos 1) e_pos_zero_ortho_one

/-- Reversion and Clifford parity really differ on this nonzero phase plane. -/
theorem reverse_ne_involute_phaseBivector55 :
    CliffordAlgebra.reverse (phaseBivector55 : Cl55) ≠
      CliffordAlgebra.involute (phaseBivector55 : Cl55) := by
  intro h
  rw [reverse_phaseBivector55, involute_phaseBivector55] at h
  have heven : -phaseBivector55 = phaseBivector55 := Subtype.ext h
  have hphase : phasePlaneMap Q55 phaseBivector55 (0, -1) =
      phasePlaneMap Q55 phaseBivector55 (0, 1) := by
    simpa using heven
  have hcoords := phasePlane55_injective hphase
  have hsnd : (-1 : ℝ) = 1 := congrArg Prod.snd hcoords
  norm_num at hsnd

theorem nativeRotor55_mul (θ φ : ℝ) :
    rotorElement Q55 phaseBivector55 θ * rotorElement Q55 phaseBivector55 φ =
      rotorElement Q55 phaseBivector55 (θ + φ) :=
  rotorElement_mul Q55 phaseBivector55 phaseBivector55_sq θ φ

theorem nativeRotor55_right_action (θ : ℝ) :
    rightRegularLinearMap Q55 (rotorElement Q55 phaseBivector55 θ) =
      (rotor nativeRealK55 θ).hom :=
  rightRegular_rotorElement Q55 phaseBivector55 phaseBivector55_sq θ

end InfoGeometry.Clifford.Cl55InternalComplex
