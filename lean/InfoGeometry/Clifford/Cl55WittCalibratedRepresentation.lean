/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55WittCalibratedGamma
import InfoGeometry.Clifford.Cl55CARSpinAutomorphism
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv
import InfoGeometry.Canonical.Cl55ChiralOccupationFiveGradeBridge
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Faithful native Clifford representation calibrated to the matrix CAR generators

The universal Clifford lift sends each native named creation/annihilation
operator to the existing Jordan–Wigner operator with the same mode index.
The existing faithful spinor equivalence supplies simplicity of the source;
equal finite dimensions then give an algebra equivalence. Raw native number
and centered matrix number differ by exactly `5/2` times the identity, so
their adjoint grading operators intertwine without a transported-grader
assumption or an arbitrary Fock basis identification.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55WittCalibratedRepresentation

open scoped BigOperators
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl55WittCalibratedGamma
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Canonical.Cl55ChiralOccupationFiveGradeBridge

/-- Universal lift of the native quadratic map into the existing matrix stage. -/
def cl55WittRepresentation : Cl55 →ₐ[ℝ] MatStage 5 :=
  CliffordAlgebra.lift Q55 ⟨wittGamma, wittGamma_square⟩

@[simp] theorem cl55WittRepresentation_ι (v : V55) :
    cl55WittRepresentation (ι55 v) = wittGamma v := by
  simp [cl55WittRepresentation]

@[simp] theorem cl55WittRepresentation_creation55 (i : Fin 5) :
    cl55WittRepresentation (creation55 i) = creation i := by
  rw [creation55, map_smul, cl55WittRepresentation_ι, nbar_pair,
    map_sub, wittGamma_e_pos, wittGamma_f_neg]
  module

@[simp] theorem cl55WittRepresentation_annihilation55 (i : Fin 5) :
    cl55WittRepresentation (annihilation55 i) = annihilation i := by
  rw [annihilation55, map_smul, cl55WittRepresentation_ι, n_pair,
    map_add, wittGamma_e_pos, wittGamma_f_neg]
  module

@[simp] theorem cl55WittRepresentation_mixedGenerator55 (i j : Fin 5) :
    cl55WittRepresentation (mixedGenerator55 i j) = E i j := by
  classical
  by_cases hij : i = j <;> simp [mixedGenerator55, E, hij]

theorem cl55WittRepresentation_numberOperator55_raw :
    cl55WittRepresentation numberOperator55 = rawFockNumber := by
  simp [numberOperator55, rawFockNumber]

/-- The scalar correction is essential for occupation and invisible to adjoints. -/
theorem cl55WittRepresentation_numberOperator55 :
    cl55WittRepresentation numberOperator55 =
      numberOperator + (5 / 2 : ℝ) • (1 : MatStage 5) := by
  rw [cl55WittRepresentation_numberOperator55_raw,
    rawFockNumber_eq_numberOperator_add_five_halves]

@[simp] theorem cl55WittRepresentation_centeredNumber :
    cl55WittRepresentation (numberOperator55 - (5 / 2 : ℝ) • (1 : Cl55)) =
      numberOperator := by
  simp [cl55WittRepresentation_numberOperator55]

theorem cl55WittRepresentation_number_commutator (X : Cl55) :
    cl55WittRepresentation (numberOperator55 * X - X * numberOperator55) =
      numberOperator * cl55WittRepresentation X -
        cl55WittRepresentation X * numberOperator := by
  rw [map_sub, map_mul, map_mul, cl55WittRepresentation_numberOperator55_raw]
  exact rawFockNumber_bracket_eq_numberOperator_bracket (cl55WittRepresentation X)

/-- Simplicity comes from the already proved native spinor algebra equivalence. -/
theorem cl55WittRepresentation_injective : Function.Injective cl55WittRepresentation := by
  letI : IsSimpleRing Cl55 :=
    IsSimpleRing.of_ringEquiv cl55SpinorAlgEquiv.toRingEquiv.symm inferInstance
  exact cl55WittRepresentation.toRingHom.injective

theorem cl55WittRepresentation_surjective : Function.Surjective cl55WittRepresentation := by
  letI : FiniteDimensional ℝ Cl55 :=
    LinearEquiv.finiteDimensional cl55SpinorAlgEquiv.toLinearEquiv.symm
  have hdim : Module.finrank ℝ Cl55 = Module.finrank ℝ (MatStage 5) := by
    calc
      Module.finrank ℝ Cl55 =
          Module.finrank ℝ (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) :=
        cl55SpinorAlgEquiv.toLinearEquiv.finrank_eq
      _ = Module.finrank ℝ (MatStage 5) :=
        (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).toLinearEquiv.finrank_eq.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (show Function.Injective cl55WittRepresentation.toLinearMap from
      cl55WittRepresentation_injective)

/-- Full carrier equivalence with proved named-generator calibration. -/
def cl55WittAlgEquiv : Cl55 ≃ₐ[ℝ] MatStage 5 :=
  AlgEquiv.ofBijective cl55WittRepresentation
    ⟨cl55WittRepresentation_injective, cl55WittRepresentation_surjective⟩

@[simp] theorem cl55WittAlgEquiv_apply (X : Cl55) :
    cl55WittAlgEquiv X = cl55WittRepresentation X := rfl

@[simp] theorem cl55WittAlgEquiv_toAlgHom :
    cl55WittAlgEquiv.toAlgHom = cl55WittRepresentation := rfl

end InfoGeometry.Clifford.Cl55WittCalibratedRepresentation
