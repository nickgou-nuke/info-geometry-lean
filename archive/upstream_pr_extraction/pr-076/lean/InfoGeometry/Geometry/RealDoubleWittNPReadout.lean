import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Real double-Witt geometry and its Newman--Penrose readout

This is the algebraic `(2,2)` layer behind a real split analogue of a null
tetrad.  The two real split planes are kept separate from the complex
transverse readout.  No connection or curvature data are assumed.
-/

namespace InfoGeometry.Geometry.RealDoubleWittNP

abbrev Plane := Fin 2 → ℝ
abbrev Carrier := Plane × Plane

def causalForm (x y : Carrier) : ℝ :=
  -(x.1 0) * (y.1 0) + (x.1 1) * (y.1 1) -
    (x.2 0) * (y.2 0) + (x.2 1) * (y.2 1)

def transverseJ : Plane →ₗ[ℝ] Plane :=
  { toFun := fun x => ![-x 1, x 0]
    map_add' := by
      intro x y
      funext i
      fin_cases i <;> simp <;> ring
    map_smul' := by
      intro a x
      funext i
      fin_cases i <;> simp }

theorem transverseJ_sq (x : Plane) :
    transverseJ (transverseJ x) = -x := by
  funext i
  fin_cases i <;> simp [transverseJ]

def npTransverseReadout : Plane →ₗ[ℝ] ℂ :=
  { toFun := fun x => (x 0 : ℂ) + Complex.I * (x 1 : ℂ)
    map_add' := by
      intro x y
      simp [add_mul]
      ring
    map_smul' := by
      intro a x
      simp [mul_add, add_mul]
      ring }

theorem npTransverseReadout_J (x : Plane) :
    npTransverseReadout (transverseJ x) =
      Complex.I * npTransverseReadout x := by
  simp [npTransverseReadout, transverseJ, pow_two]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
    rw [pow_two, Complex.I_mul_I]]
  ring

def cPlus : Plane := ![1, 1]
def cMinus : Plane := ![1, -1]
def ePlus : Plane := ![1, 1]
def eMinus : Plane := ![1, -1]

def cPlusLift : Carrier := (cPlus, 0)
def cMinusLift : Carrier := (cMinus, 0)
def ePlusLift : Carrier := (0, ePlus)
def eMinusLift : Carrier := (0, eMinus)

theorem causalForm_cPlus_self : causalForm cPlusLift cPlusLift = 0 := by
  simp [causalForm, cPlusLift, cPlus]

theorem causalForm_cMinus_self : causalForm cMinusLift cMinusLift = 0 := by
  simp [causalForm, cMinusLift, cMinus]

theorem causalForm_ePlus_self : causalForm ePlusLift ePlusLift = 0 := by
  simp [causalForm, ePlusLift, ePlus]

theorem causalForm_eMinus_self : causalForm eMinusLift eMinusLift = 0 := by
  simp [causalForm, eMinusLift, eMinus]

theorem causalForm_cPlus_cMinus :
    causalForm cPlusLift cMinusLift = -2 := by
  simp [causalForm, cPlusLift, cPlus, cMinusLift, cMinus]
  ring

theorem causalForm_ePlus_eMinus :
    causalForm ePlusLift eMinusLift = -2 := by
  simp [causalForm, ePlusLift, ePlus, eMinusLift, eMinus]
  ring

def doubleWittToFin4 : Carrier ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  { toFun := fun x => ![x.1 0, x.1 1, x.2 0, x.2 1]
    invFun := fun x => (![x 0, x 1], ![x 2, x 3])
    left_inv := by
      intro x
      rcases x with ⟨c, e⟩
      apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · funext i
        fin_cases i <;> rfl
    right_inv := by
      intro x
      funext i
      fin_cases i <;> rfl
    map_add' := by
      intro x y
      funext i
      fin_cases i <;> simp
    map_smul' := by
      intro a x
      funext i
      fin_cases i <;> simp }

theorem doubleWittToFin4_apply (x : Carrier) :
    doubleWittToFin4 x = ![x.1 0, x.1 1, x.2 0, x.2 1] := rfl

theorem doubleWitt_causal_planes_are_null :
    causalForm cPlusLift cPlusLift = 0 ∧
      causalForm cMinusLift cMinusLift = 0 ∧
      causalForm ePlusLift ePlusLift = 0 ∧
      causalForm eMinusLift eMinusLift = 0 := by
  exact ⟨causalForm_cPlus_self, causalForm_cMinus_self,
    causalForm_ePlus_self, causalForm_eMinus_self⟩

end InfoGeometry.Geometry.RealDoubleWittNP
