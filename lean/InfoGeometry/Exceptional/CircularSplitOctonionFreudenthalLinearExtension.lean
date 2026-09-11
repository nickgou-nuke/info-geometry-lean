import InfoGeometry.Exceptional.CircularSplitOctonionContactLift
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Linear extension of the circular charge readout

The atom-level map is extended to the free real module on the finite circular
alphabet.  This is deliberately not an identification with a Zorn carrier.
-/

namespace InfoGeometry.Exceptional.Freudenthal

noncomputable section

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

abbrev CircularChargeModule := CircularChargeAtom →₀ ℝ

noncomputable def circularChargeLinear
    (rootMapPlus rootMapMinus : Fin 3 → J) :
    CircularChargeModule →ₗ[ℝ] FreudenthalCharge J :=
  Finsupp.linearCombination ℝ
    (fun a : CircularChargeAtom => circularCharge rootMapPlus rootMapMinus a)

noncomputable def circularSymplecticForm
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x y : CircularChargeModule) : ℝ :=
  FreudenthalCharge.symplecticForm D
    (circularChargeLinear rootMapPlus rootMapMinus x)
    (circularChargeLinear rootMapPlus rootMapMinus y)

theorem circularSymplecticForm_apply
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x y : CircularChargeModule) :
    circularSymplecticForm D rootMapPlus rootMapMinus x y =
      FreudenthalCharge.symplecticForm D
        (circularChargeLinear rootMapPlus rootMapMinus x)
        (circularChargeLinear rootMapPlus rootMapMinus y) := rfl

theorem circularSymplecticForm_skew
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x y : CircularChargeModule) :
    circularSymplecticForm D rootMapPlus rootMapMinus x y =
      -circularSymplecticForm D rootMapPlus rootMapMinus y x := by
  exact FreudenthalCharge.symplectic_form_skew D _ _

theorem circularSymplecticForm_add_left
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x x' y : CircularChargeModule) :
    circularSymplecticForm D rootMapPlus rootMapMinus (x + x') y =
      circularSymplecticForm D rootMapPlus rootMapMinus x y +
        circularSymplecticForm D rootMapPlus rootMapMinus x' y := by
  simp [circularSymplecticForm, circularChargeLinear]

theorem circularSymplecticForm_add_right
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x y y' : CircularChargeModule) :
    circularSymplecticForm D rootMapPlus rootMapMinus x (y + y') =
      circularSymplecticForm D rootMapPlus rootMapMinus x y +
        circularSymplecticForm D rootMapPlus rootMapMinus x y' := by
  simp [circularSymplecticForm, circularChargeLinear]

theorem circularRankTwo_readback
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x y z : CircularChargeModule) :
    symplecticRankTwo D
        (circularChargeLinear rootMapPlus rootMapMinus x)
        (circularChargeLinear rootMapPlus rootMapMinus y)
        (circularChargeLinear rootMapPlus rootMapMinus z) =
      circularSymplecticForm D rootMapPlus rootMapMinus y z •
          circularChargeLinear rootMapPlus rootMapMinus x +
        circularSymplecticForm D rootMapPlus rootMapMinus x z •
          circularChargeLinear rootMapPlus rootMapMinus y := by
  rw [symplecticRankTwo_apply]
  rfl

@[simp] theorem circularChargeLinear_single
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a : CircularChargeAtom) (r : ℝ) :
    circularChargeLinear rootMapPlus rootMapMinus (Finsupp.single a r) =
      r • circularCharge rootMapPlus rootMapMinus a := by
  simp [circularChargeLinear]

@[simp] theorem circularChargeLinear_zero
    (rootMapPlus rootMapMinus : Fin 3 → J) :
    circularChargeLinear rootMapPlus rootMapMinus 0 = 0 := by
  simp [circularChargeLinear]

theorem circularChargeLinear_add
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x y : CircularChargeModule) :
    circularChargeLinear rootMapPlus rootMapMinus (x + y) =
      circularChargeLinear rootMapPlus rootMapMinus x +
        circularChargeLinear rootMapPlus rootMapMinus y := by
  simp

theorem circularChargeLinear_smul
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (r : ℝ) (x : CircularChargeModule) :
    circularChargeLinear rootMapPlus rootMapMinus (r • x) =
      r • circularChargeLinear rootMapPlus rootMapMinus x := by
  simp

theorem circularChargeLinear_atom_readback
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a : CircularChargeAtom) :
    circularChargeLinear rootMapPlus rootMapMinus (Finsupp.single a 1) =
      circularCharge rootMapPlus rootMapMinus a := by
  simpa only [one_smul] using
    circularChargeLinear_single rootMapPlus rootMapMinus a 1

theorem circularChargeLinear_apply
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x : CircularChargeModule) :
    circularChargeLinear rootMapPlus rootMapMinus x =
      Finsupp.sum x (fun a r => r • circularCharge rootMapPlus rootMapMinus a) := by
  rfl

noncomputable def circularSymplecticLinear
    (rootMapPlus rootMapMinus : Fin 3 → J) :
    CircularChargeModule →ₗ[ℝ]
      CircularChargeModule →ₗ[ℝ] ℝ :=
  Finsupp.lsum ℝ (fun a =>
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight
      (Finsupp.linearCombination ℝ (fun b =>
        FreudenthalCharge.symplecticForm D
          (circularCharge rootMapPlus rootMapMinus a)
          (circularCharge rootMapPlus rootMapMinus b))))

@[simp] theorem circularSymplecticLinear_single_single
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a b : CircularChargeAtom) :
    circularSymplecticLinear (D := D) rootMapPlus rootMapMinus
        (Finsupp.single a 1) (Finsupp.single b 1) =
      FreudenthalCharge.symplecticForm D
        (circularCharge rootMapPlus rootMapMinus a)
        (circularCharge rootMapPlus rootMapMinus b) := by
  simp [circularSymplecticLinear]

theorem circularSymplecticLinear_eq_pullback
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x y : CircularChargeModule) :
    circularSymplecticLinear (D := D) rootMapPlus rootMapMinus x y =
      FreudenthalCharge.symplecticForm D
        (circularChargeLinear rootMapPlus rootMapMinus x)
        (circularChargeLinear rootMapPlus rootMapMinus y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
      simp only [map_add, LinearMap.add_apply, symplecticForm_add_left, hx₁, hx₂]
  | single a r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ =>
          simp only [map_add, symplecticForm_add_right, hy₁, hy₂]
      | single b s =>
          simp [circularSymplecticLinear, circularChargeLinear,
            symplecticForm_smul_left, symplecticForm_smul_right]
          ring

theorem circularRankTwo_intertwining
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x y z : CircularChargeModule) :
    symplecticRankTwo D
        (circularChargeLinear rootMapPlus rootMapMinus x)
        (circularChargeLinear rootMapPlus rootMapMinus y)
        (circularChargeLinear rootMapPlus rootMapMinus z) =
      circularChargeLinear rootMapPlus rootMapMinus
        (circularSymplecticLinear (D := D) rootMapPlus rootMapMinus y z • x +
          circularSymplecticLinear (D := D) rootMapPlus rootMapMinus x z • y) := by
  rw [symplecticRankTwo_apply]
  rw [← circularSymplecticLinear_eq_pullback D rootMapPlus rootMapMinus y z,
    ← circularSymplecticLinear_eq_pullback D rootMapPlus rootMapMinus x z]
  simp only [map_add, map_smul]

theorem circularSymplecticLinear_swap
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x y : CircularChargeModule) :
    circularSymplecticLinear (D := D) rootMapPlus rootMapMinus x y =
      -circularSymplecticLinear (D := D) rootMapPlus rootMapMinus y x := by
  rw [circularSymplecticLinear_eq_pullback D rootMapPlus rootMapMinus,
    circularSymplecticLinear_eq_pullback D rootMapPlus rootMapMinus]
  exact FreudenthalCharge.symplectic_form_skew D _ _

theorem circularSymplecticLinear_self
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (x : CircularChargeModule) :
    circularSymplecticLinear (D := D) rootMapPlus rootMapMinus x x = 0 := by
  have h := circularSymplecticLinear_swap D rootMapPlus rootMapMinus x x
  linarith

end
end InfoGeometry.Exceptional.Freudenthal
