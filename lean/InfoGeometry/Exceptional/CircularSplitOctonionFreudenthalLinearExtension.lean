import InfoGeometry.Exceptional.CircularSplitOctonionContactLift

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
    Finsupp.linearCombination ℝ (fun b =>
      FreudenthalCharge.symplecticForm D
        (circularCharge rootMapPlus rootMapMinus a)
        (circularCharge rootMapPlus rootMapMinus b)))

@[simp] theorem circularSymplecticLinear_single_single
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a b : CircularChargeAtom) :
    circularSymplecticLinear D rootMapPlus rootMapMinus
        (Finsupp.single a 1) (Finsupp.single b 1) =
      FreudenthalCharge.symplecticForm D
        (circularCharge rootMapPlus rootMapMinus a)
        (circularCharge rootMapPlus rootMapMinus b) := by
  simp [circularSymplecticLinear]

end
end InfoGeometry.Exceptional.Freudenthal
