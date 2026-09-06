import InfoGeometry.Clifford.Cl55CARSpinAutomorphism

/-!
# Chiral grand-canonical generators in `Cl(5,5)`

This file keeps the two sheet observables inside the noncommutative Clifford
algebra.  The two distinguished CAR modes are the concrete sheets; their
number operators are quadratic Clifford elements.  Chemical potentials are
real scalars acting on these elements, while all products below remain
products in `Cl55`.

Only algebraic conservation is proved here.  A KMS state or an analytic
modular flow requires additional analytic data and is therefore not inferred
from the generator alone.
-/

namespace InfoGeometry.Clifford.Clifford55

open SplitClifford

noncomputable def chiralPlusNumber55 : Cl55 :=
  mixedGenerator55 0 0

noncomputable def chiralMinusNumber55 : Cl55 :=
  mixedGenerator55 1 1

noncomputable def chiralTotalNumber55 : Cl55 :=
  chiralPlusNumber55 + chiralMinusNumber55

noncomputable def chiralCharge55 : Cl55 :=
  chiralPlusNumber55 - chiralMinusNumber55

@[simp] theorem chiralTotalNumber55_eq :
    chiralTotalNumber55 = chiralPlusNumber55 + chiralMinusNumber55 := rfl

@[simp] theorem chiralCharge55_eq :
    chiralCharge55 = chiralPlusNumber55 - chiralMinusNumber55 := rfl

/-! The two chemical potentials are decomposed into mean and chiral parts. -/

noncomputable def meanChemicalPotential (μplus μminus : ℝ) : ℝ :=
  (μplus + μminus) / 2

noncomputable def chiralChemicalPotential (μplus μminus : ℝ) : ℝ :=
  (μplus - μminus) / 2

theorem chemicalPotential_decomposition
    (μplus μminus : ℝ) :
    μplus • chiralPlusNumber55 + μminus • chiralMinusNumber55 =
      meanChemicalPotential μplus μminus • chiralTotalNumber55 +
        chiralChemicalPotential μplus μminus • chiralCharge55 := by
  simp only [meanChemicalPotential, chiralChemicalPotential,
    chiralTotalNumber55, chiralCharge55, smul_add, smul_sub,
    div_eq_mul_inv]
  module

noncomputable def chiralGrandCanonicalGenerator55
    (H : Cl55) (μplus μminus : ℝ) : Cl55 :=
  H - μplus • chiralPlusNumber55 - μminus • chiralMinusNumber55

theorem chiralGrandCanonicalGenerator55_eq_decomposed
    (H : Cl55) (μplus μminus : ℝ) :
    chiralGrandCanonicalGenerator55 H μplus μminus =
      H - meanChemicalPotential μplus μminus • chiralTotalNumber55 -
        chiralChemicalPotential μplus μminus • chiralCharge55 := by
  rw [chiralGrandCanonicalGenerator55]
  have hdecomp := chemicalPotential_decomposition μplus μminus
  rw [sub_sub, sub_sub, hdecomp]

def chiralChargeConserved55 (H : Cl55) : Prop :=
  H * chiralCharge55 = chiralCharge55 * H

theorem chiralGrandCanonicalGenerator55_commutes_charge
    (H : Cl55) (μplus μminus : ℝ)
    (hH : chiralChargeConserved55 H)
    (hPlus : chiralPlusNumber55 * chiralCharge55 =
      chiralCharge55 * chiralPlusNumber55)
    (hMinus : chiralMinusNumber55 * chiralCharge55 =
      chiralCharge55 * chiralMinusNumber55) :
    chiralGrandCanonicalGenerator55 H μplus μminus * chiralCharge55 =
      chiralCharge55 * chiralGrandCanonicalGenerator55 H μplus μminus := by
  have hp : (μplus • chiralPlusNumber55) * chiralCharge55 =
      chiralCharge55 * (μplus • chiralPlusNumber55) := by
    rw [smul_mul_assoc, mul_smul_comm, hPlus]
  have hm : (μminus • chiralMinusNumber55) * chiralCharge55 =
      chiralCharge55 * (μminus • chiralMinusNumber55) := by
    rw [smul_mul_assoc, mul_smul_comm, hMinus]
  calc
    chiralGrandCanonicalGenerator55 H μplus μminus * chiralCharge55 =
        H * chiralCharge55 -
          (μplus • chiralPlusNumber55) * chiralCharge55 -
          (μminus • chiralMinusNumber55) * chiralCharge55 := by
            simp [chiralGrandCanonicalGenerator55, sub_mul]
    _ = chiralCharge55 * H -
          chiralCharge55 * (μplus • chiralPlusNumber55) -
          chiralCharge55 * (μminus • chiralMinusNumber55) := by
            rw [hH, hp, hm]
    _ = chiralCharge55 * chiralGrandCanonicalGenerator55 H μplus μminus := by
            simp [chiralGrandCanonicalGenerator55, mul_sub, sub_mul]

theorem chiralNumber55_commutator_creation
    (j : Fin 5) (hj : j = 0) :
    chiralPlusNumber55 * creation55 j - creation55 j * chiralPlusNumber55 =
      creation55 j := by
  subst j
  simpa [chiralPlusNumber55] using
    mixedGenerator55_commutator_creation 0 0 0

theorem chiralNumber55_commutator_annihilation
    (j : Fin 5) (hj : j = 0) :
    chiralPlusNumber55 * annihilation55 j - annihilation55 j * chiralPlusNumber55 =
      -(annihilation55 j) := by
  subst j
  simpa [chiralPlusNumber55] using
    mixedGenerator55_commutator_annihilation 0 0 0

theorem zeroChiralGrandCanonical_commutator_creation_plus
    (μplus μminus : ℝ) :
    chiralGrandCanonicalGenerator55 0 μplus μminus * creation55 0 -
        creation55 0 * chiralGrandCanonicalGenerator55 0 μplus μminus =
      -(μplus • creation55 0) := by
  have hp : (μplus • chiralPlusNumber55) * creation55 0 -
      creation55 0 * (μplus • chiralPlusNumber55) = μplus • creation55 0 := by
    rw [smul_mul_assoc, mul_smul_comm]
    rw [← smul_sub]
    simpa [chiralPlusNumber55] using congrArg (fun x : Cl55 => μplus • x)
      (mixedGenerator55_commutator_creation 0 0 0)
  have hm : (μminus • chiralMinusNumber55) * creation55 0 -
      creation55 0 * (μminus • chiralMinusNumber55) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm]
    rw [← smul_sub]
    simpa [chiralMinusNumber55] using congrArg (fun x : Cl55 => μminus • x)
      (mixedGenerator55_commutator_creation 1 1 0)
  rw [chiralGrandCanonicalGenerator55]
  simp only [zero_sub]
  calc
    (-(μplus • chiralPlusNumber55) - μminus • chiralMinusNumber55) * creation55 0 -
        creation55 0 * (-(μplus • chiralPlusNumber55) -
          μminus • chiralMinusNumber55) =
      -((μplus • chiralPlusNumber55) * creation55 0 -
        creation55 0 * (μplus • chiralPlusNumber55)) -
      ((μminus • chiralMinusNumber55) * creation55 0 -
        creation55 0 * (μminus • chiralMinusNumber55)) := by noncomm_ring
    _ = -(μplus • creation55 0) := by rw [hp, hm]; simp

theorem zeroChiralGrandCanonical_commutator_annihilation_plus
    (μplus μminus : ℝ) :
    chiralGrandCanonicalGenerator55 0 μplus μminus * annihilation55 0 -
        annihilation55 0 * chiralGrandCanonicalGenerator55 0 μplus μminus =
      μplus • annihilation55 0 := by
  have hp : (μplus • chiralPlusNumber55) * annihilation55 0 -
      annihilation55 0 * (μplus • chiralPlusNumber55) =
        -(μplus • annihilation55 0) := by
    rw [smul_mul_assoc, mul_smul_comm]
    rw [← smul_sub]
    simpa [chiralPlusNumber55] using congrArg (fun x : Cl55 => μplus • x)
      (mixedGenerator55_commutator_annihilation 0 0 0)
  have hm : (μminus • chiralMinusNumber55) * annihilation55 0 -
      annihilation55 0 * (μminus • chiralMinusNumber55) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm]
    rw [← smul_sub]
    simpa [chiralMinusNumber55] using congrArg (fun x : Cl55 => μminus • x)
      (mixedGenerator55_commutator_annihilation 1 1 0)
  rw [chiralGrandCanonicalGenerator55]
  simp only [zero_sub]
  calc
    (-(μplus • chiralPlusNumber55) - μminus • chiralMinusNumber55) * annihilation55 0 -
        annihilation55 0 * (-(μplus • chiralPlusNumber55) -
          μminus • chiralMinusNumber55) =
      -((μplus • chiralPlusNumber55) * annihilation55 0 -
        annihilation55 0 * (μplus • chiralPlusNumber55)) -
      ((μminus • chiralMinusNumber55) * annihilation55 0 -
        annihilation55 0 * (μminus • chiralMinusNumber55)) := by noncomm_ring
    _ = μplus • annihilation55 0 := by rw [hp, hm]; simp

end InfoGeometry.Clifford.Clifford55
