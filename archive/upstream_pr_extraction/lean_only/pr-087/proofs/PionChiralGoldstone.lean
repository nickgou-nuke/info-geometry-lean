import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Clifford.Cl55WittCircularAxes
import InfoGeometry.Clifford.Cl55CAROperatorLift

/-!
# Native chiral nilpotent sector in `Cl(5,5)`

This owner uses the repository's verified creation/annihilation elements in
the native real Clifford algebra.  It deliberately does not introduce a
second matrix carrier, an external `Complex.I`, or an unsupported
identification with a Pin/TKK physical model.

For a mode `i`, the charged pair is

* `piPlus i  = creation55 i`,
* `piMinus i = annihilation55 i`.

The neutral generator is the commutator half

`piZero i = (creation55 i * annihilation55 i -
             annihilation55 i * creation55 i) / 2`.

The existing native CAR theorem supplies the full proof of nilpotence,
the CAR relation, and the real `sl₂` bracket relations.  The hyperbolic and
elliptic Witt axes are the existing `Cl55WittCircularAxes` owners; the
nilpotent pair is recovered from them by half-sum/half-difference.

This file is an algebraic closure packet only.  Projective null boundaries,
lightcones, parabolic actions, and TKK gradings remain owned by their
respective modules and are not silently identified here.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

variable (i : Fin 5)

/-- Native charged raising element. -/
def piPlus : Cl55 := creation55 i

/-- Native charged lowering element. -/
def piMinus : Cl55 := annihilation55 i

/-- Native neutral Cartan element, with the usual CAR normalization. -/
def piZero : Cl55 :=
  mixedGenerator55 i i

@[simp] theorem piPlus_apply : piPlus i = creation55 i := rfl

@[simp] theorem piMinus_apply : piMinus i = annihilation55 i := rfl

@[simp] theorem piPlus_sq : piPlus i * piPlus i = 0 := by
  exact creation55_sq i

@[simp] theorem piMinus_sq : piMinus i * piMinus i = 0 := by
  exact annihilation55_sq i

theorem piPlus_piMinus_car :
    piPlus i * piMinus i + piMinus i * piPlus i = (1 : Cl55) := by
  simpa [piPlus, piMinus, add_comm] using
    annihilation55_creation55_anticommutator i

theorem piPlus_piMinus_lie :
    ⁅piPlus i, piMinus i⁆ = (2 : ℝ) • piZero i := by
  rw [LieRing.of_associative_ring_bracket]
  simp only [piPlus, piMinus, piZero]
  have hcar :
      annihilation55 i * creation55 i +
          creation55 i * annihilation55 i = (1 : Cl55) :=
    annihilation55_creation55_anticommutator i
  simp only [mixedGenerator55, if_pos, Algebra.smul_def]
  have hhalf :
      (algebraMap ℝ Cl55) 2 *
          (algebraMap ℝ Cl55 (1 / 2 : ℝ)) = 1 := by
    rw [← map_mul]
    norm_num
  rw [mul_sub, mul_one, hhalf]
  have hca :
      annihilation55 i * creation55 i =
        (1 : Cl55) - creation55 i * annihilation55 i :=
    eq_sub_of_add_eq hcar
  rw [hca]
  have htwo :
      (algebraMap ℝ Cl55) (2 : ℝ) = (1 : Cl55) + 1 := by
    norm_num [map_ofNat]
  rw [htwo]
  noncomm_ring

theorem piZero_piPlus_lie :
    ⁅piZero i, piPlus i⁆ = piPlus i := by
  rw [LieRing.of_associative_ring_bracket]
  simpa [piPlus, piZero, mixedGenerator55] using
    mixedGenerator55_commutator_creation i i i

theorem piZero_piMinus_lie :
    ⁅piZero i, piMinus i⁆ = -piMinus i := by
  rw [LieRing.of_associative_ring_bracket]
  simpa [piMinus, piZero, mixedGenerator55] using
    mixedGenerator55_commutator_annihilation i i i

theorem pi_chiral_car_closure :
    piPlus i * piPlus i = 0 ∧
    piMinus i * piMinus i = 0 ∧
    piPlus i * piMinus i + piMinus i * piPlus i = (1 : Cl55) ∧
    ⁅piPlus i, piMinus i⁆ = (2 : ℝ) • piZero i ∧
    ⁅piZero i, piPlus i⁆ = piPlus i ∧
    ⁅piZero i, piMinus i⁆ = -piMinus i := by
  exact ⟨piPlus_sq i, piMinus_sq i, piPlus_piMinus_car i,
    piPlus_piMinus_lie i, piZero_piPlus_lie i, piZero_piMinus_lie i⟩

theorem piPlus_from_witt_axes :
    piPlus i =
      (1 / 2 : ℝ) •
        (hyperbolicAxis55 i + ellipticAxis55 i) := by
  simp only [piPlus, hyperbolicAxis55, ellipticAxis55]
  rw [show creation55 i + annihilation55 i +
      (creation55 i - annihilation55 i) =
      creation55 i + creation55 i by abel]
  rw [← two_smul ℝ (creation55 i)]
  simp [smul_smul]

theorem piMinus_from_witt_axes :
    piMinus i =
      (1 / 2 : ℝ) •
        (hyperbolicAxis55 i - ellipticAxis55 i) := by
  simp only [piMinus, hyperbolicAxis55, ellipticAxis55]
  rw [show creation55 i + annihilation55 i -
      (creation55 i - annihilation55 i) =
        annihilation55 i + annihilation55 i by abel]
  rw [← two_smul ℝ (annihilation55 i)]
  simp [smul_smul]

theorem witt_axes_recover_piPlus :
    (1 / 2 : ℝ) •
        (hyperbolicAxis55 i + ellipticAxis55 i) = piPlus i := by
  exact (piPlus_from_witt_axes i).symm

theorem witt_axes_recover_piMinus :
    (1 / 2 : ℝ) •
        (hyperbolicAxis55 i - ellipticAxis55 i) = piMinus i := by
  exact (piMinus_from_witt_axes i).symm

/-! ### Genuine operator-valued readout -/

theorem pi_chiral_operator_car_closure :
    leftAction55 (piPlus i) * leftAction55 (piPlus i) = 0 ∧
    leftAction55 (piMinus i) * leftAction55 (piMinus i) = 0 ∧
    leftAction55 (piMinus i) * leftAction55 (piPlus i) +
        leftAction55 (piPlus i) * leftAction55 (piMinus i) = 1 := by
  constructor
  · rw [piPlus, ← leftAction55_mul, creation55_sq, leftAction55_zero]
  constructor
  · rw [piMinus, ← leftAction55_mul, annihilation55_sq, leftAction55_zero]
  · rw [piPlus, piMinus]
    exact cl55CAR_leftAction_anticommutator i

end InfoGeometry.Clifford.Clifford55

end
