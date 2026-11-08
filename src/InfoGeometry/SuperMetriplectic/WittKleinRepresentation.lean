/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveKleinRepresentation
import InfoGeometry.SuperMetriplectic.WittWeylDiracSolder

/-! The presented Klein group acts by units on the actual neutral Witt
matrix carrier. Its first generator is the existing Majorana form, with
Dirac right action on arbitrary ket–bras. -/
noncomputable section
namespace InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
open Matrix InfoGeometry.Quantum.NeutralKreinMajoranaFrame
open InfoGeometry.Canonical.ReflexiveNilpotentFlows
open InfoGeometry.Canonical.KleinPresentedGroup
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

def wittKleinRep (n : ℕ) (t : ℝˣ) : KleinGroup →* (Matrix2 n)ˣ :=
  reflexiveKleinRep (wittAnnihilator_sq_zero n) (wittCreator_sq_zero n)
    (wittAnnihilator_inner_inverse n) (wittCreator_inner_inverse n) t

@[simp] theorem wittKleinRep_genA (n : ℕ) (t : ℝˣ) :
    (wittKleinRep n t (toKlein genA) : Matrix2 n) = majoranaForm n := by
  unfold wittKleinRep
  rw [reflexiveKleinRep_genA]
  change weyl (wittAnnihilator n) (wittCreator n) = _
  simp only [weyl, complement, support, witt_car_anticomm, sub_self, zero_add,
    witt_difference_eq_majoranaForm]

@[simp] theorem wittKleinRep_genB (n : ℕ) (t : ℝˣ) :
    (wittKleinRep n t (toKlein genB) : Matrix2 n) =
      (t : ℝ) • (wittAnnihilator n * wittCreator n) +
        (↑(t⁻¹) : ℝ) • (wittCreator n * wittAnnihilator n) := by
  unfold wittKleinRep
  rw [reflexiveKleinRep_genB, diagonalUnit_val]
  simp only [InfoGeometry.Canonical.ReflexiveNilpotentFlows.diagonal, complement, support, witt_car_anticomm, sub_self, add_zero]

theorem solder_wittKleinRep_genA_right (n : ℕ) (t : ℝˣ) (l r : Carrier n → ℝ) :
    solder (kreinMetric n) l ((wittKleinRep n t (toKlein genA) : Matrix2 n) *ᵥ r) =
      solder (kreinMetric n) l r * majoranaForm n := by
  rw [wittKleinRep_genA]
  exact solder_majoranaForm_right n l r

end InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
