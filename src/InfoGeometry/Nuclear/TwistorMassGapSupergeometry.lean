import Mathlib.Data.Complex.Basic
import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Twistor.FiniteAmbitwistorParaKahler
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Nuclear.TwistorMassGapSupergeometry

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.FiniteAmbitwistorParaKahler

def twistor_chiral_volume (Z : Twistor4) : ℂ :=
  spinorPairing Z.1 Z.2 - spinorPairing Z.2 Z.1

def is_incident (Z : Twistor4) (X : ComplexSpacetime) : Prop :=
  Z.1 = omegaLinearMap X Z.2

def is_real_spacetime (X : ComplexSpacetime) : Prop :=
  ∀ i j, X i j = star (X j i)

theorem incidence_generates_masslessness (Z : Twistor4) (X : ComplexSpacetime)
    (h_real : is_real_spacetime X)
    (h_incident : is_incident Z X) :
    twistor_chiral_volume Z = 0 := by
  dsimp [twistor_chiral_volume, is_incident, omegaLinearMap] at *
  rw [h_incident]
  dsimp [spinorPairing, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two, map_add, map_mul]
  have h00 : (starRingEnd ℂ) (X 0 0) = X 0 0 := (h_real 0 0).symm
  have h11 : (starRingEnd ℂ) (X 1 1) = X 1 1 := (h_real 1 1).symm
  have h10 : (starRingEnd ℂ) (X 1 0) = X 0 1 := (h_real 0 1).symm
  have h01 : (starRingEnd ℂ) (X 0 1) = X 1 0 := (h_real 1 0).symm
  rw [h00, h11, h10, h01]
  ring

theorem mass_breaks_incidence (Z : Twistor4) (X : ComplexSpacetime)
    (h_real : is_real_spacetime X)
    (h_massive : twistor_chiral_volume Z ≠ 0) :
    ¬ is_incident Z X := by
  intro h_inc
  exact h_massive (incidence_generates_masslessness Z X h_real h_inc)

end InfoGeometry.Nuclear.TwistorMassGapSupergeometry
