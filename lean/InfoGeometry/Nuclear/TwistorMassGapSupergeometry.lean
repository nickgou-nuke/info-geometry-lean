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
  simp only [Fin.sum_univ_two, star_add, star_mul]
  have h00 := h_real 0 0
  have h01 := h_real 0 1
  have h10 := h_real 1 0
  have h11 := h_real 1 1
  rw [h00, h11, h10]
  ring_nf

theorem mass_breaks_incidence (Z : Twistor4) (X : ComplexSpacetime)
    (h_real : is_real_spacetime X)
    (h_massive : twistor_chiral_volume Z ≠ 0) :
    ¬ is_incident Z X := by
  intro h_inc
  exact h_massive (incidence_generates_masslessness Z X h_real h_inc)

end InfoGeometry.Nuclear.TwistorMassGapSupergeometry
