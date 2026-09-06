import Mathlib

open Complex

def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s

def toSymmetryAdapted (s : ℂ) : ℂ := s - (1 / 2 : ℂ)
def fromSymmetryAdapted (z : ℂ) : ℂ := z + (1 / 2 : ℂ)

def symmetryAdaptedXi (z : ℂ) : ℂ := riemannXi (fromSymmetryAdapted z)

theorem symmetryAdaptedXi_is_even (z : ℂ) :
    symmetryAdaptedXi z = symmetryAdaptedXi (-z) := by
  unfold symmetryAdaptedXi fromSymmetryAdapted riemannXi
  have h1 : -(z) + (1 / 2 : ℂ) = 1 - (z + (1 / 2 : ℂ)) := by ring
  rw [h1, completedRiemannZeta_one_sub]
  ring
