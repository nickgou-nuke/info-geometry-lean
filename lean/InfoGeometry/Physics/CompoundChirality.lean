import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics.CompoundChirality

open Algebra.FiniteSpin

noncomputable section

def halfTurnAboutSecondAxis (spin : Vec3R) : Vec3R :=
  ![-spin 0, spin 1, -spin 2]

def reverseSpin (spin : Vec3R) : Vec3R := -spin

def rotationAfterReversal (spin : Vec3R) : Vec3R :=
  halfTurnAboutSecondAxis (reverseSpin spin)

theorem rotationAfterReversal_coordinates (spin : Vec3R) :
    rotationAfterReversal spin = ![spin 0, -spin 1, spin 2] := by
  ext coordinate
  fin_cases coordinate <;> simp [rotationAfterReversal, halfTurnAboutSecondAxis, reverseSpin]

theorem rotationAfterReversal_involutive : Function.Involutive rotationAfterReversal := by
  intro spin
  ext coordinate
  fin_cases coordinate <;> simp [rotationAfterReversal_coordinates]

theorem rotationAfterReversal_preserves_first (spin : Vec3R) :
    rotationAfterReversal spin 0 = spin 0 := by
  simp [rotationAfterReversal_coordinates]

theorem rotationAfterReversal_reverses_second (spin : Vec3R) :
    rotationAfterReversal spin 1 = -spin 1 := by
  simp [rotationAfterReversal_coordinates]

theorem rotationAfterReversal_preserves_third (spin : Vec3R) :
    rotationAfterReversal spin 2 = spin 2 := by
  simp [rotationAfterReversal_coordinates]

theorem rotationAfterReversal_need_not_negate_spin :
    ∃ spin : Vec3R, rotationAfterReversal spin ≠ -spin := by
  refine ⟨![1, 2, 3], ?_⟩
  intro equal
  have coordinate := congrFun equal 0
  norm_num [rotationAfterReversal_coordinates] at coordinate

def residualSpin (initial emitted : Vec3R) : Vec3R := initial - emitted

theorem residualSpin_balance (initial emitted : Vec3R) :
    residualSpin initial emitted + emitted = initial := by
  simp [residualSpin]

theorem residualSpin_can_vanish (initial : Vec3R) : residualSpin initial initial = 0 := by
  simp [residualSpin]

end

end InfoGeometry.Physics.CompoundChirality
