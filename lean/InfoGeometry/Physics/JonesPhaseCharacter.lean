/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.B3PresentedGroup

/-! The scalar phase and its removal on the existing presented braid group.
Descent of the phase-removed representation to S₃ is a separate construction. -/

noncomputable section
namespace InfoGeometry.Physics.JonesPhaseCharacter

open B3PresentedGroup

def imaginaryUnit : ℂˣ where
  val := Complex.I
  inv := -Complex.I
  val_inv := by simp
  inv_val := by simp

def phase : B3 →* ℂˣ := homOfArtinPair imaginaryUnit imaginaryUnit rfl

@[simp] theorem phase_generator (i : B3Gen) :
    phase (PresentedGroup.of i : B3) = imaginaryUnit := by
  cases i <;> simp [phase]

def scalarUnit : ℂˣ →* GL8 :=
  Units.map (algebraMap ℂ (Matrix (Fin 8) (Fin 8) ℂ)).toMonoidHom

theorem scalarUnit_commute (z : ℂˣ) (g : GL8) : Commute (scalarUnit z) g := by
  apply Units.ext
  exact Algebra.commutes (z : ℂ) (g : Matrix (Fin 8) (Fin 8) ℂ)

def phaseRemoved : B3 →* GL8 where
  toFun g := scalarUnit ((phase g)⁻¹) * phi g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, mul_inv_rev]
    rw [(scalarUnit_commute ((phase h)⁻¹) (scalarUnit ((phase g)⁻¹))).eq]
    exact ((scalarUnit_commute ((phase h)⁻¹) (phi g)).symm.mul_mul_mul_comm _ _).symm

theorem phase_factorization (g : B3) :
    phi g = scalarUnit (phase g) * phaseRemoved g := by
  change phi g = scalarUnit (phase g) * (scalarUnit ((phase g)⁻¹) * phi g)
  rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem phase_generator_square (i : B3Gen) :
    (phase ((PresentedGroup.of i : B3) * PresentedGroup.of i) : ℂ) = -1 := by
  simp [imaginaryUnit]

end InfoGeometry.Physics.JonesPhaseCharacter
