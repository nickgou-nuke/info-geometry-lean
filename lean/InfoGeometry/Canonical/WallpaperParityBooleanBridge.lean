/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge
import InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra

/-!
# Wallpaper lattice mod 2 as a Boolean sector

The square lattice `Λ = ℤ²` reduces modulo 2 to `Λ / 2Λ ≅ (ℤ/2)²`, the
two-generator Boolean sector. Translation acts by XOR; the diagonal reflection
acts by the coordinate swap; the axis reflection acts trivially. This last fact
is the honest limitation: signs are invisible modulo 2, so the hyperoctahedral
sign flips live on the signed root lattice `A₁²`, not on `Λ / 2Λ`.
-/
namespace InfoGeometry.Canonical.WallpaperParityBooleanBridge

open InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge
open InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra
open InfoGeometry.Canonical.KreinProjectorLattice

/-- Parity class of a lattice vector, as a pair of bits. -/
def wallpaperParity (t : Z2) : Fin 2 → Bool :=
  ![t.1.bodd, t.2.bodd]

theorem wallpaperParity_add (s t : Z2) :
    wallpaperParity (s + t) = wallpaperParity s + wallpaperParity t := by
  funext i
  fin_cases i <;> simp [wallpaperParity, Int.bodd_add]
  all_goals cases s.1.bodd <;> cases t.1.bodd <;> rfl

theorem wallpaperParity_neg (t : Z2) :
    wallpaperParity (-t) = wallpaperParity t := by
  funext i
  fin_cases i <;> simp [wallpaperParity, Int.bodd_neg]

theorem wallpaperParity_sigmaX (t : Z2) :
    wallpaperParity (sigmaX t) = wallpaperParity t := by
  funext i
  fin_cases i <;> simp [wallpaperParity, sigmaX, Int.bodd_neg]

/-- Permutation action on bit vectors (precomposition by the inverse). -/
def permBool (σ : Equiv.Perm (Fin 2)) (b : Fin 2 → Bool) : Fin 2 → Bool :=
  fun i => b (σ.symm i)

theorem wallpaperParity_sigmaD (t : Z2) :
    wallpaperParity (sigmaD t) =
      permBool (Equiv.swap (0 : Fin 2) (1 : Fin 2)) (wallpaperParity t) := by
  funext i
  fin_cases i <;> simp [wallpaperParity, sigmaD, permBool]

/-- Embed a bit vector into the two-generator Boolean sector. -/
def parityToSector (b : Fin 2 → Bool) : Sector 2 :=
  fun i => if b i = true then KreinSector.plus else KreinSector.minus

theorem wallpaperParity_sigmaX_sector (t : Z2) :
    parityToSector (wallpaperParity (sigmaX t)) =
      parityToSector (wallpaperParity t) := by
  rw [wallpaperParity_sigmaX]

theorem wallpaperParity_sigmaD_sector (t : Z2) :
    parityToSector (wallpaperParity (sigmaD t)) =
      (Equiv.swap (0 : Fin 2) (1 : Fin 2)) • parityToSector (wallpaperParity t) := by
  rw [wallpaperParity_sigmaD]
  funext i
  fin_cases i
  · change parityToSector (permBool (Equiv.swap (0 : Fin 2) 1) (wallpaperParity t)) 0 =
      parityToSector (wallpaperParity t) ((Equiv.swap (0 : Fin 2) 1).symm 0)
    simp [parityToSector, permBool]
  · change parityToSector (permBool (Equiv.swap (0 : Fin 2) 1) (wallpaperParity t)) 1 =
      parityToSector (wallpaperParity t) ((Equiv.swap (0 : Fin 2) 1).symm 1)
    simp [parityToSector, permBool]

theorem wallpaperParity_surjective : Function.Surjective wallpaperParity := by
  intro b
  refine ⟨((if b 0 = true then 1 else 0 : ℤ), (if b 1 = true then 1 else 0 : ℤ)), ?_⟩
  funext i
  fin_cases i <;> by_cases h0 : b 0 = true <;> by_cases h1 : b 1 = true <;>
    simp [wallpaperParity, h0, h1, Int.bodd]

end InfoGeometry.Canonical.WallpaperParityBooleanBridge
