import InfoGeometry.Canonical.D6SixModeAction
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# A finite reciprocal-lattice and hexagonal Brillouin-zone readout

This owner fixes an explicit reciprocal-coordinate model for the six-mode
`D6` star.  It is deliberately finite and algebraic: it does not assert a
continuum Bloch theorem or the existence of Dirac points.
-/

namespace InfoGeometry.Canonical.D6ReciprocalLatticeBrillouinZone

open InfoGeometry.Canonical.D6SixModeAction

abbrev ReciprocalCoord := Fin 2 → ℤ

def hexStarFin : Fin 6 → ReciprocalCoord :=
  ![![1, 0], ![1, -1], ![0, -1], ![-1, 0], ![-1, 1], ![0, 1]]

def hexStar (k : D6Index) : ReciprocalCoord :=
  hexStarFin ⟨k.val, k.isLt⟩

def axialNorm (p : ReciprocalCoord) : ℤ :=
  max (max |p 0| |p 1|) |p 0 + p 1|

def reciprocalLatticePoint (m n : ℤ) : ReciprocalCoord := ![m, n]

def axialRotate (p : ReciprocalCoord) : ReciprocalCoord :=
  ![-p 1, p 0 + p 1]

def axialReflect (p : ReciprocalCoord) : ReciprocalCoord :=
  ![p 1, p 0]

def axialRotateInv (p : ReciprocalCoord) : ReciprocalCoord :=
  ![p 0 + p 1, -p 0]

def hexagonalBrillouinBoundary (p : Fin 2 → ℝ) : Prop :=
  max (max |p 0| |p 1|) |p 0 + p 1| = 1

def realAxialRotate (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-p 1, p 0 + p 1]

def realAxialReflect (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![p 1, p 0]

def hexagonalReciprocalShell (p : ReciprocalCoord) : Prop :=
  axialNorm p = 1

theorem hexStarFin_axialNorm (k : Fin 6) : axialNorm (hexStarFin k) = 1 := by
  fin_cases k <;> norm_num [axialNorm, hexStarFin]

theorem hexStar_axialNorm (k : D6Index) : axialNorm (hexStar k) = 1 := by
  exact hexStarFin_axialNorm ⟨k.val, k.isLt⟩

theorem rotation_hexStar_mem (k i : D6Index) :
    hexStar (rotation k i) ∈ Set.range hexStar := by
  exact ⟨rotation k i, rfl⟩

theorem reflection_hexStar_mem (i : D6Index) :
    hexStar (reflection i) ∈ Set.range hexStar := by
  exact ⟨reflection i, rfl⟩

theorem d6_hexStar_closed (i : D6Index) :
    hexStar i ∈ Set.range hexStar := by
  exact ⟨i, rfl⟩

theorem reciprocalLatticePoint_zero :
    reciprocalLatticePoint 0 0 = ![0, 0] := by
  rfl

theorem axialNorm_rotate (p : ReciprocalCoord) :
    axialNorm (axialRotate p) = axialNorm p := by
  simp [axialNorm, axialRotate, abs_neg, max_comm, max_left_comm]

theorem axialNorm_reflect (p : ReciprocalCoord) :
    axialNorm (axialReflect p) = axialNorm p := by
  simp [axialNorm, axialReflect, max_comm, max_left_comm]
  rw [add_comm (p 1) (p 0)]

theorem hexagonalReciprocalShell_rotate (p : ReciprocalCoord) :
    hexagonalReciprocalShell p ↔
      hexagonalReciprocalShell (axialRotate p) := by
  simp [hexagonalReciprocalShell, axialNorm_rotate]

theorem hexagonalReciprocalShell_reflect (p : ReciprocalCoord) :
    hexagonalReciprocalShell p ↔
      hexagonalReciprocalShell (axialReflect p) := by
  simp [hexagonalReciprocalShell, axialNorm_reflect]

theorem hexagonalBrillouinBoundary_rotate (p : Fin 2 → ℝ) :
    hexagonalBrillouinBoundary p ↔
      hexagonalBrillouinBoundary (realAxialRotate p) := by
  simp [hexagonalBrillouinBoundary, realAxialRotate, abs_neg,
    max_comm, max_left_comm]

theorem hexagonalBrillouinBoundary_reflect (p : Fin 2 → ℝ) :
    hexagonalBrillouinBoundary p ↔
      hexagonalBrillouinBoundary (realAxialReflect p) := by
  simp [hexagonalBrillouinBoundary, realAxialReflect, max_comm, max_left_comm]
  rw [add_comm (p 1) (p 0)]

theorem axialReflect_involutive (p : ReciprocalCoord) :
    axialReflect (axialReflect p) = p := by
  funext i
  fin_cases i <;> rfl

theorem axialRotate_mem_reciprocalLattice (p : ReciprocalCoord) :
    ∃ m n : ℤ, axialRotate p = reciprocalLatticePoint m n := by
  exact ⟨-p 1, p 0 + p 1, by rfl⟩

theorem axialReflect_mem_reciprocalLattice (p : ReciprocalCoord) :
    ∃ m n : ℤ, axialReflect p = reciprocalLatticePoint m n := by
  exact ⟨p 1, p 0, by rfl⟩

theorem axialRotate_sixth (p : ReciprocalCoord) :
    axialRotate (axialRotate (axialRotate
      (axialRotate (axialRotate (axialRotate p))))) = p := by
  funext i
  fin_cases i <;> simp [axialRotate]

theorem axialRotateInv_left (p : ReciprocalCoord) :
    axialRotateInv (axialRotate p) = p := by
  funext i
  fin_cases i <;> simp [axialRotate, axialRotateInv]

theorem axialRotateInv_right (p : ReciprocalCoord) :
    axialRotate (axialRotateInv p) = p := by
  funext i
  fin_cases i <;> simp [axialRotate, axialRotateInv]

theorem axialReflect_conjugates_rotate (p : ReciprocalCoord) :
    axialReflect (axialRotate (axialReflect p)) = axialRotateInv p := by
  funext i
  fin_cases i <;> simp [axialRotate, axialReflect, axialRotateInv, add_comm]

theorem hexStarFin_pairwise_ne : Function.Injective hexStarFin := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [hexStarFin] at h ⊢

end InfoGeometry.Canonical.D6ReciprocalLatticeBrillouinZone
