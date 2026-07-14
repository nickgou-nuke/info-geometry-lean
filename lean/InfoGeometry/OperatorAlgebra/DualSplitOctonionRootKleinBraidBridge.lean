import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.OperatorAlgebra.DualSplitOctonionAlgebra
import InfoGeometry.OperatorAlgebra.ChiralTripotentSuperTKKLedger
import InfoGeometry.Canonical.O55TKKAnomalyAnnihilation
import InfoGeometry.Topology.ParafermionBraiding
import InfoGeometry.Topology.WallpaperKleinBottlePresentation

/-!
# Dual split-octonion root / tripotent / Klein / braid bridge

This file extracts finite algebraic claims from the dual split-octonion narrative
and wires them to existing owners:

* the central pair `{I,-I}` is even in the finite `Z₂` grading;
* odd roots stay even when their power lands in the central even layer, while
  square roots may be odd;
* the concrete tripotent diagonal operator has spectrum labels `{-1,0,1}` and
  satisfies `T^3 = T`;
* a finite `Z₃` clock cycle returns after three steps;
* a block Klein monodromy witness satisfies `M_y M_x M_y = M_x⁻¹` in the
  exact sign case;
* the `G₂` Coxeter/Artin braid word of length six is represented by two
  reflections of the six-cycle.

The file does not assert analytic braid operators, particle-sector models,
continuum cancellation results, or compactification classifications.
-/

namespace DualSplitOctonionRootKleinBraidBridge

open Matrix

/-! ## `Z₂` root grading of the central sign layer -/

/-- `false` is even and `true` is odd.  The grade of an `n`-fold product. -/
def z2PowerGrade (n : Nat) (g : Bool) : Bool :=
  if n % 2 = 0 then false else g

/-- Odd powers landing in the central even layer force the input grade to be even. -/
theorem odd_power_to_even_forces_even (g : Bool) :
    z2PowerGrade 3 g = false → g = false := by
  cases g <;> decide

/-- A square root of an even central element may carry odd grade. -/
theorem square_root_grade_one_lands_even :
    z2PowerGrade 2 true = false := by
  rfl

/-- A fourth root of an even central element may also carry odd grade. -/
theorem fourth_root_grade_one_lands_even :
    z2PowerGrade 4 true = false := by
  rfl

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- The finite identity matrix. -/
def I2Z : Mat2Z := 1

/-- The central sign `-I`. -/
def negI2Z : Mat2Z := -1

/-- Both central signs are assigned even grade. -/
def centralSignGrade (_A : Mat2Z) : Bool := false

/-- The central sign pair is even in the finite `Z₂` grading. -/
theorem central_sign_pair_even :
    centralSignGrade I2Z = false ∧ centralSignGrade negI2Z = false := by
  exact ⟨rfl, rfl⟩

/-- The negative identity squares to the identity. -/
theorem negI2Z_sq : negI2Z * negI2Z = I2Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ## Tripotent and `Z₃` clock readouts -/

abbrev Mat3Z := Matrix (Fin 3) (Fin 3) ℤ

/-- Diagonal tripotent with entries `-1,0,1`. -/
def tripotentZ3 : Mat3Z :=
  !![-1, 0, 0;
      0, 0, 0;
      0, 0, 1]

/-- Concrete `T^3 = T` tripotent identity. -/
theorem tripotentZ3_cube :
    tripotentZ3 * tripotentZ3 * tripotentZ3 = tripotentZ3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Three-state sector labels used for the finite clock shadow. -/
inductive Z3Sector where
  | zero | one | two
  deriving DecidableEq, Repr

/-- Clock rotation `0 → 1 → 2 → 0`. -/
def z3Rotate : Z3Sector → Z3Sector
  | .zero => .one
  | .one => .two
  | .two => .zero

/-- One full `Z₃` clock cycle is the identity. -/
theorem z3Rotate_cube (s : Z3Sector) :
    z3Rotate (z3Rotate (z3Rotate s)) = s := by
  cases s <;> rfl

/-! ## Finite Klein monodromy block witness -/

abbrev Mat8Z := Matrix (Fin 8) (Fin 8) ℤ

/-- Central sign monodromy `-I₈`. -/
def Mx : Mat8Z :=
  -1

/-- Cross-cap block swap between the two four-dimensional halves. -/
def My : Mat8Z :=
  fun i j => if (i.val + 4 = j.val) ∨ (j.val + 4 = i.val) then 1 else 0

/-- In the central-sign finite witness, `M_x` is its own inverse. -/
theorem Mx_sq : Mx * Mx = (1 : Mat8Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The block-swap cross-cap is an involution. -/
theorem My_sq : My * My = (1 : Mat8Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Exact Klein monodromy relation in the finite central-sign block witness. -/
theorem klein_monodromy_relation :
    My * Mx * My = Mx := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Equivalent `M_y M_x M_y = M_x⁻¹` readout using `M_x² = I`. -/
theorem klein_monodromy_relation_inverse_form :
    My * Mx * My = Mx ∧ Mx * Mx = (1 : Mat8Z) := by
  exact ⟨klein_monodromy_relation, Mx_sq⟩

/-! ## `G₂` Coxeter/Artin length-six finite shadow -/

/-- First reflection of the six-cycle. -/
def g2s : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 5
  | 2 => 4
  | 3 => 3
  | 4 => 2
  | 5 => 1

/-- Second reflection of the six-cycle. -/
def g2t : Fin 6 → Fin 6
  | 0 => 1
  | 1 => 0
  | 2 => 5
  | 3 => 4
  | 4 => 3
  | 5 => 2

/-- Left length-six Artin word for Coxeter exponent `m=6`. -/
def g2ArtinLeft (x : Fin 6) : Fin 6 :=
  g2s (g2t (g2s (g2t (g2s (g2t x)))))

/-- Right length-six Artin word for Coxeter exponent `m=6`. -/
def g2ArtinRight (x : Fin 6) : Fin 6 :=
  g2t (g2s (g2t (g2s (g2t (g2s x)))))

/-- Finite `G₂` Coxeter/Artin braid relation `(st)^3=(ts)^3` on the six-cycle. -/
theorem g2_artin_length_six (x : Fin 6) :
    g2ArtinLeft x = g2ArtinRight x := by
  fin_cases x <;> rfl

/-- Consolidated finite bridge packet. -/
theorem dual_split_octonion_root_klein_braid_packet :
    z2PowerGrade 2 true = false ∧
      centralSignGrade I2Z = false ∧
      centralSignGrade negI2Z = false ∧
      negI2Z * negI2Z = I2Z ∧
      tripotentZ3 * tripotentZ3 * tripotentZ3 = tripotentZ3 ∧
      (∀ s : Z3Sector, z3Rotate (z3Rotate (z3Rotate s)) = s) ∧
      My * Mx * My = Mx ∧
      Mx * Mx = (1 : Mat8Z) ∧
      (∀ x : Fin 6, g2ArtinLeft x = g2ArtinRight x) := by
  exact ⟨square_root_grade_one_lands_even, central_sign_pair_even.1,
    central_sign_pair_even.2, negI2Z_sq, tripotentZ3_cube, z3Rotate_cube,
    klein_monodromy_relation, Mx_sq, g2_artin_length_six⟩

end DualSplitOctonionRootKleinBraidBridge
