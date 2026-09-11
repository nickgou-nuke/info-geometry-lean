import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import InfoGeometry.Section7
import InfoGeometry.Section8
import InfoGeometry.Section12

/-!
# Section 3: Soldering Forms

This file closes the finite raw-Pauli soldering corridor for Section 3 and
records the exact boundary between the verified algebra and the curved
geometric claims in the source text.

#### BUCKET 1: CLOSED FINITE THEOREMS
The raw complex Pauli trace orthogonality, coordinate recovery, and
Minkowski-spinor completeness identity are proved directly.  Existing owners
also close the flat identity-tetrad metric, zero spin connection, flat
spinorial covariant constancy of soldering forms, flat tetrad postulate, and
flat Clifford-soldering derivative.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None in this file.  The curved tetrad and spin-bundle statements need a real
formal layer before they can be stated honestly as conditional theorems.

#### BUCKET 3: OPEN CLOSURE DEBT
No theorem here derives a curved spin connection from an arbitrary tetrad,
proves the general tetrad postulate, proves covariant constancy of curved
soldering forms, constructs smooth spinor/tangent bundles, or identifies a
Bogoliubov/Fock frame with a Pauli soldered tetrad frame.  Those remain open
until their precise formal premises and objects exist in the codebase.
-/

open scoped BigOperators

noncomputable section

namespace Section3

open Matrix

def s0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def sf : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3
def eta4 : Matrix (Fin 4) (Fin 4) ℂ := !![(-1),0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]
def eps : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem trace_ortho (a b : Fin 4) : ((∑ i : Fin 2, (sf a * sf b) i i) / (2 : ℂ)) = if a = b then (1 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;> simp [sf, s0, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two]

theorem vec_recover (t x y z : ℂ) (a : Fin 4) :
    ((∑ i : Fin 2, (sf a * (t • s0 + x • s1 + y • s2 + z • s3)) i i) / (2 : ℂ))
    = match a with | 0 => t | 1 => x | 2 => y | 3 => z := by
  fin_cases a <;> simp [sf, s0, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two]
  · ring_nf
  · ring_nf
  · ring_nf
    rw [show Complex.I ^ 2 = (-1 : ℂ) by simp [pow_two, Complex.I_mul_I]]
    ring_nf
  · ring_nf

theorem completeness (A B Ap Bp : Fin 2) :
    (∑ a : Fin 4, ∑ b : Fin 4, eta4 a b * sf a A Ap * sf b B Bp) = (-2 : ℂ) * eps A B * eps Ap Bp := by
  fin_cases A <;> fin_cases B <;> fin_cases Ap <;> fin_cases Bp <;>
    simp [sf, s0, s1, s2, s3, eta4, eps, Fin.sum_univ_four] <;> ring

/-! ## Flat and finite owners reused by Section 3 -/

/-- Section 7 owns the flat identity tetrad metric calculation. -/
theorem flat_tetrad_metric_owner :
    Section7.eTetradᵀ * Section7.eta4 * Section7.eTetrad = Section7.eta4 :=
  Section7.tetrad_metric_flat

/-- Section 7 owns the vanishing spin connection for the flat identity frame. -/
theorem flat_spin_connection_owner (mu : Fin 4) (A B : Fin 2) :
    Section7.spinConnection mu A B = 0 :=
  Section7.spin_connection_vanishes_flat mu A B

/-- Section 7 owns the flat covariant constancy shadow for soldering forms. -/
theorem flat_soldering_covariant_constancy_owner
    (a mu nu : Fin 4) (A Ap : Fin 2) :
    (∑ B : Fin 2, Section7.spinConnection mu A B * Section7.soldering a nu B Ap)
      - (∑ Bp : Fin 2,
          Section7.soldering a nu A Bp * Section7.spinConnection mu Bp Ap) = 0 :=
  Section7.soldering_covariant_constancy_flat a mu nu A Ap

/-- Section 8 owns the flat tetrad-postulate coefficient shadow. -/
theorem flat_tetrad_compatibility_owner (mu nu a : Fin 4) :
    (0 : ℝ) - 0 + Section8.Quat.spinConnectionFlat mu a nu = 0 :=
  Section8.Quat.tetrad_compatibility_flat mu nu a

/-- Section 12 owns the flat Clifford-soldering covariant-derivative shadow. -/
theorem flat_clifford_soldering_derivative_owner (E : Section12.SpinMat) :
    Section12.cliffordSolderingDerivative 0 0 E = 0 :=
  Section12.cliffordSolderingDerivative_flat E

/--
Finite Section 3 repair packet: raw Pauli soldering is closed, and the curved
language is restricted to existing flat/finite theorem owners.
-/
theorem repaired_section3_soldering_packet :
    (∀ a b : Fin 4,
      ((∑ i : Fin 2, (sf a * sf b) i i) / (2 : ℂ)) =
        if a = b then (1 : ℂ) else 0) ∧
    (∀ t x y z : ℂ, ∀ a : Fin 4,
      ((∑ i : Fin 2, (sf a * (t • s0 + x • s1 + y • s2 + z • s3)) i i)
          / (2 : ℂ)) =
        match a with | 0 => t | 1 => x | 2 => y | 3 => z) ∧
    (∀ A B Ap Bp : Fin 2,
      (∑ a : Fin 4, ∑ b : Fin 4, eta4 a b * sf a A Ap * sf b B Bp) =
        (-2 : ℂ) * eps A B * eps Ap Bp) ∧
    Section7.eTetradᵀ * Section7.eta4 * Section7.eTetrad = Section7.eta4 ∧
    (∀ mu A B, Section7.spinConnection mu A B = 0) ∧
    (∀ a mu nu A Ap,
      (∑ B : Fin 2, Section7.spinConnection mu A B * Section7.soldering a nu B Ap)
        - (∑ Bp : Fin 2,
            Section7.soldering a nu A Bp * Section7.spinConnection mu Bp Ap) = 0) ∧
    (∀ mu nu a, (0 : ℝ) - 0 + Section8.Quat.spinConnectionFlat mu a nu = 0) ∧
    (∀ E : Section12.SpinMat, Section12.cliffordSolderingDerivative 0 0 E = 0) := by
  exact ⟨trace_ortho, vec_recover, completeness, flat_tetrad_metric_owner,
    flat_spin_connection_owner, flat_soldering_covariant_constancy_owner,
    flat_tetrad_compatibility_owner, flat_clifford_soldering_derivative_owner⟩

end Section3
