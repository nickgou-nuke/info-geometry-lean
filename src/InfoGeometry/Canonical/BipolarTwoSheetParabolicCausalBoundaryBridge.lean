import InfoGeometry.Canonical.BipolarTwoSheetCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarTwoSheetCausalBulkBridge
import InfoGeometry.Canonical.ChiralParabolicNilpotentWeld
import InfoGeometry.Physics.ChiralCausalCone
import Mathlib.Tactic

/-!
# Two-sheet parabolic causal-boundary bridge

The two sheets are represented by the two opposite chiral nilpotent generators
`σPlus` and `σMinus`.  The deck involution exchanges them, and Hermitian
conjugation exchanges them as well.  Each sheet is individually parabolic/null:
its generator squares to zero and has determinant zero.

The doubled pair contains more algebraic information than either sheet alone:
its symmetric and antisymmetric combinations recover the transverse Pauli
coordinates.  Together with the grading generator `σ3c` and the identity, these
operators reconstruct every `2 × 2` complex matrix.

This gives a finite exact boundary-to-bulk algebraic mechanism:

* one sheet -> one nilpotent parabolic direction;
* two sheets -> conjugate nilpotent pair;
* even/odd sheet combinations -> independent transverse directions;
* adding identity and grading -> the full Pauli matrix carrier;
* the critical unit-circle boundary phase -> a null point in the repository's
  four-real-coordinate causal carrier.

No AdS/CFT correspondence, dimension theorem for manifolds, or Einstein dynamics
is asserted.  "Holographic" is only an interpretation of this exact algebraic
boundary-to-bulk reconstruction pattern.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarTwoSheetParabolicCausalBoundaryBridge

open Matrix Complex
open InfoGeometry.Topology.Weyl
open InfoGeometry.Canonical.BipolarTwoSheetCore
open InfoGeometry.Canonical.BipolarTwoSheetCausalBulkBridge
open InfoGeometry.Canonical.ChiralParabolicNilpotentWeld
open InfoGeometry.Physics.ChiralCausalCone
open InfoGeometry.Physics.SolderingSpinConnectionBogoliubov
open InfoGeometry.Algebra.RealPauliCausalCone

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Parabolic nilpotent generator carried by each sheet. -/
def sheetParabolicGenerator : ChiralSheet → M2C
  | ChiralSheet.plus => σPlus
  | ChiralSheet.minus => σMinus

@[simp] theorem sheetParabolicGenerator_plus :
    sheetParabolicGenerator ChiralSheet.plus = σPlus := rfl

@[simp] theorem sheetParabolicGenerator_minus :
    sheetParabolicGenerator ChiralSheet.minus = σMinus := rfl

/-- Deck exchange is represented by Hermitian conjugation of the parabolic
sheet generator. -/
theorem sheetParabolicGenerator_swap (sh : ChiralSheet) :
    sheetParabolicGenerator sh.swap =
      (sheetParabolicGenerator sh)ᴴ := by
  cases sh
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sheetParabolicGenerator, σPlus, σMinus, Matrix.conjTranspose]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sheetParabolicGenerator, σPlus, σMinus, Matrix.conjTranspose]

/-- Every sheet generator is square-zero. -/
theorem sheetParabolicGenerator_sq_zero (sh : ChiralSheet) :
    sheetParabolicGenerator sh * sheetParabolicGenerator sh = 0 := by
  cases sh
  · exact σPlus_sq
  · exact σMinus_sq

/-- Every sheet generator has zero determinant. -/
theorem sheetParabolicGenerator_det_zero (sh : ChiralSheet) :
    Matrix.det (sheetParabolicGenerator sh) = 0 := by
  cases sh
  · exact chiral_transition_determinants_zero.1
  · exact chiral_transition_determinants_zero.2

/-- Opposite sheets satisfy the transverse completeness/CAR relation. -/
theorem sheet_pair_anticommutator_identity (sh : ChiralSheet) :
    sheetParabolicGenerator sh * sheetParabolicGenerator sh.swap +
      sheetParabolicGenerator sh.swap * sheetParabolicGenerator sh = 1 := by
  cases sh
  · exact anti_σPlus_σMinus
  · simpa [add_comm] using anti_σPlus_σMinus

/-- The symmetric two-sheet combination is exactly the first transverse Pauli
coordinate. -/
theorem sheet_symmetric_eq_sigma1 :
    sheetParabolicGenerator ChiralSheet.plus +
      sheetParabolicGenerator ChiralSheet.minus = σ1 := by
  simpa [sheetParabolicGenerator] using σ1_from_chiral.symm

/-- The antisymmetric two-sheet combination reconstructs the second transverse
Pauli coordinate after multiplication by `-i`. -/
theorem sheet_antisymmetric_eq_sigma2 :
    (-Complex.I) •
      (sheetParabolicGenerator ChiralSheet.plus -
        sheetParabolicGenerator ChiralSheet.minus) = σ2 := by
  simpa [sheetParabolicGenerator] using σ2_from_chiral.symm

/-- Coefficients of the canonical chiral decomposition of a `2 × 2` complex
matrix. -/
def matrixScalarCoeff (M : M2C) : ℂ := (M 0 0 + M 1 1) / 2

def matrixGradingCoeff (M : M2C) : ℂ := (M 0 0 - M 1 1) / 2

def matrixPlusCoeff (M : M2C) : ℂ := M 0 1

def matrixMinusCoeff (M : M2C) : ℂ := M 1 0

/-- Every `2 × 2` complex matrix is reconstructed from identity, grading, and
the two parabolic sheet generators. -/
theorem matrix_eq_two_sheet_chiral_decomposition (M : M2C) :
    M =
      matrixScalarCoeff M • (1 : M2C) +
      matrixGradingCoeff M • σ3c +
      matrixPlusCoeff M • sheetParabolicGenerator ChiralSheet.plus +
      matrixMinusCoeff M • sheetParabolicGenerator ChiralSheet.minus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixScalarCoeff, matrixGradingCoeff, matrixPlusCoeff,
      matrixMinusCoeff, sheetParabolicGenerator, σPlus, σMinus, σ3c]
  all_goals ring

/-- The doubled parabolic boundary pair therefore generates the complete
`2 × 2` complex matrix carrier once the scalar and grading directions are
included. -/
theorem two_sheet_generates_full_pauli_carrier (M : M2C) :
    ∃ a h p m : ℂ,
      M = a • (1 : M2C) + h • σ3c +
        p • sheetParabolicGenerator ChiralSheet.plus +
        m • sheetParabolicGenerator ChiralSheet.minus := by
  exact ⟨matrixScalarCoeff M, matrixGradingCoeff M,
    matrixPlusCoeff M, matrixMinusCoeff M,
    matrix_eq_two_sheet_chiral_decomposition M⟩

/-- The two critical sheets project to a conjugate pair of null representatives
in the existing four-real-coordinate causal carrier. -/
theorem critical_two_sheet_parabolic_causal_packet (y : ℝ) :
    sheetMirror (plusLift (InfoGeometry.Analysis.BipolarCrossRatioLog.criticalLine y)) =
      minusLift (InfoGeometry.Analysis.BipolarCrossRatioLog.criticalLine y) ∧
    sheetParabolicGenerator ChiralSheet.plus *
      sheetParabolicGenerator ChiralSheet.plus = 0 ∧
    sheetParabolicGenerator ChiralSheet.minus *
      sheetParabolicGenerator ChiralSheet.minus = 0 ∧
    detMinkowski (criticalNullBulk y) = 0 := by
  exact ⟨sheetMirror_plus_criticalLine y,
    sheetParabolicGenerator_sq_zero ChiralSheet.plus,
    sheetParabolicGenerator_sq_zero ChiralSheet.minus,
    criticalNullBulk_lightlike y⟩

/-- Compact reconstruction packet: deck exchange swaps the two parabolic
nilpotents, the pair completes the transverse algebra, and the critical phase
lands on the causal null cone. -/
theorem two_sheet_parabolic_boundary_reconstruction (y : ℝ) :
    sheetParabolicGenerator ChiralSheet.plus.swap =
      (sheetParabolicGenerator ChiralSheet.plus)ᴴ ∧
    sheetParabolicGenerator ChiralSheet.plus *
        sheetParabolicGenerator ChiralSheet.minus +
      sheetParabolicGenerator ChiralSheet.minus *
        sheetParabolicGenerator ChiralSheet.plus = 1 ∧
    sheetParabolicGenerator ChiralSheet.plus +
      sheetParabolicGenerator ChiralSheet.minus = σ1 ∧
    detMinkowski (criticalNullBulk y) = 0 := by
  exact ⟨sheetParabolicGenerator_swap ChiralSheet.plus,
    sheet_pair_anticommutator_identity ChiralSheet.plus,
    sheet_symmetric_eq_sigma1,
    criticalNullBulk_lightlike y⟩

end InfoGeometry.Canonical.BipolarTwoSheetParabolicCausalBoundaryBridge
