/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumGravity.ConnesSpectralHiggsBoussoBound

/-!
# Concrete Integer Examples for Section 121: Finite Scalar/Matrix Identities
Target: `InfoGeometry/QuantumGravity/ConnesSpectralHiggsBoussoBoundAudit.lean`

Verifies over `ℤ` (`decide`) the finite matrix-square identity and sample values
of the scalar quartic polynomial and the defined Raychaudhuri-style polynomial.
These checks do not assert a spectral action or geometric entropy bound.
-/

namespace InfoGeometry.QuantumGravity.ConnesBoussoAudit

open InfoGeometry.QuantumGravity.ConnesBousso

/-- Finite matrix-square example for `D₀ = 3`, `ϕ = 4`. -/
theorem sample_finite_sheet_matrix_square_int :
    let D := SheetMatrixCoord2.connesDiracMatrixModel (3 : ℤ) 4
    SheetMatrixCoord2.mul D D = ⟨25, 0, 0, 25⟩ ∧
    SheetMatrixCoord2.trace (SheetMatrixCoord2.mul D D) = 50 := by
  decide

/-- Sample values of the scalar quartic polynomial over `ℤ`. -/
theorem sample_scalar_quartic_potential_int :
    spectralHiggsPotential (2 : ℤ) 5 5 = 0 ∧
    spectralHiggsPotential (2 : ℤ) 5 (-5) = 0 ∧
    spectralHiggsPotential (2 : ℤ) 5 3 = 512 := by
  decide

/-- Sample value and sign of the defined Raychaudhuri-style scalar polynomial. -/
theorem sample_scalar_raychaudhuri_rhs_int :
    raychaudhuriFocusingRate2 (3 : ℤ) 2 4 5 = -57 ∧
    (-57 : ℤ) ≤ 0 := by
  decide

#print axioms SheetMatrixCoord2.finite_sheet_matrix_square
#print axioms SheetMatrixCoord2.finite_sheet_matrix_trace_square
#print axioms SheetMatrixCoord2.sheetMatrixCoord2_mul_noncommutative
#print axioms spectralHiggsPotential_nonneg
#print axioms raychaudhuri_scalar_rhs_nonpos
#print axioms two_segment_scalar_bound_transitive
#print axioms sample_finite_sheet_matrix_square_int
#print axioms sample_scalar_quartic_potential_int
#print axioms sample_scalar_raychaudhuri_rhs_int

end InfoGeometry.QuantumGravity.ConnesBoussoAudit
