import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.OperatorAlgebra.CuntzTomitaQuadraticReadout
import InfoGeometry.Quantum.PauliSoldering

/-!
# Finite Pauli soldering to a trace-normalized Tomita density

This is the finite, theorem-safe quantization wire

`PauliParavector -> 2 x 2 Pauli matrix -> X Xᴴ -> trace normalization`.

The Pauli matrix is only a two-dimensional representation block.  No claim is
made here that it is the full `Cl(5,5)` carrier, and no unbounded `xp`
operator is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.PauliTomitaDensityBridge

open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Quantum.PauliSoldering
open scoped ComplexOrder

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The soldered matrix attached to a real Pauli paravector. -/
def solderedMatrix (P : PauliParavector) : M2C :=
  solder (P.energy, P.px, P.py, P.pz)

theorem solderedMatrix_eq_pauliMatrix (P : PauliParavector) :
    solderedMatrix P = P.pauliMatrix := by
  rw [solderedMatrix, solder_explicit]
  simp [PauliParavector.pauliMatrix]

/-- The finite Tomita quadratic readout of the soldered Pauli block. -/
def solderedQuadratic (δ : ℝ) (P : PauliParavector) : M2C :=
  tomitaQuadratic δ (solderedMatrix P)

theorem solderedQuadratic_eq_pauliQuadratic
    (δ : ℝ) (P : PauliParavector) :
    solderedQuadratic δ P = tomitaQuadratic δ P.pauliMatrix := by
  rw [solderedQuadratic, solderedMatrix_eq_pauliMatrix]

theorem solderedQuadratic_delta_invariant
    (δ₁ δ₂ : ℝ) (P : PauliParavector) :
    solderedQuadratic δ₁ P = solderedQuadratic δ₂ P := by
  rw [solderedQuadratic_eq_pauliQuadratic,
    solderedQuadratic_eq_pauliQuadratic,
    tomitaQuadratic_delta_invariant]

theorem solderedQuadratic_isHermitian
    (δ : ℝ) (P : PauliParavector) :
    (solderedQuadratic δ P).IsHermitian := by
  rw [solderedQuadratic_eq_pauliQuadratic]
  exact tomitaQuadratic_isHermitian δ P.pauliMatrix

theorem solderedQuadratic_posSemidef
    (δ : ℝ) (P : PauliParavector) :
    (solderedQuadratic δ P).PosSemidef := by
  rw [solderedQuadratic_eq_pauliQuadratic]
  exact tomitaQuadratic_posSemidef δ P.pauliMatrix

/-- Trace-normalized density readout, defined for a nonzero Pauli block. -/
noncomputable def pauliDensity
    (δ : ℝ) (P : PauliParavector) (hP : P.pauliMatrix ≠ 0) : M2C :=
  normalizedTomitaQuadratic δ P.pauliMatrix
    (tomitaQuadratic_trace_ne_zero_of_ne_zero δ hP)

theorem pauliDensity_trace
    (δ : ℝ) (P : PauliParavector) (hP : P.pauliMatrix ≠ 0) :
    Matrix.trace (pauliDensity δ P hP) = 1 := by
  unfold pauliDensity
  exact normalizedTomitaQuadratic_trace δ P.pauliMatrix _

theorem pauliDensity_isHermitian
    (δ : ℝ) (P : PauliParavector) (hP : P.pauliMatrix ≠ 0) :
    (pauliDensity δ P hP).IsHermitian := by
  unfold pauliDensity
  exact normalizedTomitaQuadratic_isHermitian_of_trace_ne_zero
    δ P.pauliMatrix _

theorem pauliDensity_posSemidef
    (δ : ℝ) (P : PauliParavector) (hP : P.pauliMatrix ≠ 0) :
    (pauliDensity δ P hP).PosSemidef := by
  unfold pauliDensity
  exact normalizedTomitaQuadratic_posSemidef_of_trace_ne_zero
    δ P.pauliMatrix _

theorem pauliDensity_right_unitary_invariant
    (δ : ℝ) (P : PauliParavector) (U : M2C)
    (hU : U * U.conjTranspose = 1)
    (hP : P.pauliMatrix ≠ 0) :
    normalizedTomitaQuadratic δ (P.pauliMatrix * U)
        (tomitaQuadratic_trace_right_unitary_ne_zero δ P.pauliMatrix U hU
          (tomitaQuadratic_trace_ne_zero_of_ne_zero δ hP)) =
      normalizedTomitaQuadratic δ P.pauliMatrix
        (tomitaQuadratic_trace_ne_zero_of_ne_zero δ hP) := by
  exact normalizedTomitaQuadratic_right_unitary_invariant_of_trace_ne_zero
    δ P.pauliMatrix U hU
      (tomitaQuadratic_trace_ne_zero_of_ne_zero δ hP)

end InfoGeometry.Canonical.PauliTomitaDensityBridge
