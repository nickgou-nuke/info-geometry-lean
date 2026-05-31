import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/-!
# InfoGeometry.Categorical.FibonacciBraiding

Theorem-safe categorical wrapper for the finite Fibonacci fusion/matrix data.

This file does not claim a full braid-group representation theorem.  It only
packages the explicit `F`, `R`, and `B = F R F` readouts together with an
optional Artin witness, so that a concrete matrix identity can be carried as
first-class data.

No analytic continuation.
No conformal-block construction.
No universal topological quantum computing claim.
-/

namespace InfoGeometry.Categorical.FibonacciBraiding

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/--
A theorem-safe packet for the finite Fibonacci braid readout.

The packet stores the scalar parameters, the finite `F`-matrix relations, and
an explicit Artin witness for the associated `R/B` matrices.
-/
structure FibonacciBraidingPacket where
  /-- The primitive phase parameter. -/
  q : Units ℂ
  /-- The inverse-golden-ratio parameter. -/
  τ : ℂ
  /-- The square-root parameter for `τ`. -/
  s : ℂ
  /-- The square-root relation. -/
  s_sq : s ^ 2 = τ
  /-- The Fibonacci relation for `τ`. -/
  tau_sq_add_tau : τ ^ 2 + τ = 1
  /-- The explicit Artin braid relation witness. -/
  artin :
    fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
      fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s

namespace FibonacciBraidingPacket

variable {P : FibonacciBraidingPacket}

/-- The finite Fibonacci fusion matrix attached to the packet. -/
noncomputable def F (P : FibonacciBraidingPacket) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fibonacciFusionMatrix P.τ P.s

/-- The finite diagonal braid matrix attached to the packet. -/
noncomputable def R (P : FibonacciBraidingPacket) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fibonacciRMatrix P.q

/-- The finite middle-generator matrix attached to the packet. -/
noncomputable def B (P : FibonacciBraidingPacket) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fibonacciBMatrix P.q P.τ P.s

/-- The packet `F`-matrix is involutive. -/
theorem F_sq (P : FibonacciBraidingPacket) : P.F * P.F = 1 := by
  simpa [F] using (fibonacciFusionMatrix_sq P.s_sq P.tau_sq_add_tau)

/-- The packet `F`-matrix has determinant `-1`. -/
theorem det_F (P : FibonacciBraidingPacket) : P.F.det = -1 := by
  simpa [F] using (det_fibonacciFusionMatrix P.s_sq P.tau_sq_add_tau)

/-- The packet middle generator is `F R F`. -/
theorem B_eq_FRF (P : FibonacciBraidingPacket) : P.B = P.F * P.R * P.F := by
  rfl

/-- The explicit Artin braid relation carried by the packet. -/
theorem artin_relation (P : FibonacciBraidingPacket) :
    P.R * P.B * P.R = P.B * P.R * P.B := by
  simpa [R, B] using P.artin

/-- The packet-level braid relation can be re-exposed as the canonical matrix identity. -/
theorem artin_relation_as_matrix_identity (P : FibonacciBraidingPacket) :
    fibonacciRMatrix P.q * fibonacciBMatrix P.q P.τ P.s * fibonacciRMatrix P.q =
      fibonacciBMatrix P.q P.τ P.s * fibonacciRMatrix P.q * fibonacciBMatrix P.q P.τ P.s :=
  P.artin

end FibonacciBraidingPacket

end InfoGeometry.Categorical.FibonacciBraiding
