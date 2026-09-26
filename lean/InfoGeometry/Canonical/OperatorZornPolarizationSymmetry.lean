import InfoGeometry.Canonical.OperatorZornCasimirNullIdentity

/-!
# Coordinate symmetries of the existing noncommutative Zorn product

The maps act on `NCZornElement A`, retaining its three operator-valued
colour slots and its nonassociative product. Coordinate sign reversal and
exchange commute. Their composite is multiplicative even for noncommuting
coefficients. Neither component is silently declared an algebra grading,
a modular conjugation, or a spacetime deck transformation.
-/

namespace InfoGeometry.Canonical.OperatorZornPolarizationSymmetry

open InfoGeometry.Canonical InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

/-- Sign reversal of the two vector slots. -/
def offDiagonalSign (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨X.n_plus, X.n_minus, -X.sigma_plus, -X.sigma_minus⟩

/-- Exchange of the scalar and vector slots. This is not anti-linear. -/
def exchange (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨X.n_minus, X.n_plus, X.sigma_minus, X.sigma_plus⟩

/-- The signed exchange, without any assertion of geometric holonomy. -/
def signedExchange (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨X.n_minus, X.n_plus, -X.sigma_minus, -X.sigma_plus⟩

@[simp] theorem offDiagonalSign_sq (X : OperatorZornMatrix A) :
    offDiagonalSign (offDiagonalSign X) = X := by
  cases X
  simp [offDiagonalSign]

@[simp] theorem exchange_sq (X : OperatorZornMatrix A) : exchange (exchange X) = X := by
  cases X
  rfl

@[simp] theorem signedExchange_sq (X : OperatorZornMatrix A) :
    signedExchange (signedExchange X) = X := by
  cases X
  simp [signedExchange]

theorem coordinate_actions_commute (X : OperatorZornMatrix A) :
    offDiagonalSign (exchange X) = exchange (offDiagonalSign X) := rfl

theorem signedExchange_eq_composite (X : OperatorZornMatrix A) :
    signedExchange X = exchange (offDiagonalSign X) := rfl

/-- Multiplicativity is established with every coefficient product in its
original order; no commutativity or alternativity of the payload is assumed. -/
theorem signedExchange_mul (X Y : OperatorZornMatrix A) :
    signedExchange (operatorZornMul X Y) =
      operatorZornMul (signedExchange X) (signedExchange Y) := by
  apply operatorZornMatrix_ext
  · simp [signedExchange, operatorZornMul, NCZornElement.mul, NCZornElement.zornDot]
  · simp [signedExchange, operatorZornMul, NCZornElement.mul, NCZornElement.zornDot]
  · funext i
    fin_cases i <;>
      simp [signedExchange, operatorZornMul, NCZornElement.mul,
        NCZornElement.zornCross] <;> noncomm_ring
  · funext i
    fin_cases i <;>
      simp [signedExchange, operatorZornMul, NCZornElement.mul,
        NCZornElement.zornCross] <;> noncomm_ring

/-- Native `MulEquiv` does not require the underlying multiplication to be associative. -/
def signedExchangeMulEquiv : OperatorZornMatrix A ≃* OperatorZornMatrix A where
  toFun := signedExchange
  invFun := signedExchange
  left_inv := signedExchange_sq
  right_inv := signedExchange_sq
  map_mul' := signedExchange_mul

/-- The upper pure-vector square is zero exactly when its three coefficient
commutators vanish. -/
theorem sigmaPlus_square_zero_iff (U : OperatorVector A) :
    operatorZornMul (sigmaPlus U) (sigmaPlus U) = 0 ↔ operatorCross U U = 0 := by
  rw [sigmaPlus_mul_sigmaPlus]
  constructor
  · intro h
    exact congrArg NCZornElement.sigma_minus h
  · intro h
    rw [h]
    rfl

theorem sigmaMinus_square_zero_iff (U : OperatorVector A) :
    operatorZornMul (sigmaMinus U) (sigmaMinus U) = 0 ↔ operatorCross U U = 0 := by
  rw [sigmaMinus_mul_sigmaMinus]
  constructor
  · intro h
    have hz : -operatorCross U U = 0 := congrArg NCZornElement.sigma_plus h
    exact neg_eq_zero.mp hz
  · intro h
    rw [h, neg_zero]
    rfl

theorem sigmaPlus_square_zero_iff_commuting (U : OperatorVector A) :
    operatorZornMul (sigmaPlus U) (sigmaPlus U) = 0 ↔
      U 1 * U 2 = U 2 * U 1 ∧ U 2 * U 0 = U 0 * U 2 ∧ U 0 * U 1 = U 1 * U 0 := by
  rw [sigmaPlus_square_zero_iff, operatorCross_self_eq_zero_iff]

theorem sigmaMinus_square_zero_iff_commuting (U : OperatorVector A) :
    operatorZornMul (sigmaMinus U) (sigmaMinus U) = 0 ↔
      U 1 * U 2 = U 2 * U 1 ∧ U 2 * U 0 = U 0 * U 2 ∧ U 0 * U 1 = U 1 * U 0 := by
  rw [sigmaMinus_square_zero_iff, operatorCross_self_eq_zero_iff]

/-- Coordinate Peirce decomposition, without changing the native multiplication. -/
theorem coordinate_peirce_decomposition (X : OperatorZornMatrix A) :
    nPlus X.n_plus + nMinus X.n_minus + sigmaPlus X.sigma_plus +
      sigmaMinus X.sigma_minus = X := by
  apply operatorZornMatrix_ext
  · change X.n_plus + 0 + 0 + 0 = X.n_plus
    simp
  · change 0 + X.n_minus + 0 + 0 = X.n_minus
    simp
  · ext i
    change 0 + 0 + X.sigma_plus i + 0 = X.sigma_plus i
    simp
  · ext i
    change 0 + 0 + 0 + X.sigma_minus i = X.sigma_minus i
    simp

/-- The source's ordered quadratic readout vanishes on every upper vector,
including upper vectors whose operator-valued square is nonzero. -/
@[simp] theorem orderedReadout_sigmaPlus (U : OperatorVector A) :
    operatorZornCasimir (sigmaPlus U) = 0 := by
  simp [operatorZornCasimir, sigmaPlus, operatorDot, NCZornElement.zornDot]

/-- The coordinate sign preserves this ordered quadratic readout exactly. -/
theorem offDiagonalSign_orderedReadout (X : OperatorZornMatrix A) :
    operatorZornCasimir (offDiagonalSign X) = operatorZornCasimir X := by
  simp [operatorZornCasimir, offDiagonalSign, operatorDot, NCZornElement.zornDot]

/-- The signed exchange need not preserve the operator-valued quadratic
readout itself. The entire discrepancy is an explicit sum of commutators. -/
theorem signedExchange_orderedReadout_defect (X : OperatorZornMatrix A) :
    operatorZornCasimir (signedExchange X) - operatorZornCasimir X =
      (X.n_minus * X.n_plus - X.n_plus * X.n_minus) +
      (X.sigma_plus 0 * X.sigma_minus 0 - X.sigma_minus 0 * X.sigma_plus 0) +
      (X.sigma_plus 1 * X.sigma_minus 1 - X.sigma_minus 1 * X.sigma_plus 1) +
      (X.sigma_plus 2 * X.sigma_minus 2 - X.sigma_minus 2 * X.sigma_plus 2) := by
  simp only [operatorZornCasimir, signedExchange, operatorDot, NCZornElement.zornDot,
    Pi.neg_apply, neg_mul_neg]
  noncomm_ring

/-- A finite matrix trace removes that discrepancy, without making the
operator-valued readout commute. -/
theorem trace_signedExchange_orderedReadout
    {n : Type*} [Fintype n] [DecidableEq n]
    (X : OperatorZornMatrix (Matrix n n ℂ)) :
    Matrix.trace (operatorZornCasimir (signedExchange X)) =
      Matrix.trace (operatorZornCasimir X) := by
  simp only [operatorZornCasimir, signedExchange, operatorDot, NCZornElement.zornDot,
    Pi.neg_apply, neg_mul_neg, Matrix.trace_sub, Matrix.trace_add]
  rw [Matrix.trace_mul_comm X.n_minus X.n_plus,
    Matrix.trace_mul_comm (X.sigma_minus 0) (X.sigma_plus 0),
    Matrix.trace_mul_comm (X.sigma_minus 1) (X.sigma_plus 1),
    Matrix.trace_mul_comm (X.sigma_minus 2) (X.sigma_plus 2)]

/-- A concrete refutation of the attachment's coordinate anticommutation law. -/
theorem coordinate_actions_do_not_anticommute :
    ¬ ∀ U V : OperatorVector ℝ,
      offDiagonalSign (exchange (chiralOperatorZorn U V)) =
        -(exchange (offDiagonalSign (chiralOperatorZorn U V))) := by
  intro h
  have h0 := congrArg (fun X : OperatorZornMatrix ℝ => X.sigma_minus 0)
    (h ![1, 0, 0] 0)
  norm_num [offDiagonalSign, exchange, chiralOperatorZorn, operatorZornCoordinates] at h0
  change (-1 : ℝ) = -(-1 : ℝ) at h0
  linarith

end InfoGeometry.Canonical.OperatorZornPolarizationSymmetry
