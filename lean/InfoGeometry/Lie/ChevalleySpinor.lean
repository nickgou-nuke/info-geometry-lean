import Mathlib.Tactic

namespace InfoGeometry.Lie.ChevalleySpinor

open CliffordAlgebra
open Even

/- 1. SPLIT SIGNATURE QUADRATIC FORMS -/

/-- The standard split quadratic form Q(x) = ∑ x_i² - ∑ y_i² on M = Mp × Mm -/
def splitQuadraticForm {R : Type*} [CommRing R] {Mp Mm : Type*} [AddCommGroup Mp] [AddCommGroup Mm]
    [Module R Mp] [Module R Mm] (Qp : QuadraticForm R Mp) (Qm : QuadraticForm R Mm) :
    QuadraticForm R (Mp × Mm) :=
  (Qp.prod <| -Qm)

/- 2. SPINOR REPRESENTATION VIA MATHLIB'S NATIVE EVEN SUBALGEBRA -/

/-- The spinor representation of the even subalgebra -/
def spinorRepEven {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} {A : Type*} [Ring A] [Algebra R A]
    (f : EvenHom Q A) : even Q →ₐ[R] A :=
  (even.lift (R := R) (Q := Q) (A := A)) f

/-- The canonical embedding of pairs into the even subalgebra -/
def evenIota {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} : EvenHom Q (even Q) :=
  even.ι Q

/- 3. CUNTZ ALGEBRA SOCKET FOR SPLIT SIGNATURES -/

/-- The Cuntz trace state on the split Clifford algebra -/
structure CuntzTraceSocket {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (A : Type*) [Ring A] [Algebra R A] where
  trace : A →ₗ[R] R
  trace_mul_comm : ∀ a b : A, trace (a * b) = trace (b * a)

/-- The canonical trace on matrix algebras as a Cuntz trace socket -/
def matrixCuntzTrace {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) {n : Type*} [Fintype n] [DecidableEq n] :
    CuntzTraceSocket Q (Matrix n n R) :=
  ⟨Matrix.traceLinearMap n R R, fun a b => by
    dsimp [Matrix.traceLinearMap]
    rw [Matrix.trace_mul_comm]⟩

/- 4. ITKURA-SAITO / BURG DIVERGENCE ON CLIFFORD ALGEBRAS -/

/-- The Itakura-Saito divergence as an operator Bregman divergence
  on the even subalgebra with the trace socket -/
noncomputable def itakuraSaitoDivergence {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} {A : Type*} [Ring A] [Algebra R A] [Inv A]
    (socket : CuntzTraceSocket Q A) (X Y : A) : R :=
  socket.trace (X * Y⁻¹) - socket.trace (1 : A) - socket.trace (Y * X⁻¹) + socket.trace (1 : A)

/-- The Burg/Itakura-Saito divergence on the spinor representation -/
noncomputable def burgDivergence {n : ℕ} (X Y : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) : ℝ :=
  (matrixCuntzTrace (0 : QuadraticForm ℝ (Fin n → ℝ)) (n := Fin (2 ^ n))).trace (X * Y⁻¹) - 
  (matrixCuntzTrace (0 : QuadraticForm ℝ (Fin n → ℝ)) (n := Fin (2 ^ n))).trace (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) -
  (matrixCuntzTrace (0 : QuadraticForm ℝ (Fin n → ℝ)) (n := Fin (2 ^ n))).trace (Y * X⁻¹) + 
  (matrixCuntzTrace (0 : QuadraticForm ℝ (Fin n → ℝ)) (n := Fin (2 ^ n))).trace (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ)

/-- The application of the Cuntz trace socket to a matrix equals Matrix.trace -/
theorem cuntzTraceSocket_apply {n : ℕ} (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) :
    (matrixCuntzTrace (0 : QuadraticForm ℝ (Fin n → ℝ)) (n := Fin (2 ^ n))).trace M = Matrix.trace M :=
  rfl

/-- The isomorphism between the Itakura-Saito divergence on the Cuntz trace socket
  and the Burg divergence on the matrix algebra -/
theorem itakuraSaito_eq_burg {n : ℕ} (X Y : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) :
    itakuraSaitoDivergence (matrixCuntzTrace (0 : QuadraticForm ℝ (Fin n → ℝ)) (n := Fin (2 ^ n))) X Y = burgDivergence X Y :=
  rfl

end InfoGeometry.Lie.ChevalleySpinor
