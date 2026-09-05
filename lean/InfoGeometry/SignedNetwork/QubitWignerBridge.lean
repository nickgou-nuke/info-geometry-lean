import InfoGeometry.SignedNetwork.PauliContextBridge
import InfoGeometry.SignedNetwork.BalancedPairKernel

/-!
# An explicit qubit quasiprobability frame and its Hamiltonian generator

This is a concrete representation-level quantum realization, not a claimed
Wigner calculus on every graph. The four trace-one Hermitian phase-point
operators are not positive operators. Their signed coordinates reconstruct a
Hermitian qubit operator. The finite generator is derived from the actual
Hamiltonian commutator, not from an arbitrary imaginary matrix entry.

The use of matrices here is the existing spin-one-half representation. No
associative instance or matrix-algebra identification is imposed on the
nonassociative operator-Zorn field carrier.
-/

noncomputable section

namespace InfoGeometry.SignedNetwork.QubitWignerBridge

open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.SignedNetwork.CoherenceAndProjection
open InfoGeometry.SignedNetwork.PauliContextBridge
open InfoGeometry.SignedNetwork.BalancedPairKernel
open scoped Matrix

/-- A fixed four-point choice of qubit phase-space frame. -/
def phaseDirection : Fin 4 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

def dot3 (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def cross3 (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- Hermitian trace-one phase-point operators; these are not POVM effects. -/
def phasePoint (a : Fin 4) : Mat2 :=
  contextProjector (phaseDirection a 0) (phaseDirection a 1) (phaseDirection a 2)

def synthesis (w : Fin 4 → ℝ) : Mat2 := ∑ a, (w a : ℂ) • phasePoint a

def analysis (M : Mat2) (a : Fin 4) : ℝ := (Matrix.trace (phasePoint a * M)).re / 2

/-- Exact duality of the selected four phase-point coordinates. -/
theorem analysis_synthesis (w : Fin 4 → ℝ) : analysis (synthesis w) = w := by
  funext a
  fin_cases a <;>
    simp [analysis, synthesis, phasePoint, phaseDirection, contextProjector,
      PauliParavector.pauliMatrix, Matrix.trace, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Fin.sum_univ_four, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- Total signed weight is the operator trace, not an assumed probability law. -/
theorem trace_synthesis (w : Fin 4 → ℝ) :
    Matrix.trace (synthesis w) = ((∑ a, w a : ℝ) : ℂ) := by
  simp [synthesis, phasePoint, Matrix.trace_sum, Matrix.trace_smul,
    contextProjector_trace, smul_eq_mul] <;> push_cast <;> ring

/-- A normalized pure-state example has a negative quasiprobability coordinate. -/
theorem negative_quasiprobability_example :
    analysis (contextProjector (-3/5) (-4/5) 0) 0 = (-1/10 : ℝ) := by
  norm_num [analysis, phasePoint, phaseDirection, contextProjector,
    PauliParavector.pauliMatrix, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

theorem negative_example_idempotent :
    contextProjector (-3/5) (-4/5) 0 * contextProjector (-3/5) (-4/5) 0 =
      contextProjector (-3/5) (-4/5) 0 := by
  apply contextProjector_idempotent
  norm_num

/-- The scalar Hamiltonian term is omitted because it commutes with every state. -/
def hamiltonian (h : Fin 3 → ℝ) : Mat2 :=
  PauliParavector.pauliMatrix ⟨0, h 0, h 1, h 2⟩

/-- Hamiltonian Liouville generator. Physical time evolution uses `hbar > 0`. -/
def liouville (hbar : ℝ) (H M : Mat2) : Mat2 :=
  (((1 / hbar : ℝ) : ℂ) * (-Complex.I)) • (H * M - M * H)

/-- Real generator obtained by conjugating the Hamiltonian commutator into
the fixed quasiprobability frame. Rows are child cells, columns are parent cells. -/
def wignerGenerator (hbar : ℝ) (h : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => (1 / 2 : ℝ) * (1 / hbar) *
    dot3 (phaseDirection a) (cross3 h (phaseDirection b))

/-- Exact commutator-to-quasiprobability intertwining. -/
theorem synthesis_generator (hbar : ℝ) (h : Fin 3 → ℝ) (w : Fin 4 → ℝ) :
    synthesis (fun a => ∑ b, wignerGenerator hbar h a b * w b) =
      liouville hbar (hamiltonian h) (synthesis w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [synthesis, wignerGenerator, dot3, cross3, phasePoint, phaseDirection,
      contextProjector, hamiltonian, liouville, PauliParavector.pauliMatrix,
      Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      Fin.sum_univ_four, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- Every Hamiltonian column is mass-zero, derived from the explicit frame. -/
theorem wignerGenerator_column_sum (hbar : ℝ) (h : Fin 3 → ℝ) (b : Fin 4) :
    (∑ a, wignerGenerator hbar h a b) = 0 := by
  fin_cases b <;>
    simp [wignerGenerator, phaseDirection, dot3, cross3, Fin.sum_univ_four] <;> ring

/-- The finite generator is skew-symmetric in this orthogonal phase-point frame. -/
theorem wignerGenerator_skew (hbar : ℝ) (h : Fin 3 → ℝ) (a b : Fin 4) :
    wignerGenerator hbar h a b = -wignerGenerator hbar h b a := by
  fin_cases a <;> fin_cases b <;>
    simp [wignerGenerator, phaseDirection, dot3, cross3] <;> ring

/-- A balanced pair intensity reproduces every column of this actual
Hamiltonian generator, including zero-rate columns. No stochastic convergence is asserted. -/
theorem hamiltonian_pair_first_moment (hbar : ℝ) (h : Fin 3 → ℝ) (b a : Fin 4) :
    (∑ c, pairRate (fun d => wignerGenerator hbar h d b) a c) -
        (∑ c, pairRate (fun d => wignerGenerator hbar h d b) c a) =
      wignerGenerator hbar h a b := by
  exact pairRate_recovers_column_all _ (wignerGenerator_column_sum hbar h b) a

end InfoGeometry.SignedNetwork.QubitWignerBridge
