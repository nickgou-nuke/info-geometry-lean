import InfoGeometry.SignedNetwork.PauliContextBridge
import InfoGeometry.SignedNetwork.BalancedPairKernel

/-! A finite qubit frame built on the repository Pauli paravector owner.
The coefficients are real coordinates; no positivity or stochastic meaning is
asserted for them. -/
namespace InfoGeometry.SignedNetwork.QubitWignerBridge
noncomputable section
open InfoGeometry.SignedNetwork.PauliContextBridge
open InfoGeometry.SignedNetwork.BalancedPairKernel
open scoped Matrix

def phaseDirection : Fin 4 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

def phasePoint (a : Fin 4) : Mat2 :=
  contextProjector (phaseDirection a 0) (phaseDirection a 1) (phaseDirection a 2)

def synthesis (w : Fin 4 → ℝ) : Mat2 :=
  ∑ a, (w a : ℂ) • phasePoint a

def analysis (M : Mat2) (a : Fin 4) : ℝ :=
  (Matrix.trace (phasePoint a * M)).re / 2

theorem analysis_synthesis (w : Fin 4 → ℝ) : analysis (synthesis w) = w := by
  funext a
  fin_cases a <;>
    simp [analysis, synthesis, phasePoint, phaseDirection, contextProjector,
      InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix,
      Matrix.trace, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sum_apply, Fin.sum_univ_four, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> ring

def dot3 (u v : Fin 3 → ℝ) : ℝ := u 0*v 0 + u 1*v 1 + u 2*v 2

def cross3 (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1*v 2-u 2*v 1, u 2*v 0-u 0*v 2, u 0*v 1-u 1*v 0]

def hamiltonian (h : Fin 3 → ℝ) : Mat2 :=
  InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix
    ⟨0, h 0, h 1, h 2⟩

def wignerGenerator (hbar : ℝ) (h : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => (1/2) * (1/hbar) * dot3 (phaseDirection a) (cross3 h (phaseDirection b))

theorem wignerGenerator_column_sum (hbar : ℝ) (h : Fin 3 → ℝ) (b : Fin 4) :
    ∑ a, wignerGenerator hbar h a b = 0 := by
  fin_cases b <;> simp [wignerGenerator, dot3, cross3, phaseDirection,
    Fin.sum_univ_four] <;> ring

theorem wignerGenerator_skew (hbar : ℝ) (h : Fin 3 → ℝ) (a b : Fin 4) :
    wignerGenerator hbar h a b = -wignerGenerator hbar h b a := by
  fin_cases a <;> fin_cases b <;>
    simp [wignerGenerator, dot3, cross3, phaseDirection] <;> ring

theorem pairRate_recovers_wigner_column (hbar : ℝ) (h : Fin 3 → ℝ)
    (b a : Fin 4) :
    (∑ c, pairRate (fun d => wignerGenerator hbar h d b) a c) -
        (∑ c, pairRate (fun d => wignerGenerator hbar h d b) c a) =
      wignerGenerator hbar h a b := by
  exact pairRate_recovers_column_all _ (wignerGenerator_column_sum hbar h b) a

theorem phasePoint_trace (a : Fin 4) : Matrix.trace (phasePoint a) = 1 := by
  exact contextProjector_trace _ _ _

theorem trace_synthesis (w : Fin 4 → ℝ) :
    Matrix.trace (synthesis w) = ((∑ a, w a : ℝ) : ℂ) := by
  simp [synthesis, Matrix.trace_sum, Matrix.trace_smul, phasePoint_trace]

def liouville (hbar : ℝ) (h : Fin 3 → ℝ) (M : Mat2) : Mat2 :=
  (-Complex.I / hbar) •
    (hamiltonian h * M - M * hamiltonian h)

set_option maxHeartbeats 800000 in
theorem synthesis_generator (hbar : ℝ) (h : Fin 3 → ℝ) (w : Fin 4 → ℝ)
    (hhbar : hbar ≠ 0) :
    synthesis (fun a => ∑ b, wignerGenerator hbar h a b * w b) =
      liouville hbar h (synthesis w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [synthesis, wignerGenerator, dot3, cross3, phasePoint, phaseDirection,
      contextProjector, hamiltonian, liouville,
      InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix,
      Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      Fin.sum_univ_four, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, hhbar] <;> ring

end
end InfoGeometry.SignedNetwork.QubitWignerBridge
