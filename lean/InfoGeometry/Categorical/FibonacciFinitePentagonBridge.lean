import InfoGeometry.External.Auto.FibAnyonThm6_pentagon
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.FibonacciFiveChannelAssociator

/-!
# Golden finite Fibonacci pentagon bridge

The external finite golden-ratio calculation is reused to instantiate the
native complex fusion matrix and the existing five-channel carrier.  This is
an explicit finite `F² = 1` readout; it is not promoted to a global
pentagon/monoidal coherence claim.
-/

namespace InfoGeometry.Categorical.FibonacciFinitePentagonBridge

open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciFiveChannelAssociator

noncomputable def goldenF12Complex : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => (F12_mat i j : ℂ)

theorem golden_tau_relation :
    tau_gr ^ 2 + tau_gr = 1 := by
  nlinarith [pentagon_condition, s_sq_eq_tau]

theorem golden_complex_s_relation :
    (s_gr : ℂ) ^ 2 = (tau_gr : ℂ) := by
  exact_mod_cast s_sq_eq_tau

theorem golden_complex_tau_relation :
    (tau_gr : ℂ) ^ 2 + (tau_gr : ℂ) = 1 := by
  exact_mod_cast golden_tau_relation

theorem golden_fusion_matrix_sq :
    fibonacciFusionMatrix (tau_gr : ℂ) (s_gr : ℂ) *
        fibonacciFusionMatrix (tau_gr : ℂ) (s_gr : ℂ) = 1 := by
  exact fibonacciFusionMatrix_sq golden_complex_s_relation
    golden_complex_tau_relation

theorem golden_five_channel_associator_sq :
    fiveChannelAssociatorMatrix (tau_gr : ℂ) (s_gr : ℂ) *
        fiveChannelAssociatorMatrix (tau_gr : ℂ) (s_gr : ℂ) = 1 := by
  exact fiveChannelAssociatorMatrix_sq (tau_gr : ℂ) (s_gr : ℂ)
    golden_complex_s_relation golden_complex_tau_relation

theorem golden_F12_complex_pentagon :
    goldenF12Complex * goldenF12Complex * goldenF12Complex =
      goldenF12Complex := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j)
    fib_anyons_pentagon_full
  simpa [goldenF12Complex, Matrix.mul_apply, Fin.sum_univ_three] using
    congrArg Complex.ofReal h

/- The same finite pentagon readout on the associated operator carrier. -/
theorem golden_F12_complex_pentagon_linear :
    (Matrix.toLin' goldenF12Complex).comp
        ((Matrix.toLin' goldenF12Complex).comp
          (Matrix.toLin' goldenF12Complex)) =
      Matrix.toLin' goldenF12Complex := by
  rw [show (Matrix.toLin' goldenF12Complex).comp
      ((Matrix.toLin' goldenF12Complex).comp
        (Matrix.toLin' goldenF12Complex)) =
      Matrix.toLin'
        (goldenF12Complex * goldenF12Complex * goldenF12Complex) by
    simp [Matrix.toLin'_mul, mul_assoc]]
  rw [golden_F12_complex_pentagon]

theorem golden_fusion_matrix_ne_one :
    fibonacciFusionMatrix (tau_gr : ℂ) (s_gr : ℂ) ≠ 1 := by
  intro h
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have : (tau_gr : ℂ) = 1 := by
    simpa [fibonacciFusionMatrix] using h00
  have hreal : tau_gr = 1 := by exact_mod_cast this
  have hrel := golden_tau_relation
  rw [hreal] at hrel
  norm_num at hrel

end InfoGeometry.Categorical.FibonacciFinitePentagonBridge
