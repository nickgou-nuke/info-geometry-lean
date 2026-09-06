import InfoGeometry.Quantum.NeutralKreinMajoranaFrame

/-!
# Finite semi-Riemannian Krein bridge

This is the finite matrix shadow of the fundamental-symmetry construction in
semi-Riemannian spectral geometry.  It packages the existing neutral frame;
it does not assert a spectral triple, a Dirac operator, or Tomita theory.
-/

namespace InfoGeometry.Quantum.FiniteSemiRiemannianKreinBridge

open InfoGeometry.Quantum.NeutralKreinMajoranaFrame

abbrev FrameMatrix (n : ℕ) := Matrix (Carrier n) (Carrier n) ℝ

/-- Algebraic fundamental-symmetry conditions for a neutral matrix frame. -/
def IsFiniteFundamentalSymmetry (η R : FrameMatrix n) : Prop :=
  R * R = (1 : FrameMatrix n) ∧
    R.transpose * η * R = η

theorem exchange_is_finite_fundamental_symmetry (n : ℕ) :
    IsFiniteFundamentalSymmetry (kreinMetric n) (exchange n) := by
  constructor
  · exact exchange_sq n
  · rw [kreinMetric_is_neutral]
    rw [exchange, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.one_apply]

theorem exchange_positive_readout_identity (n : ℕ) :
    kreinMetric n * exchange n = (1 : FrameMatrix n) := by
  exact positiveReadout_eq_identity n

theorem exchange_positive_readout_on_frame (n : ℕ) (x : Carrier n) :
    (kreinMetric n * exchange n) x x = (1 : ℝ) := by
  rw [exchange_positive_readout_identity]
  simp

theorem grading_is_anti_isometry (n : ℕ) :
    (grading n).transpose * kreinMetric n * grading n = -(kreinMetric n) :=
  kreinMetric_grading_anti_isometry n

end InfoGeometry.Quantum.FiniteSemiRiemannianKreinBridge
