import Mathlib.Tactic
import InfoGeometry.Foundations.NewtonKantorovich

/-!
# InfoGeometry.Foundations.NewtonKantorovichJacobianCertificate

Jacobian/Lipschitz certificate wrapper for Newton--Kantorovich convergence.

This file packages the majorant-side contractive/Cauchy guarantees into a
reusable interface suitable for downstream problem families.
-/

namespace InfoGeometry.Foundations.NewtonKantorovichJacobianCertificate

open InfoGeometry.Foundations.NewtonKantorovich
open InfoGeometry.Foundations.NewtonKantorovichSequence

noncomputable section

/--
Abstract scalar NK certificate data:
`L` is the local derivative-Lipschitz constant and `η` the initial residual
majorant, with optional geometric-step witness constants `C, q`.
-/
structure NKScalarCertificate where
  L : ℝ
  η : ℝ
  C : ℝ
  q : ℝ
  h_nonneg : 0 ≤ L * η
  h_half : L * η ≤ 1 / 2
  hq : q < 1
  hstep :
    ∀ n,
      dist (majorantSeq L η (n + 1)) (majorantSeq L η (n + 2)) ≤ C * q ^ n

/-- Under a scalar NK certificate, the shifted majorant sequence is Cauchy. -/
theorem majorant_shifted_cauchy_of_law
    (cert : NKScalarCertificate) :
    CauchySeq (fun n => majorantSeq cert.L cert.η (n + 1)) := by
  exact majorant_seq_cauchy_of_h_le_half cert.L cert.η cert.C cert.q cert.h_half cert.hq cert.hstep

/--
Readable alias for the certificate safety inequality:
`0 ≤ 1 - 2(Lη)`.
-/
theorem safety_margin_nonneg (cert : NKScalarCertificate) :
    0 ≤ 1 - 2 * (cert.L * cert.η) := by
  exact h_safe (cert.L * cert.η) cert.h_half

/--
In the zero-residual lane (`η = 0`), the majorant sequence is identically zero.
-/
theorem majorantSeq_zero_residual
    (L : ℝ) :
    ∀ n, majorantSeq L 0 n = 0 := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [majorantSeq_succ, ih, majorantStep]

/--
Explicit geometric step bound for the zero-residual lane:
all consecutive distances are zero, hence bounded by `0 * q^n`.
-/
theorem hstep_zero_residual
    (L q : ℝ) :
    ∀ n,
      dist (majorantSeq L 0 (n + 1)) (majorantSeq L 0 (n + 2)) ≤ 0 * q ^ n := by
  intro n
  rw [majorantSeq_zero_residual L (n + 1), majorantSeq_zero_residual L (n + 2)]
  simp

/--
Strict-branch certificate constructor from a strict threshold and a geometric
step witness.
-/
def mkStrict
    (L η C q : ℝ)
    (h_nonneg : 0 ≤ L * η)
    (h_strict : L * η < 1 / 2)
    (hq : q < 1)
    (hstep :
      ∀ n,
        dist (majorantSeq L η (n + 1)) (majorantSeq L η (n + 2)) ≤ C * q ^ n) :
    NKScalarCertificate where
  L := L
  η := η
  C := C
  q := q
  h_nonneg := h_nonneg
  h_half := le_of_lt h_strict
  hq := hq
  hstep := hstep

/- The shifted sequence is Cauchy in the zero-residual lane directly from the
   owner theorem, without constructing an intermediate evidence value. -/
theorem zeroResidual_shifted_cauchy
    (L : ℝ) :
    CauchySeq (fun n => majorantSeq L 0 (n + 1)) := by
  have h_half : L * 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hq : (0 : ℝ) < 1 := by norm_num
  exact majorant_seq_cauchy_of_h_le_half L 0 0 0 h_half hq
    (hstep_zero_residual L 0)

end
end InfoGeometry.Foundations.NewtonKantorovichJacobianCertificate
