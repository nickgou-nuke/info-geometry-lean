import Mathlib
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
theorem majorant_shifted_cauchy_of_certificate
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

end
end InfoGeometry.Foundations.NewtonKantorovichJacobianCertificate
