import Mathlib.Tactic
import InfoGeometry.Foundations.NewtonKantorovich

/-!
# InfoGeometry.Foundations.NewtonKantorovichJacobianCertificate

Jacobian/Lipschitz property wrapper for Newton--Kantorovich convergence.

This file packages the majorant-side contractive/Cauchy guarantees into a
reusable interface suitable for downstream problem families.
-/

namespace InfoGeometry.Foundations.NewtonKantorovichJacobianCertificate

open InfoGeometry.Foundations.NewtonKantorovich
open InfoGeometry.Foundations.NewtonKantorovichSequence

noncomputable section

/--
Abstract scalar NK property data:
`L` is the local derivative-Lipschitz constant and `η` the initial residual
majorant, with optional geometric-step property constants `C, q`.
-/
def NKScalarCertificate : Type _ :=
  {p : ℝ × ℝ × ℝ × ℝ //
    0 ≤ p.1 * p.2.1 ∧
    p.1 * p.2.1 ≤ 1 / 2 ∧
    p.2.2.2 < 1 ∧
    ∀ n,
      dist (majorantSeq p.1 p.2.1 (n + 1))
        (majorantSeq p.1 p.2.1 (n + 2)) ≤ p.2.2.1 * p.2.2.2 ^ n}

namespace NKScalarCertificate

/-- Native tuple projection for the local Lipschitz constant. -/
abbrev L (cert : NKScalarCertificate) : ℝ := cert.1.1

/-- Native tuple projection for the initial residual majorant. -/
abbrev η (cert : NKScalarCertificate) : ℝ := cert.1.2.1

/-- Native tuple projection for the geometric step constant. -/
abbrev C (cert : NKScalarCertificate) : ℝ := cert.1.2.2.1

/-- Native tuple projection for the geometric ratio. -/
abbrev q (cert : NKScalarCertificate) : ℝ := cert.1.2.2.2

/-- Native subtype proof of the nonnegativity condition. -/
theorem h_nonneg (cert : NKScalarCertificate) : 0 ≤ cert.L * cert.η :=
  cert.2.1

/-- Native subtype proof of the Newton--Kantorovich half-bound. -/
theorem h_half (cert : NKScalarCertificate) : cert.L * cert.η ≤ 1 / 2 :=
  cert.2.2.1

/-- Native subtype proof that the geometric ratio is contractive. -/
theorem hq (cert : NKScalarCertificate) : cert.q < 1 :=
  cert.2.2.2.1

/-- Native subtype proof of the geometric step estimate. -/
theorem hstep (cert : NKScalarCertificate) :
    ∀ n,
      dist (majorantSeq cert.L cert.η (n + 1))
        (majorantSeq cert.L cert.η (n + 2)) ≤ cert.C * cert.q ^ n :=
  cert.2.2.2.2

end NKScalarCertificate

/-- Under a scalar NK property, the shifted majorant sequence is Cauchy. -/
theorem majorant_shifted_cauchy_of_law
    (cert : NKScalarCertificate) :
    CauchySeq (fun n => majorantSeq cert.L cert.η (n + 1)) := by
  exact majorant_seq_cauchy_of_h_le_half cert.L cert.η cert.C cert.q cert.h_half cert.hq cert.hstep

/--
Readable alias for the property safety inequality:
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
Strict-branch property constructor from a strict threshold and a geometric
step property.
-/
def mkStrict
    (L η C q : ℝ)
    (h_nonneg : 0 ≤ L * η)
    (h_strict : L * η < 1 / 2)
    (hq : q < 1)
    (hstep :
      ∀ n,
        dist (majorantSeq L η (n + 1)) (majorantSeq L η (n + 2)) ≤ C * q ^ n) :
    NKScalarCertificate := by
  refine ⟨(L, η, C, q), ?_⟩
  exact ⟨h_nonneg, le_of_lt h_strict, hq, hstep⟩

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
