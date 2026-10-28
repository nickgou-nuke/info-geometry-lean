/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.OperatorAlgebra.PeirceSignedTransport
import InfoGeometry.OperatorAlgebra.PeirceBoundaryMetric

/-! # Real trace duality, signed transport, and the metric distinction

The signed map is skew-adjoint for the positive Frobenius form. Its square
therefore has nonpositive energy. It is self-adjoint for a separately displayed
indefinite form induced by the Peirce reflection. These are different adjoints.
A nonzero square-zero arrow gives a positive input with nonpositive signed
output, so the signed transfer is not a positive quantum channel.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

open Matrix InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.IdempotentCartan

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem skewTransport_trace (a b x : Matrix n n ℝ) :
    trace (skewTransport ℝ a b x) = -trace ((a*b-b*a)*x) := by
  simp only [skewTransport_apply, trace_sub, sub_mul]
  rw [trace_mul_comm (a*x) b, trace_mul_comm (b*x) a]
  simp only [mul_assoc]
  abel

/-- Adjointness is proved against the actual positive trace pairing. -/
theorem crossTransport_frobenius (a x y : Matrix n n ℝ) :
    trace ((crossTransport ℝ a aᴴ x)ᴴ*y) =
      trace (xᴴ*crossTransport ℝ a aᴴ y) := by
  simp only [crossTransport_apply, conjTranspose_add, add_mul, trace_add,
    sandwich_frobenius_adjoint, conjTranspose_conjTranspose, mul_add]
  exact add_comm _ _

theorem skewTransport_frobenius (a x y : Matrix n n ℝ) :
    trace ((skewTransport ℝ a aᴴ x)ᴴ*y) =
      -trace (xᴴ*skewTransport ℝ a aᴴ y) := by
  simp only [skewTransport_apply, conjTranspose_sub, sub_mul, trace_sub,
    sandwich_frobenius_adjoint, conjTranspose_conjTranspose, mul_sub]
  abel

/-- Hermitian-preserving does not mean positive. -/
theorem skewTransport_isHermitian (a : Matrix n n ℝ) {x : Matrix n n ℝ}
    (hx : x.IsHermitian) : (skewTransport ℝ a aᴴ x).IsHermitian := by
  change (a*x*aᴴ-aᴴ*x*a)ᴴ = a*x*aᴴ-aᴴ*x*a
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
    hx.eq, mul_assoc]

/-- Negative square energy is a Gram square, with no nilpotence hypothesis. -/
theorem skewTransport_energy (a x : Matrix n n ℝ) :
    trace (xᴴ * (-skewTransport ℝ a aᴴ (skewTransport ℝ a aᴴ x))) =
      trace ((skewTransport ℝ a aᴴ x)ᴴ * skewTransport ℝ a aᴴ x) := by
  rw [mul_neg, trace_neg]
  exact (skewTransport_frobenius a x (skewTransport ℝ a aᴴ x)).symm

theorem skewTransport_energy_nonneg (a x : Matrix n n ℝ) :
    0 ≤ trace (xᴴ * (-skewTransport ℝ a aᴴ (skewTransport ℝ a aᴴ x))) := by
  rw [skewTransport_energy]
  exact (posSemidef_conjTranspose_mul_self _).trace_nonneg

/-- The kernel statement concerns full matrix endomorphisms, not eigenvalues. -/
theorem skewTransport_square_ker (a : Matrix n n ℝ) :
    LinearMap.ker (skewTransport ℝ a aᴴ * skewTransport ℝ a aᴴ) =
      LinearMap.ker (skewTransport ℝ a aᴴ) := by
  ext x
  change skewTransport ℝ a aᴴ (skewTransport ℝ a aᴴ x)=0 ↔
    skewTransport ℝ a aᴴ x=0
  constructor
  · intro h
    apply trace_conjTranspose_mul_self_eq_zero_iff.mp
    have he := skewTransport_energy a x
    simpa only [h, neg_zero, mul_zero, trace_zero] using he.symm
  · intro h
    rw [h, map_zero]

/-- A faithful positive-metric test detects the signed map's positivity failure. -/
theorem skewTransport_not_positive {a : Matrix n n ℝ}
    (ha : a*a=0) (hne : a≠0) :
    ¬ (skewTransport ℝ a aᴴ (a*aᴴ)).PosSemidef := by
  have hform : skewTransport ℝ a aᴴ (a*aᴴ) =
      -((aᴴ*a)ᴴ*(aᴴ*a)) := by
    simp only [skewTransport_apply, conjTranspose_mul, conjTranspose_conjTranspose]
    have hn (x : Matrix n n ℝ) : a*(a*x)=0 := by rw [← mul_assoc, ha, zero_mul]
    noncomm_ring [ha, hn]
  have hz : aᴴ*a ≠ 0 := by
    intro h
    apply hne
    apply trace_conjTranspose_mul_self_eq_zero_iff.mp
    rw [h, trace_zero]
  have htrace : trace ((aᴴ*a)ᴴ*(aᴴ*a)) ≠ 0 :=
    mt trace_conjTranspose_mul_self_eq_zero_iff.mp hz
  intro h
  rw [hform] at h
  have hle := h.trace_nonneg
  rw [trace_neg] at hle
  have hge := (posSemidef_conjTranspose_mul_self (aᴴ*a)).trace_nonneg
  apply htrace
  linarith

/-- Explicit positive input accompanies the nonpositivity statement. -/
theorem skewTransport_positive_input_obstruction {a : Matrix n n ℝ}
    (ha : a*a=0) (hne : a≠0) :
    (a*aᴴ).PosSemidef ∧ ¬ (skewTransport ℝ a aᴴ (a*aᴴ)).PosSemidef :=
  ⟨posSemidef_self_mul_conjTranspose a, skewTransport_not_positive ha hne⟩

section Reflection
variable {p : Matrix n n ℝ} (hp : p*p=p)

/-- A fundamental involution on the entire real matrix carrier. -/
theorem left_reflection_involution :
    LinearMap.mulLeft ℝ (reflection p) * LinearMap.mulLeft ℝ (reflection p) =
      (1 : Module.End ℝ (Matrix n n ℝ)) := by
  ext x
  change reflection p*(reflection p*x)=x
  rw [← mul_assoc, reflection_sq hp, one_mul]

/-- Applying the involution in the second slot recovers positive Frobenius norm. -/
theorem left_reflection_positive (x : Matrix n n ℝ) (hx : x≠0) :
    0 < trace (xᴴ * reflection p * (reflection p*x)) := by
  have he : xᴴ * reflection p * (reflection p*x)=xᴴ*x := by
    simp only [mul_assoc, ← mul_assoc (reflection p) (reflection p), reflection_sq hp, one_mul]
  rw [he]
  have hn := (posSemidef_conjTranspose_mul_self x).trace_nonneg
  have hz : trace (xᴴ*x)≠0 := mt trace_conjTranspose_mul_self_eq_zero_iff.mp hx
  exact lt_of_le_of_ne hn (Ne.symm hz)

/-- The signed map is self-adjoint for B(x,y)=tr(x^T S y), not for Frobenius. -/
theorem skewTransport_krein_pairing (hps : pᴴ=p) (a x y : Matrix n n ℝ) :
    trace ((skewTransport ℝ (component10 p a) (component10 p a)ᴴ x)ᴴ *
      reflection p * y) =
    trace (xᴴ * reflection p *
      skewTransport ℝ (component10 p a) (component10 p a)ᴴ y) := by
  have hr : component01 p aᴴ = (component10 p a)ᴴ := by
    simp only [component01, component10, complementIdempotent, conjTranspose_mul,
      conjTranspose_sub, conjTranspose_one, hps, mul_assoc]
  have hin := congrArg (fun f : Module.End ℝ (Matrix n n ℝ) => f y)
    (skewTransport_reflection ℝ hp a aᴴ)
  have hout := congrArg (fun f : Module.End ℝ (Matrix n n ℝ) => f y)
    (reflection_skewTransport ℝ hp a aᴴ)
  rw [hr] at hin hout
  change skewTransport ℝ (component10 p a) (component10 p a)ᴴ (reflection p*y) =
    -crossTransport ℝ (component10 p a) (component10 p a)ᴴ y at hin
  change reflection p*skewTransport ℝ (component10 p a) (component10 p a)ᴴ y =
    crossTransport ℝ (component10 p a) (component10 p a)ᴴ y at hout
  rw [mul_assoc, skewTransport_frobenius, hin, ← hout, mul_neg, trace_neg, neg_neg]
  simp only [mul_assoc]

/-- Graded trace of the signed output recovers the symmetric expectation. -/
theorem skewTransport_weighted_trace (a b x : Matrix n n ℝ) :
    trace (reflection p *
      skewTransport ℝ (component10 p a) (component01 p b) x) =
    trace ((component10 p a*component01 p b+component01 p b*component10 p a)*x) := by
  have h := congrArg (fun f : Module.End ℝ (Matrix n n ℝ) => f x)
    (reflection_skewTransport ℝ hp a b)
  change reflection p*skewTransport ℝ (component10 p a) (component01 p b) x =
    crossTransport ℝ (component10 p a) (component01 p b) x at h
  rw [h, crossTransport_trace]

end Reflection
end InfoGeometry.OperatorAlgebra.LieJordan
