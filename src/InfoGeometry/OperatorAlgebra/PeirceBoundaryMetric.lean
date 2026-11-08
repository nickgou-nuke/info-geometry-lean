/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanGradedDifferential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith

/-! # Real adjoint boundaries, energy, and harmonic kernels

The pairing is the actual positive Frobenius trace on the entire real matrix
algebra. The adjoint of the twisted minus action is the twisted PLUS action
of the transpose. Consequently the adjoint Laplacian is Jordan multiplication,
whereas the anticommutator of two minus actions is a Lie action.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

open Matrix InfoGeometry.Core.IdempotentCartan

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Cyclic trace of the two-sided transport requires no parity restriction. -/
theorem crossTransport_trace (a b x : Matrix n n ℝ) :
    trace (crossTransport ℝ a b x) = trace ((a * b + b * a) * x) := by
  simp only [crossTransport_apply, trace_add, add_mul]
  rw [trace_mul_comm (a * x) b, trace_mul_comm (b * x) a]
  simp only [mul_assoc]
  abel

/-- The transpose pairing suffices for positivity; independent arrows need not. -/
theorem crossTransport_positive (a : Matrix n n ℝ) {x : Matrix n n ℝ}
    (hx : x.PosSemidef) : (crossTransport ℝ a aᴴ x).PosSemidef := by
  change (a * x * aᴴ + aᴴ * x * a).PosSemidef
  exact (hx.mul_mul_conjTranspose_same a).add (hx.conjTranspose_mul_mul_same a)

/-- Trace preservation is a normalization hypothesis, not an interpretation. -/
theorem crossTransport_trace_of_normalized (a b : Matrix n n ℝ)
    (h : a * b + b * a = 1) (x : Matrix n n ℝ) :
    trace (crossTransport ℝ a b x) = trace x := by
  rw [crossTransport_trace, h, one_mul]

omit [DecidableEq n] in
theorem frobenius_trace_symm (x y : Matrix n n ℝ) :
    trace (xᴴ * y) = trace (yᴴ * x) := by
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose, star_trivial]
    using (trace_conjTranspose (xᴴ * y)).symm

omit [DecidableEq n] in
theorem sandwich_frobenius_adjoint (a b x y : Matrix n n ℝ) :
    trace ((a * x * b)ᴴ * y) = trace (xᴴ * (aᴴ * y * bᴴ)) := by
  simp only [conjTranspose_mul]
  calc
    _ = trace (bᴴ * (xᴴ * (aᴴ * y))) := by simp only [mul_assoc]
    _ = trace ((xᴴ * (aᴴ * y)) * bᴴ) := trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

variable {p : Matrix n n ℝ} (hp : p * p = p) (hps : pᴴ = p)
include hps

private theorem reflection_conjTranspose : (reflection p)ᴴ = reflection p := by
  simp only [reflection, two_nsmul, conjTranspose_sub, conjTranspose_add,
    conjTranspose_one, hps]

theorem peirceTwist_transpose (x : Matrix n n ℝ) :
    ((peirceTwist ℝ p hp).toAlgHom x)ᴴ =
      (peirceTwist ℝ p hp).toAlgHom xᴴ := by
  change (reflection p * x * reflection p)ᴴ = reflection p * xᴴ * reflection p
  simp only [conjTranspose_mul, reflection_conjTranspose hps, mul_assoc]

theorem peirceTwist_frobenius_adjoint (x y : Matrix n n ℝ) :
    trace (((peirceTwist ℝ p hp).toAlgHom x)ᴴ * y) =
      trace (xᴴ * (peirceTwist ℝ p hp).toAlgHom y) := by
  change trace ((reflection p * x * reflection p)ᴴ * y) =
    trace (xᴴ * (reflection p * y * reflection p))
  rw [sandwich_frobenius_adjoint, reflection_conjTranspose hps]

variable {q : Matrix n n ℝ} (hq : (peirceTwist ℝ p hp).toAlgHom q = -q)
include hp hq

theorem peirce_odd_transpose : (peirceTwist ℝ p hp).toAlgHom qᴴ = -qᴴ := by
  rw [← peirceTwist_transpose hp hps, hq, conjTranspose_neg]

/-- An actual adjoint identity in the positive real trace pairing. -/
theorem boundary_frobenius_adjoint (x y : Matrix n n ℝ) :
    trace ((twistedInner ℝ (peirceTwist ℝ p hp).toAlgHom q x)ᴴ * y) =
      trace (xᴴ * twistedCoInner ℝ (peirceTwist ℝ p hp).toAlgHom qᴴ y) := by
  simp only [twistedInner_apply, twistedCoInner_apply, conjTranspose_sub,
    conjTranspose_mul, sub_mul, trace_sub]
  have hcyc : trace ((qᴴ * ((peirceTwist ℝ p hp).toAlgHom x)ᴴ) * y) =
      trace (((peirceTwist ℝ p hp).toAlgHom x)ᴴ * (y * qᴴ)) := by
    rw [mul_assoc, trace_mul_comm qᴴ, mul_assoc]
  rw [hcyc, peirceTwist_frobenius_adjoint hp hps,
    map_mul, peirce_odd_transpose hp hps hq]
  simp only [mul_neg, trace_neg, sub_neg_eq_add, mul_add, trace_add, mul_assoc]

/-- This, not the two-boundary Lie action, is the adjoint-pair Laplacian. -/
theorem boundary_adjoint_laplacian :
    twistedInner ℝ (peirceTwist ℝ p hp).toAlgHom q *
        twistedCoInner ℝ (peirceTwist ℝ p hp).toAlgHom qᴴ +
      twistedCoInner ℝ (peirceTwist ℝ p hp).toAlgHom qᴴ *
        twistedInner ℝ (peirceTwist ℝ p hp).toAlgHom q =
      jordanOp ℝ (q * qᴴ + qᴴ * q) :=
  twistedInner_coInner ℝ (peirceTwist ℝ p hp).toAlgHom
    (peirceTwist_involutive ℝ p hp) hq (peirce_odd_transpose hp hps hq)

/-- Exact sum-of-Gram energies, with no spectral or commuting reduction. -/
theorem boundary_energy (x : Matrix n n ℝ) :
    trace (xᴴ * jordanOp ℝ (q * qᴴ + qᴴ * q) x) =
      trace ((twistedInner ℝ (peirceTwist ℝ p hp).toAlgHom q x)ᴴ *
        twistedInner ℝ (peirceTwist ℝ p hp).toAlgHom q x) +
      trace ((twistedCoInner ℝ (peirceTwist ℝ p hp).toAlgHom qᴴ x)ᴴ *
        twistedCoInner ℝ (peirceTwist ℝ p hp).toAlgHom qᴴ x) := by
  let d := twistedInner ℝ (peirceTwist ℝ p hp).toAlgHom q
  let c := twistedCoInner ℝ (peirceTwist ℝ p hp).toAlgHom qᴴ
  change trace (xᴴ * jordanOp ℝ (q * qᴴ + qᴴ * q) x) =
    trace ((d x)ᴴ * d x) + trace ((c x)ᴴ * c x)
  have hL : jordanOp ℝ (q * qᴴ + qᴴ * q) x = d (c x) + c (d x) :=
    (congrArg (fun f : Module.End ℝ (Matrix n n ℝ) => f x)
      (boundary_adjoint_laplacian hp hps hq)).symm
  rw [hL, mul_add, trace_add]
  rw [frobenius_trace_symm x (d (c x)),
    boundary_frobenius_adjoint hp hps hq (c x) x,
    ← boundary_frobenius_adjoint hp hps hq x (d x)]
  exact add_comm _ _

theorem boundary_energy_nonneg (x : Matrix n n ℝ) :
    0 ≤ trace (xᴴ * jordanOp ℝ (q * qᴴ + qᴴ * q) x) := by
  rw [boundary_energy hp hps hq]
  exact add_nonneg
    (posSemidef_conjTranspose_mul_self
      (twistedInner ℝ (peirceTwist ℝ p hp).toAlgHom q x)).trace_nonneg
    (posSemidef_conjTranspose_mul_self
      (twistedCoInner ℝ (peirceTwist ℝ p hp).toAlgHom qᴴ x)).trace_nonneg

/-- The harmonic subspace is the intersection of the two actual kernels. -/
theorem boundary_laplacian_ker :
    LinearMap.ker (jordanOp ℝ (q * qᴴ + qᴴ * q)) =
      LinearMap.ker (twistedInner ℝ (peirceTwist ℝ p hp).toAlgHom q) ⊓
      LinearMap.ker (twistedCoInner ℝ (peirceTwist ℝ p hp).toAlgHom qᴴ) := by
  let d := twistedInner ℝ (peirceTwist ℝ p hp).toAlgHom q
  let c := twistedCoInner ℝ (peirceTwist ℝ p hp).toAlgHom qᴴ
  ext x
  change jordanOp ℝ (q * qᴴ + qᴴ * q) x = 0 ↔ d x = 0 ∧ c x = 0
  constructor
  · intro hx
    have he := boundary_energy hp hps hq x
    rw [hx, mul_zero, trace_zero] at he
    have hd := (posSemidef_conjTranspose_mul_self (d x)).trace_nonneg
    have hc := (posSemidef_conjTranspose_mul_self (c x)).trace_nonneg
    constructor
    · apply trace_conjTranspose_mul_self_eq_zero_iff.mp
      linarith
    · apply trace_conjTranspose_mul_self_eq_zero_iff.mp
      linarith
  · rintro ⟨hd, hc⟩
    have hL := congrArg (fun f : Module.End ℝ (Matrix n n ℝ) => f x)
      (boundary_adjoint_laplacian hp hps hq)
    change d (c x) + c (d x) = _ at hL
    simpa only [hd, hc, map_zero, add_zero] using hL.symm

end InfoGeometry.OperatorAlgebra.LieJordan
