/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceGradedDifferential
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

/-- Positivity requires the transpose pairing; it is not automatic for independent arrows. -/
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
local notation "θ" => AlgEquiv.toAlgHom (peirceTwist ℝ p hp)

private theorem reflection_conjTranspose : (reflection p)ᴴ = reflection p := by
  simp only [reflection, two_nsmul, conjTranspose_sub, conjTranspose_add,
    conjTranspose_one, hps]

theorem peirceTwist_transpose (x : Matrix n n ℝ) :
    (θ x)ᴴ = θ xᴴ := by
  change (reflection p * x * reflection p)ᴴ = reflection p * xᴴ * reflection p
  simp only [conjTranspose_mul, reflection_conjTranspose hps, mul_assoc]

theorem peirceTwist_frobenius_adjoint (x y : Matrix n n ℝ) :
    trace ((θ x)ᴴ * y) = trace (xᴴ * θ y) := by
  change trace ((reflection p * x * reflection p)ᴴ * y) =
    trace (xᴴ * (reflection p * y * reflection p))
  rw [sandwich_frobenius_adjoint, reflection_conjTranspose hps]

variable {q : Matrix n n ℝ} (hq : θ q = -q)
include hq
local notation "d" => twistedInner ℝ θ q
local notation "c" => twistedCoInner ℝ θ qᴴ

theorem peirce_odd_transpose : θ qᴴ = -qᴴ := by
  rw [← peirceTwist_transpose hp hps, hq, conjTranspose_neg]

/-- An actual adjoint identity in the positive real trace pairing. -/
theorem boundary_frobenius_adjoint (x y : Matrix n n ℝ) :
    trace ((d x)ᴴ * y) = trace (xᴴ * c y) := by
  simp only [twistedInner_apply, twistedCoInner_apply, conjTranspose_sub,
    conjTranspose_mul, sub_mul, trace_sub]
  have hcyc : trace ((qᴴ * (θ x)ᴴ) * y) = trace ((θ x)ᴴ * (y * qᴴ)) := by
    rw [mul_assoc, trace_mul_comm qᴴ, mul_assoc]
  rw [hcyc, peirceTwist_frobenius_adjoint hp hps,
    map_mul, peirce_odd_transpose hp hps hq]
  simp only [mul_neg, trace_neg, sub_neg_eq_add, mul_add, trace_add, mul_assoc]

/-- This, not the two-boundary Lie action, is the adjoint-pair Laplacian. -/
theorem boundary_adjoint_laplacian :
    d * c + c * d = jordanOp ℝ (q * qᴴ + qᴴ * q) :=
  twistedInner_coInner ℝ θ (peirceTwist_involutive ℝ p hp) hq
    (peirce_odd_transpose hp hps hq)

/-- Exact sum-of-Gram energies, with no spectral or commuting reduction. -/
theorem boundary_energy (x : Matrix n n ℝ) :
    trace (xᴴ * jordanOp ℝ (q * qᴴ + qᴴ * q) x) =
      trace ((d x)ᴴ * d x) + trace ((c x)ᴴ * c x) := by
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
  exact add_nonneg (posSemidef_conjTranspose_mul_self (d x)).trace_nonneg
    (posSemidef_conjTranspose_mul_self (c x)).trace_nonneg

/-- The harmonic subspace is the intersection of the two actual kernels. -/
theorem boundary_laplacian_ker :
    LinearMap.ker (jordanOp ℝ (q * qᴴ + qᴴ * q)) =
      LinearMap.ker d ⊓ LinearMap.ker c := by
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
