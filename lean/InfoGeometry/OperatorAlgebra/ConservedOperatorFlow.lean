/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TransportLieDerivative
import InfoGeometry.OperatorAlgebra.ChiralCouplingOperators

/-!
# Conserved operators under the existing exponential transport

The operator algebra need not commute. Only scalar multiples of a single
generator commute, as required for a one-parameter group. Fixedness at all
times is equivalent to the actual generator commutator vanishing. These
are Banach-algebra transport theorems; identifying this flow with the modular
flow of a specified faithful state is separate additional mathematics.
-/

namespace InfoGeometry.OperatorAlgebra.ConservedOperatorFlow

open InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.ChiralCouplingOperators

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [NormedAlgebra ℝ A] [CompleteSpace A]

private theorem exponential_add (H : A) (s t : ℝ) :
    NormedSpace.exp ((s + t) • H) =
      NormedSpace.exp (s • H) * NormedSpace.exp (t • H) := by
  rw [add_smul]
  apply NormedSpace.exp_add_of_commute
  change (s • H) * (t • H) = (t • H) * (s • H)
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm s t]

private theorem exponential_cancel (H : A) (t : ℝ) :
    NormedSpace.exp (t • H) * NormedSpace.exp (t • (-H)) = 1 := by
  have hc : Commute (t • H) (t • (-H)) := by
    rw [smul_neg]
    exact (Commute.refl _).neg_right
  rw [← NormedSpace.exp_add_of_commute hc]
  simp

@[simp] theorem flow_zero (H a : A) : expTransport H a 0 = a := by
  simp [expTransport]

@[simp] theorem flow_one (H : A) (t : ℝ) : expTransport H 1 t = 1 := by
  simpa [expTransport] using exponential_cancel H t

theorem flow_add_time (H a : A) (s t : ℝ) :
    expTransport H a (s + t) = expTransport H (expTransport H a t) s := by
  have hn : NormedSpace.exp ((s + t) • (-H)) =
      NormedSpace.exp (t • (-H)) * NormedSpace.exp (s • (-H)) := by
    rw [add_comm s t]
    exact exponential_add (-H) t s
  simp only [expTransport, exponential_add H s t, hn, mul_assoc]

theorem flow_inverse (H a : A) (t : ℝ) :
    expTransport H (expTransport H a t) (-t) = a := by
  rw [← flow_add_time, neg_add_cancel, flow_zero]

theorem flow_mul (H a b : A) (t : ℝ) :
    expTransport H (a * b) t = expTransport H a t * expTransport H b t := by
  have hi : NormedSpace.exp (t • (-H)) * NormedSpace.exp (t • H) = 1 := by
    simpa using exponential_cancel (-H) t
  unfold expTransport
  calc (NormedSpace.exp (t • H) * (a * b)) * NormedSpace.exp (t • (-H))
      = NormedSpace.exp (t • H) * a * 1 * b * NormedSpace.exp (t • (-H)) := by
          noncomm_ring
    _ = NormedSpace.exp (t • H) * a *
          (NormedSpace.exp (t • (-H)) * NormedSpace.exp (t • H)) * b *
            NormedSpace.exp (t • (-H)) := by rw [hi]
    _ = _ := by noncomm_ring

theorem flow_smul (H a : A) (c t : ℝ) :
    expTransport H (c • a) t = c • expTransport H a t := by
  simp [expTransport, mul_smul_comm, smul_mul_assoc]

theorem flow_pow (H a : A) (t : ℝ) (k : ℕ) :
    expTransport H (a ^ k) t = (expTransport H a t) ^ k := by
  induction k with
  | zero => simp
  | succ k hk => rw [pow_succ, flow_mul, hk, pow_succ]

/-- Operator-level conservation, with the converse from derivative uniqueness. -/
theorem conserved_iff_commute (H Q : A) :
    (∀ t : ℝ, expTransport H Q t = Q) ↔ Commute H Q := by
  constructor
  · intro h
    have he : (fun t : ℝ => expTransport H Q t) = fun _ => Q := funext h
    have hd := hasDerivAt_expTransport_at_zero H Q
    rw [he] at hd
    have hz := hd.unique (hasDerivAt_const (0 : ℝ) Q)
    change H * Q = Q * H
    exact sub_eq_zero.mp (by simpa only [Ring.lie_def] using hz)
  · intro h t
    exact expTransport_eq_self_of_commute H Q t h.symm

/-- The existing derivative is a genuine continuous-linear Frechet derivative. -/
theorem flow_hasFDerivAt (H a : A) (t : ℝ) :
    HasFDerivAt (fun s : ℝ => expTransport H a s)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (expTransport H ⁅H, a⁆ t)) t :=
  (hasDerivAt_expTransport H a t).hasFDerivAt

theorem flow_preserves_idempotent (H P : A) (hP : P * P = P) (t : ℝ) :
    expTransport H P t * expTransport H P t = expTransport H P t := by
  rw [← flow_mul, hP]

theorem flow_preserves_square_zero (H N : A) (hN : N * N = 0) (t : ℝ) :
    expTransport H N t * expTransport H N t = 0 := by
  rw [← flow_mul, hN]
  simp [expTransport]

/-- Grading-compatible motion commutes with the explicitly defined state average. -/
theorem flow_parityAverage (H γ a : A) (hγ : Commute H γ) (t : ℝ) :
    expTransport H (parityAverage γ a) t = parityAverage γ (expTransport H a t) := by
  have hg := (conserved_iff_commute H γ).mpr hγ t
  simp only [parityAverage, flow_smul, expTransport_add_seed, flow_mul, hg]

/-- The coupling square is conserved by its own full operator flow. -/
theorem coupling_square_conserved (D : A) (t : ℝ) :
    expTransport D (D * D) t = D * D := by
  apply (conserved_iff_commute D (D * D)).mpr
  change D * (D * D) = (D * D) * D
  exact (mul_assoc D D D).symm

end InfoGeometry.OperatorAlgebra.ConservedOperatorFlow
