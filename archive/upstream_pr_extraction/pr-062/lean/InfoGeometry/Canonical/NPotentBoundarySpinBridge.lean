import Mathlib.Tactic
import InfoGeometry.Topology.ConformalSpin

/-!
# N-potent boundary spectrum and spin-readout firewall

This owner isolates the finite algebraic statement behind an `N`-potent
boundary operator.  If `T ^ N = T`, every eigenvalue satisfies
`lambda ^ N = lambda`; a nonzero eigenvalue is therefore an `(N - 1)`-st
root of unity.

The file deliberately does **not** identify such an eigenvalue with a CFT
conformal spin.  That identification needs an explicit phase/spin witness
from a conformal-block or monodromy owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.NPotentBoundarySpinBridge

open InfoGeometry.Topology.CFT

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem pow_apply_eigenvalue
    (T : Module.End K V) (v : V) (lambda : K)
    (hEig : T v = lambda • v) :
    ∀ m : ℕ, (T ^ m) v = lambda ^ m • v := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Module.End.mul_apply, hEig, map_smul, ih]
      simp [smul_smul, pow_succ]
      rw [mul_comm]

/-- Every eigenvalue of an `N`-potent endomorphism satisfies the same
polynomial relation. -/
theorem eigenvalue_pow_eq_of_nPotent
    (T : Module.End K V) (N : ℕ) (lambda : K) (v : V)
    (hN : T ^ N = T) (hEig : T v = lambda • v) (hv : v ≠ 0) :
    lambda ^ N = lambda := by
  have h := congrArg (fun A : Module.End K V => A v) hN
  change (T ^ N) v = T v at h
  rw [pow_apply_eigenvalue T v lambda hEig, hEig] at h
  exact (smul_left_injective K hv) h

/- The previous theorem is also available in the usual nonzero-root form. -/
theorem nonzero_eigenvalue_pow_pred_eq_one
    (T : Module.End K V) (N : ℕ) (lambda : K) (v : V)
    (hN : T ^ N = T) (hEig : T v = lambda • v)
    (hv : v ≠ 0) (hLam : lambda ≠ 0) (hNpos : 0 < N) :
    lambda ^ (N - 1) = 1 := by
  have hpow : lambda ^ N = lambda :=
    eigenvalue_pow_eq_of_nPotent T N lambda v hN hEig hv
  have hsucc : N - 1 + 1 = N := by omega
  have hmul : lambda ^ (N - 1) * lambda = lambda := by
    rw [← pow_succ, hsucc, hpow]
  apply mul_right_cancel₀ hLam
  simpa using hmul

/- The tripotent specialization exposes the three algebraic eigenvalue
sectors `0`, `+1`, and `-1`. -/
theorem tripotent_eigenvalue_zero_or_sq_eq_one
    (T : Module.End K V) (lambda : K) (v : V)
    (hT : T ^ 3 = T) (hEig : T v = lambda • v) (hv : v ≠ 0) :
    lambda = 0 ∨ lambda ^ 2 = 1 := by
  by_cases hLam : lambda = 0
  · exact Or.inl hLam
  · exact Or.inr
      (nonzero_eigenvalue_pow_pred_eq_one T 3 lambda v hT hEig hv hLam
        (by norm_num))

/-- Exact tripotent eigenvalue sectors over a field: zero, plus one, or minus one. -/
theorem tripotent_eigenvalue_zero_or_one_or_neg_one
    (T : Module.End K V) (lambda : K) (v : V)
    (hT : T ^ 3 = T) (hEig : T v = lambda • v) (hv : v ≠ 0) :
    lambda = 0 ∨ lambda = 1 ∨ lambda = -1 := by
  rcases tripotent_eigenvalue_zero_or_sq_eq_one T lambda v hT hEig hv with
    hzero | hsq
  · exact Or.inl hzero
  · rcases (sq_eq_one_iff.mp hsq) with hone | hneg
    · exact Or.inr (Or.inl hone)
    · exact Or.inr (Or.inr hneg)

end InfoGeometry.Canonical.NPotentBoundarySpinBridge
