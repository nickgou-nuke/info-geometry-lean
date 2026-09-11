import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite cyclotomic Andreev conjugation

This owner records the algebraic charge-conjugation statement used by the
parafermion discussion.  A finite-order charge `Q` is conjugated to its
inverse power by an involution `A`; consequently a `ζ`-eigenvector is sent to
a `ζ⁻¹`-eigenvector.  No Galois, analytic, or C*-completion claim is made.
-/

noncomputable section

namespace InfoGeometry.Canonical.CyclotomicAndreevConjugationBridge

structure Datum (V : Type*) [AddCommGroup V] [Module ℂ V] (N : ℕ) where
  Q : Module.End ℂ V
  A : Module.End ℂ V
  Q_pow : Q ^ N = (1 : Module.End ℂ V)
  A_sq : A * A = (1 : Module.End ℂ V)
  conjugates : A * Q * A = Q ^ (N - 1)

theorem charge_inverse_intertwining
    {V : Type*} [AddCommGroup V] [Module ℂ V] {N : ℕ}
    (D : Datum V N) :
    D.Q * D.A = D.A * D.Q ^ (N - 1) := by
  calc
    D.Q * D.A = (1 : Module.End ℂ V) * D.Q * D.A := by simp
    _ = (D.A * D.A) * D.Q * D.A := by rw [D.A_sq]
    _ = D.A * (D.A * D.Q * D.A) := by noncomm_ring
    _ = D.A * D.Q ^ (N - 1) := by rw [D.conjugates]

private theorem pow_apply_eigenvector
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Q : Module.End ℂ V) (ζ : ℂ) (v : V)
    (hv : Q v = ζ • v) :
    ∀ k : ℕ, (Q ^ k) v = ζ ^ k • v := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul]
      simp [pow_succ]
      module

private theorem inverse_power_eq
    {N : ℕ} {ζ : ℂ} (hN : 1 ≤ N) (hζ : ζ ≠ 0) (hroot : ζ ^ N = 1) :
    ζ ^ (N - 1) = ζ⁻¹ := by
  have hmul : ζ ^ (N - 1) * ζ = 1 := by
    calc
      ζ ^ (N - 1) * ζ = ζ ^ ((N - 1) + 1) := by rw [pow_succ]
      _ = ζ ^ N := by congr 1; omega
      _ = 1 := hroot
  calc
    ζ ^ (N - 1) = ζ ^ (N - 1) * 1 := by simp
    _ = ζ ^ (N - 1) * (ζ * ζ⁻¹) := by rw [mul_inv_cancel₀ hζ]
    _ = (ζ ^ (N - 1) * ζ) * ζ⁻¹ := by ring
    _ = ζ⁻¹ := by rw [hmul, one_mul]

theorem andreev_maps_cyclotomic_eigenvector
    {V : Type*} [AddCommGroup V] [Module ℂ V] {N : ℕ}
    (D : Datum V N) {ζ : ℂ} {v : V}
    (hN : 1 ≤ N) (hζ : ζ ≠ 0) (hroot : ζ ^ N = 1)
    (hv : D.Q v = ζ • v) :
    D.Q (D.A v) = ζ⁻¹ • D.A v := by
  have hpow := (pow_apply_eigenvector D.Q ζ v hv) (N - 1)
  calc
    D.Q (D.A v) = (D.Q * D.A) v := rfl
    _ = (D.A * D.Q ^ (N - 1)) v := by
      rw [charge_inverse_intertwining D]
    _ = D.A ((D.Q ^ (N - 1)) v) := rfl
    _ = D.A (ζ ^ (N - 1) • v) := by rw [hpow]
    _ = ζ ^ (N - 1) • D.A v := by rw [map_smul]
    _ = ζ⁻¹ • D.A v := by rw [inverse_power_eq hN hζ hroot]

end InfoGeometry.Canonical.CyclotomicAndreevConjugationBridge
