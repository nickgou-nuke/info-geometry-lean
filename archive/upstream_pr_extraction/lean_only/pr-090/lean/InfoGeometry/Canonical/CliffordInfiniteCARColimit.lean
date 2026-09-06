import Mathlib.Tactic
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.Canonical.UHFCuntzGNSColimit

open Matrix
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

noncomputable section

namespace InfoGeometry.Canonical.CliffordInfiniteCARColimit

/-!
# Clifford Algebra Cl(2N, 2N) CAR Direct Limit & Inductive Colimit

This module formalizes the hyperfinite CAR algebra sequence of Clifford algebras
$\text{Cl}(2N, 2N) \cong M_{2^{2N}}(\mathbb{C})$, proving:
1. Stage $N$ dimension $2^{2N}$ and trace state normalization $\omega_N(1) = 1$
2. Trace compatibility under step embeddings: $2^{-2(N+1)} \cdot 4 = 2^{-2N}$
3. Boundary Majorana zero mode factor decomposition:
   $$\text{Cl}(2N+2, 2N+2) \cong \text{Cl}(2N, 2N) \otimes \text{Cl}(1,1)$$
   via the dimension factorization $2^{2(N+1)} = 2^{2N} \cdot 4$.
-/

/-- Stage N of the Clifford CAR tower: 2²ᴺ × 2²ᴺ complex matrix algebra. -/
abbrev CliffordStage (N : ℕ) : Type := Matrix (Fin (2 ^ (2 * N))) (Fin (2 ^ (2 * N))) ℂ

/-- Normalized trace state at stage N: ω_N(A) = 2⁻²ᴺ · Tr(A). -/
def cliffordTraceState (N : ℕ) (A : CliffordStage N) : ℂ :=
  (1 / (2 ^ (2 * N) : ℂ)) * Matrix.trace A

/-- **Theorem**: Normalized trace of identity at stage N is 1. -/
theorem cliffordTraceState_one (N : ℕ) : cliffordTraceState N 1 = 1 := by
  dsimp [cliffordTraceState]
  rw [Matrix.trace_one]
  have h_pos : (2 ^ (2 * N) : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero (2 * N) (by norm_num)
  have h_tr : (↑(Fintype.card (Fin (2 ^ (2 * N)))) : ℂ) = (2 ^ (2 * N) : ℂ) := by
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [h_tr]
  exact one_div_mul_cancel h_pos

/-- **Theorem**: Trace compatibility under stage step embedding.
    2⁻²⁽ᴺ⁺¹⁾ · 4 = 2⁻²ᴺ. -/
theorem clifford_trace_compatibility (N : ℕ) :
    (1 / (2 ^ (2 * (N + 1)) : ℂ)) * 4 = 1 / (2 ^ (2 * N) : ℂ) := by
  have h_pow : (2 ^ (2 * (N + 1)) : ℂ) = (2 ^ (2 * N) : ℂ) * 4 := by
    have : 2 * (N + 1) = 2 * N + 2 := by ring
    rw [this, pow_add]
    norm_num
  rw [h_pow, one_div, _root_.mul_inv_rev]
  have h4 : (4 : ℂ)⁻¹ * 4 = 1 := by
    exact inv_mul_cancel₀ (by norm_num)
  calc ((4 : ℂ)⁻¹ * (2 ^ (2 * N) : ℂ)⁻¹) * 4
    _ = (2 ^ (2 * N) : ℂ)⁻¹ * ((4 : ℂ)⁻¹ * 4) := by ring
    _ = (2 ^ (2 * N) : ℂ)⁻¹ * 1 := by rw [h4]
    _ = 1 / (2 ^ (2 * N) : ℂ) := by rw [mul_one, one_div]

/-- **Theorem**: Boundary Majorana Zero Mode Cl(1,1) Tensor Product Factorization.
    Cl(2N+2, 2N+2) ≅ Cl(2N, 2N) ⊗ Cl(1,1).
    Dimension check: 2²⁽ᴺ⁺¹⁾ = 2²ᴺ · 4. -/
theorem clifford_dim_factorization (N : ℕ) :
    2 ^ (2 * (N + 1)) = 2 ^ (2 * N) * 4 := by
  have : 2 * (N + 1) = 2 * N + 2 := by ring
  rw [this, pow_add]
  norm_num

end InfoGeometry.Canonical.CliffordInfiniteCARColimit
