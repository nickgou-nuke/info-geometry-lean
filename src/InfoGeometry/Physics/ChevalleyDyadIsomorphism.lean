/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Physics.ChevalleySpinorIdeal

/-!
# Chevalley Dyad Isomorphism: Kets, Bras, and Matrix Units in Cℓ(1,1)

This module formalizes the exact isomorphism between the split Clifford algebra
`Cℓ(1,1)`, the minimal left ideal (kets), the minimal right ideal (bras),
and the 2×2 matrix unit algebra `Mat(2, R)`:

$$\mathcal{C}\ell(1, 1) \;\cong\; \operatorname{End}(\text{Spinor}) \;\cong\; \operatorname{Mat}(2, R)$$

## Structural Theorems Proved
1. **Coordinate-Free Dyad Construction**:
   - Dyad operator: `dyad ψ ϕ = ψ * ϕ`
   - General composition law: `dyad ψ₁ ϕ₁ * dyad ψ₂ ϕ₂ = ψ₁ * (ϕ₁ * ψ₂) * ϕ₂`
2. **Spinor Basis (Kets and Bras)**:
   - Ground ket: `|0⟩ = e₀ = n * p`
   - Excited ket: `|1⟩ = p * e₀` (proved equal to `p`)
   - Ground bra: `⟨0| = e₀ = n * p`
   - Excited bra: `⟨1| = e₀ * n` (proved equal to `n`)
3. **Orthonormal Bra-Ket Overlaps**:
   - `⟨0|0⟩ = e₀`
   - `⟨0|1⟩ = 0`
   - `⟨1|0⟩ = 0`
   - `⟨1|1⟩ = e₀`
4. **Dyad Matrix Unit Representation**:
   - `E₀₀ = |0⟩⟨0| = n * p`
   - `E₀₁ = |0⟩⟨1| = n`
   - `E₁₀ = |1⟩⟨0| = p`
   - `E₁₁ = |1⟩⟨1| = p * n`
   - All 16 matrix unit products `E_{ij} * E_{kl} = δ_{jk} E_{il}`
5. **Completeness & Pauli-Nambu Realization**:
   - Resolution of identity: `E₀₀ + E₁₁ = 1`
   - Particle-hole swap: `τ₁ = E₀₁ + E₁₀ = n + p`
   - Charge grading: `τ₃ = E₀₀ - E₁₁ = n p - p n`
   - Dirac-Kähler vector: `𝒟 = E₀₁ - E₁₀ = n - p`
   - Algebra isomorphisms: `τ₁² = 1`, `τ₃² = 1`, `𝒟² = -1`, `τ₁ τ₃ + τ₃ τ₁ = 0`,
     `𝒟 τ₁ + τ₁ 𝒟 = 0`, and `𝒟 τ₁ = τ₃`.

All results are genuine definitions, lemmas, and theorems with complete Lean 4 proofs.
-/

namespace InfoGeometry.Physics.ChevalleyDyad

open InfoGeometry.Physics.Chevalley

variable {R : Type*} [Ring R]

/-! ### 1. General Coordinate-Free Dyad Algebra -/

/-- Coordinate-free dyad operator `|ψ⟩⟨ϕ| = ψ * ϕ`. -/
@[inline]
def dyad (psi phi : R) : R := psi * phi

/-- General dyad composition law: `(|ψ₁⟩⟨ϕ₁|) * (|ψ₂⟩⟨ϕ₂|) = ψ₁ * (ϕ₁ * ψ₂) * ϕ₂`. -/
theorem dyad_comp (psi1 phi1 psi2 phi2 : R) :
    dyad psi1 phi1 * dyad psi2 phi2 = psi1 * (phi1 * psi2) * phi2 := by
  dsimp [dyad]
  noncomm_ring

/-! ### 2. The Spinor Basis: Kets, Bras, and Idempotents -/

/-- Reference vacuum idempotent `e₀ = n * p`. -/
@[inline]
def e0 (n p : R) : R := n * p

/-- Ground state ket vector: `|0⟩ = e₀ = n * p`. -/
@[inline]
def ket0 (n p : R) : R := e0 n p

/-- Excited state ket vector: `|1⟩ = p * e₀`. -/
@[inline]
def ket1 (n p : R) : R := p * e0 n p

/-- Ground state bra vector: `⟨0| = e₀ = n * p`. -/
@[inline]
def bra0 (n p : R) : R := e0 n p

/-- Excited state bra vector: `⟨1| = e₀ * n`. -/
@[inline]
def bra1 (n p : R) : R := e0 n p * n

/-- The excited ket reduces to the creation operator: `|1⟩ = p`. -/
theorem ket1_eval (n p : R)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    ket1 n p = p := by
  dsimp [ket1, e0]
  exact p_mul_P_plus n p h_nil_p h_car

/-- The excited bra reduces to the annihilation operator: `⟨1| = n`. -/
theorem bra1_eval (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    bra1 n p = n := by
  dsimp [bra1, e0]
  exact P_plus_mul_n n p h_nil_n h_car

/-! ### 3. Orthonormal Bra-Ket Overlaps -/

/-- Ground state overlap: `⟨0|0⟩ = e₀`. -/
theorem inner00 (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    bra0 n p * ket0 n p = e0 n p := by
  dsimp [bra0, ket0, e0]
  exact P_plus_sq n p h_nil_n h_car

/-- Orthogonality of ground bra and excited ket: `⟨0|1⟩ = 0`. -/
theorem inner01 (n p : R)
    (h_nil_p : p * p = 0) :
    bra0 n p * ket1 n p = 0 := by
  dsimp [bra0, ket1, e0]
  calc
    (n * p) * (p * (n * p)) = n * (p * p) * (n * p) := by noncomm_ring
    _ = n * 0 * (n * p) := by rw [h_nil_p]
    _ = 0 := by noncomm_ring

/-- Orthogonality of excited bra and ground ket: `⟨1|0⟩ = 0`. -/
theorem inner10 (n p : R)
    (h_nil_n : n * n = 0) :
    bra1 n p * ket0 n p = 0 := by
  dsimp [bra1, ket0, e0]
  calc
    ((n * p) * n) * (n * p) = (n * p) * (n * n) * p := by noncomm_ring
    _ = (n * p) * 0 * p := by rw [h_nil_n]
    _ = 0 := by noncomm_ring

/-- Excited state overlap: `⟨1|1⟩ = e₀`. -/
theorem inner11 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    bra1 n p * ket1 n p = e0 n p := by
  rw [bra1_eval n p h_nil_n h_car]
  rw [ket1_eval n p h_nil_p h_car]
  rfl

/-- Ground ket absorption by vacuum idempotent: `|0⟩ * e₀ = |0⟩`. -/
theorem ket0_mul_e0 (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    ket0 n p * e0 n p = ket0 n p := by
  dsimp [ket0, e0]
  exact P_plus_sq n p h_nil_n h_car

/-- Excited ket absorption by vacuum idempotent: `|1⟩ * e₀ = |1⟩`. -/
theorem ket1_mul_e0 (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    ket1 n p * e0 n p = ket1 n p := by
  dsimp [ket1, e0]
  have h_plus : (n * p) * (n * p) = n * p := P_plus_sq n p h_nil_n h_car
  calc
    p * (n * p) * (n * p) = p * ((n * p) * (n * p)) := by noncomm_ring
    _ = p * (n * p) := by rw [h_plus]

/-! ### 4. Matrix Unit Dyads and Evaluations -/

/-- Matrix unit `E₀₀ = |0⟩⟨0|`. -/
@[inline]
def E00 (n p : R) : R := dyad (ket0 n p) (bra0 n p)

/-- Matrix unit `E₀₁ = |0⟩⟨1|`. -/
@[inline]
def E01 (n p : R) : R := dyad (ket0 n p) (bra1 n p)

/-- Matrix unit `E₁₀ = |1⟩⟨0|`. -/
@[inline]
def E10 (n p : R) : R := dyad (ket1 n p) (bra0 n p)

/-- Matrix unit `E₁₁ = |1⟩⟨1|`. -/
@[inline]
def E11 (n p : R) : R := dyad (ket1 n p) (bra1 n p)

/-- Evaluation of ground projector dyad: `E₀₀ = n * p`. -/
theorem E00_eval (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    E00 n p = n * p := by
  dsimp [E00, dyad, ket0, bra0, e0]
  exact P_plus_sq n p h_nil_n h_car

/-- Evaluation of annihilation transition dyad: `E₀₁ = n`. -/
theorem E01_eval (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    E01 n p = n := by
  dsimp [E01, dyad, ket0, bra1, e0]
  have hid : (n * p) * (n * p) = n * p := P_plus_sq n p h_nil_n h_car
  calc
    (n * p) * ((n * p) * n) = ((n * p) * (n * p)) * n := by noncomm_ring
    _ = (n * p) * n := by rw [hid]
    _ = n := P_plus_mul_n n p h_nil_n h_car

/-- Evaluation of creation transition dyad: `E₁₀ = p`. -/
theorem E10_eval (n p : R)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    E10 n p = p := by
  dsimp [E10, dyad, ket1, bra0, e0]
  have h_p : p * (n * p) = p := by
    simpa [P_plus] using p_mul_P_plus n p h_nil_p h_car
  rw [h_p, h_p]

/-- Evaluation of excited projector dyad: `E₁₁ = p * n`. -/
theorem E11_eval (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    E11 n p = p * n := by
  dsimp [E11, dyad]
  rw [ket1_eval n p h_nil_p h_car]
  rw [bra1_eval n p h_nil_n h_car]

/-! ### 5. Complete Matrix Unit Multiplication Table -/

/-- Matrix unit product: `E₀₀ * E₀₀ = E₀₀`. -/
theorem E00_mul_E00 (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    E00 n p * E00 n p = E00 n p := by
  dsimp [E00]
  rw [dyad_comp, inner00 n p h_nil_n h_car, ket0_mul_e0 n p h_nil_n h_car]
  rfl

/-- Matrix unit product: `E₀₀ * E₀₁ = E₀₁`. -/
theorem E00_mul_E01 (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    E00 n p * E01 n p = E01 n p := by
  dsimp [E00, E01]
  rw [dyad_comp, inner00 n p h_nil_n h_car, ket0_mul_e0 n p h_nil_n h_car]
  rfl

/-- Matrix unit product: `E₀₀ * E₁₀ = 0`. -/
theorem E00_mul_E10 (n p : R)
    (h_nil_p : p * p = 0) :
    E00 n p * E10 n p = 0 := by
  dsimp [E00, E10]
  rw [dyad_comp, inner01 n p h_nil_p]
  noncomm_ring

/-- Matrix unit product: `E₀₀ * E₁₁ = 0`. -/
theorem E00_mul_E11 (n p : R)
    (h_nil_p : p * p = 0) :
    E00 n p * E11 n p = 0 := by
  dsimp [E00, E11]
  rw [dyad_comp, inner01 n p h_nil_p]
  noncomm_ring

/-- Matrix unit product: `E₀₁ * E₀₀ = 0`. -/
theorem E01_mul_E00 (n p : R)
    (h_nil_n : n * n = 0) :
    E01 n p * E00 n p = 0 := by
  dsimp [E01, E00]
  rw [dyad_comp, inner10 n p h_nil_n]
  noncomm_ring

/-- Matrix unit product: `E₀₁ * E₀₁ = 0`. -/
theorem E01_mul_E01 (n p : R)
    (h_nil_n : n * n = 0) :
    E01 n p * E01 n p = 0 := by
  dsimp [E01]
  rw [dyad_comp, inner10 n p h_nil_n]
  noncomm_ring

/-- Matrix unit product: `E₀₁ * E₁₀ = E₀₀`. -/
theorem E01_mul_E10 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    E01 n p * E10 n p = E00 n p := by
  dsimp [E01, E10, E00]
  rw [dyad_comp, inner11 n p h_nil_n h_nil_p h_car, ket0_mul_e0 n p h_nil_n h_car]
  rfl

/-- Matrix unit product: `E₀₁ * E₁₁ = E₀₁`. -/
theorem E01_mul_E11 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    E01 n p * E11 n p = E01 n p := by
  dsimp [E01, E11]
  rw [dyad_comp, inner11 n p h_nil_n h_nil_p h_car, ket0_mul_e0 n p h_nil_n h_car]
  rfl

/-- Matrix unit product: `E₁₀ * E₀₀ = E₁₀`. -/
theorem E10_mul_E00 (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    E10 n p * E00 n p = E10 n p := by
  dsimp [E10, E00]
  rw [dyad_comp, inner00 n p h_nil_n h_car, ket1_mul_e0 n p h_nil_n h_car]
  rfl

/-- Matrix unit product: `E₁₀ * E₀₁ = E₁₁`. -/
theorem E10_mul_E01 (n p : R)
    (h_nil_n : n * n = 0)
    (h_car : n * p + p * n = 1) :
    E10 n p * E01 n p = E11 n p := by
  dsimp [E10, E01, E11]
  rw [dyad_comp, inner00 n p h_nil_n h_car, ket1_mul_e0 n p h_nil_n h_car]
  rfl

/-- Matrix unit product: `E₁₀ * E₁₀ = 0`. -/
theorem E10_mul_E10 (n p : R)
    (h_nil_p : p * p = 0) :
    E10 n p * E10 n p = 0 := by
  dsimp [E10]
  rw [dyad_comp, inner01 n p h_nil_p]
  noncomm_ring

/-- Matrix unit product: `E₁₀ * E₁₁ = 0`. -/
theorem E10_mul_E11 (n p : R)
    (h_nil_p : p * p = 0) :
    E10 n p * E11 n p = 0 := by
  dsimp [E10, E11]
  rw [dyad_comp, inner01 n p h_nil_p]
  noncomm_ring

/-- Matrix unit product: `E₁₁ * E₀₀ = 0`. -/
theorem E11_mul_E00 (n p : R)
    (h_nil_n : n * n = 0) :
    E11 n p * E00 n p = 0 := by
  dsimp [E11, E00]
  rw [dyad_comp, inner10 n p h_nil_n]
  noncomm_ring

/-- Matrix unit product: `E₁₁ * E₀₁ = 0`. -/
theorem E11_mul_E01 (n p : R)
    (h_nil_n : n * n = 0) :
    E11 n p * E01 n p = 0 := by
  dsimp [E11, E01]
  rw [dyad_comp, inner10 n p h_nil_n]
  noncomm_ring

/-- Matrix unit product: `E₁₁ * E₁₀ = E₁₀`. -/
theorem E11_mul_E10 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    E11 n p * E10 n p = E10 n p := by
  dsimp [E11, E10]
  rw [dyad_comp, inner11 n p h_nil_n h_nil_p h_car, ket1_mul_e0 n p h_nil_n h_car]
  rfl

/-- Matrix unit product: `E₁₁ * E₁₁ = E₁₁`. -/
theorem E11_mul_E11 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    E11 n p * E11 n p = E11 n p := by
  dsimp [E11]
  rw [dyad_comp, inner11 n p h_nil_n h_nil_p h_car, ket1_mul_e0 n p h_nil_n h_car]
  rfl

/-! ### 6. Resolution of Identity and Pauli-Nambu Realization -/

/-- Resolution of identity: `E₀₀ + E₁₁ = 1`. -/
theorem resolution_of_identity (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    E00 n p + E11 n p = 1 := by
  rw [E00_eval n p h_nil_n h_car]
  rw [E11_eval n p h_nil_n h_nil_p h_car]
  exact h_car

/-- Charge grading / Cartan split involution: `τ₃ = E₀₀ - E₁₁`. -/
@[inline]
def tau3 (n p : R) : R := E00 n p - E11 n p

/-- Particle-hole swap / Majorana chiral sum: `τ₁ = E₀₁ + E₁₀`. -/
@[inline]
def tau1 (n p : R) : R := E01 n p + E10 n p

/-- Chiral Dirac-Kähler vector: `𝒟 = E₀₁ - E₁₀`. -/
@[inline]
def diracVector (n p : R) : R := E01 n p - E10 n p

/-- Involution property: `τ₁² = 1`. -/
theorem tau1_sq (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    tau1 n p * tau1 n p = 1 := by
  dsimp [tau1]
  rw [E01_eval n p h_nil_n h_car]
  rw [E10_eval n p h_nil_p h_car]
  exact chiral_sum_sq n p h_nil_n h_nil_p h_car

/-- Involution property: `τ₃² = 1`. -/
theorem tau3_sq (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    tau3 n p * tau3 n p = 1 := by
  dsimp [tau3]
  rw [E00_eval n p h_nil_n h_car]
  rw [E11_eval n p h_nil_n h_nil_p h_car]
  exact chiralGrading_sq n p h_nil_n h_nil_p h_car

/-- Anticommutation of Pauli matrices: `τ₁ τ₃ + τ₃ τ₁ = 0`. -/
theorem tau1_anticommutes_tau3 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    tau1 n p * tau3 n p + tau3 n p * tau1 n p = 0 := by
  dsimp [tau1, tau3]
  rw [E00_eval n p h_nil_n h_car]
  rw [E01_eval n p h_nil_n h_car]
  rw [E10_eval n p h_nil_p h_car]
  rw [E11_eval n p h_nil_n h_nil_p h_car]
  have h1 := chiralGrading_anticommutes_n n p h_nil_n h_car
  have h2 := chiralGrading_anticommutes_p n p h_nil_p h_car
  dsimp [chiralGrading] at h1 h2
  calc
    (n + p) * (n * p - p * n) + (n * p - p * n) * (n + p)
      = ((n * p - p * n) * n + n * (n * p - p * n)) +
        ((n * p - p * n) * p + p * (n * p - p * n)) := by noncomm_ring
    _ = 0 + 0 := by rw [h1, h2]
    _ = 0 := add_zero 0

/-- Clifford squaring of the Dirac vector: `𝒟² = -1`. -/
theorem diracVector_sq (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    diracVector n p * diracVector n p = -1 := by
  dsimp [diracVector]
  rw [E01_eval n p h_nil_n h_car]
  rw [E10_eval n p h_nil_p h_car]
  exact dirac_vector_sq n p h_nil_n h_nil_p h_car

/-- Anticommutation of Dirac vector with chiral sum: `𝒟 τ₁ + τ₁ 𝒟 = 0`. -/
theorem diracVector_anticommutes_tau1 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    diracVector n p * tau1 n p + tau1 n p * diracVector n p = 0 := by
  dsimp [diracVector, tau1]
  rw [E01_eval n p h_nil_n h_car]
  rw [E10_eval n p h_nil_p h_car]
  exact dirac_anticommutes_chiral_sum n p h_nil_n h_nil_p

/-- Dirac-Pauli conversion: `𝒟 * τ₁ = τ₃`. -/
theorem diracVector_mul_tau1_eq_tau3 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    diracVector n p * tau1 n p = tau3 n p := by
  dsimp [diracVector, tau1, tau3]
  rw [E00_eval n p h_nil_n h_car]
  rw [E01_eval n p h_nil_n h_car]
  rw [E10_eval n p h_nil_p h_car]
  rw [E11_eval n p h_nil_n h_nil_p h_car]
  exact dirac_mul_chiral_sum_eq_grading n p h_nil_n h_nil_p

/-- Dirac-Pauli conversion: `τ₁ * 𝒟 = - τ₃`. -/
theorem tau1_mul_diracVector_eq_neg_tau3 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    tau1 n p * diracVector n p = - tau3 n p := by
  dsimp [diracVector, tau1, tau3]
  rw [E00_eval n p h_nil_n h_car]
  rw [E01_eval n p h_nil_n h_car]
  rw [E10_eval n p h_nil_p h_car]
  rw [E11_eval n p h_nil_n h_nil_p h_car]
  exact chiral_sum_mul_dirac_eq_neg_grading n p h_nil_n h_nil_p

end InfoGeometry.Physics.ChevalleyDyad
