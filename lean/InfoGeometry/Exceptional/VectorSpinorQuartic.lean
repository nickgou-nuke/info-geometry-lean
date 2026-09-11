import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Finset

/-!
# InfoGeometry.Exceptional.VectorSpinorQuartic

A finite associative vector--spinor quartic readout on the real coordinate space
`(Fin 2 → Fin 12 → ℝ) × (Fin 1 → Fin 32 → ℝ)`.

This file proves only the algebraic scaling laws of the displayed coordinate
polynomial.  It does **not** prove that this polynomial is the genuine
`E₇(₇)` Freudenthal invariant, a black-hole entropy theorem, a holographic area
law, or a qubit-entanglement classification theorem.
-/

namespace InfoGeometry.Exceptional.VectorSpinorQuartic

/--
A 56-coordinate real vector--spinor packet: `2 * 12 = 24` vector coordinates
and `1 * 32 = 32` spinor coordinates.
-/
structure VectorSpinorState56 where
  vectorCharge : Matrix (Fin 2) (Fin 12) ℝ
  spinorCharge : Matrix (Fin 1) (Fin 32) ℝ

/-- Uniform scalar scaling of the vector--spinor packet. -/
def smul56 (c : ℝ) (S : VectorSpinorState56) : VectorSpinorState56 where
  vectorCharge := c • S.vectorCharge
  spinorCharge := c • S.spinorCharge

/-- Split-signature coordinate signs with six positive and six negative entries. -/
def eta66 (a : Fin 12) : ℝ :=
  if a.val < 6 then 1 else -1

/-- Quadratic readout of the `(2,12)` vector component. -/
def vectorQuadratic (V : Matrix (Fin 2) (Fin 12) ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ a : Fin 12, eta66 a * (V i a) ^ 2

/-- Quadratic readout of the `(1,32)` spinor component. -/
def spinorQuadratic (Ψ : Matrix (Fin 1) (Fin 32) ℝ) : ℝ :=
  ∑ a : Fin 32, (Ψ 0 a) ^ 2

/-- The finite associative quartic readout `Qᵥ(V)^2 + Qₛ(Ψ)^2`. -/
def vectorSpinorQuartic (S : VectorSpinorState56) : ℝ :=
  (vectorQuadratic S.vectorCharge) ^ 2 + (spinorQuadratic S.spinorCharge) ^ 2

/-- The vector quadratic scales with degree two. -/
theorem vectorQuadratic_smul (c : ℝ) (V : Matrix (Fin 2) (Fin 12) ℝ) :
    vectorQuadratic (c • V) = c ^ 2 * vectorQuadratic V := by
  unfold vectorQuadratic
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ i : Fin 2, ∑ a : Fin 12, eta66 a * (c * V i a) ^ 2)
        = ∑ i : Fin 2, ∑ a : Fin 12, c ^ 2 * (eta66 a * (V i a) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = c ^ 2 * ∑ i : Fin 2, ∑ a : Fin 12, eta66 a * (V i a) ^ 2 := by
          rw [Finset.mul_sum]
          congr 1
          ext i
          rw [Finset.mul_sum]

/-- The spinor quadratic scales with degree two. -/
theorem spinorQuadratic_smul (c : ℝ) (Ψ : Matrix (Fin 1) (Fin 32) ℝ) :
    spinorQuadratic (c • Ψ) = c ^ 2 * spinorQuadratic Ψ := by
  unfold spinorQuadratic
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ a : Fin 32, (c * Ψ 0 a) ^ 2) = ∑ a : Fin 32, c ^ 2 * (Ψ 0 a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = c ^ 2 * ∑ a : Fin 32, (Ψ 0 a) ^ 2 := by
      rw [Finset.mul_sum]

/-- The finite vector--spinor quartic readout scales with degree four. -/
theorem vectorSpinorQuartic_smul (c : ℝ) (S : VectorSpinorState56) :
    vectorSpinorQuartic (smul56 c S) = c ^ 4 * vectorSpinorQuartic S := by
  unfold vectorSpinorQuartic smul56
  rw [vectorQuadratic_smul, spinorQuadratic_smul]
  ring

/-- The finite vector--spinor quartic readout is nonnegative. -/
theorem vectorSpinorQuartic_nonneg (S : VectorSpinorState56) :
    0 ≤ vectorSpinorQuartic S := by
  unfold vectorSpinorQuartic
  positivity

/-- Square-root scaling for a fourth-power factor. -/
lemma sqrt_c4_mul (c x : ℝ) :
    Real.sqrt (c ^ 4 * x) = c ^ 2 * Real.sqrt x := by
  have hc2 : 0 ≤ c ^ 2 := by positivity
  have h_mul : c ^ 4 * x = (c ^ 2) ^ 2 * x := by ring
  rw [h_mul]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (c ^ 2) ^ 2)]
  rw [Real.sqrt_sq hc2]

/-- Algebraic square-root readout associated to `vectorSpinorQuartic`. -/
noncomputable def sqrtQuarticReadout (S : VectorSpinorState56) : ℝ :=
  Real.pi * Real.sqrt (vectorSpinorQuartic S)

/-- The algebraic square-root readout scales with degree two. -/
theorem sqrtQuarticReadout_smul (c : ℝ) (S : VectorSpinorState56) :
    sqrtQuarticReadout (smul56 c S) = c ^ 2 * sqrtQuarticReadout S := by
  unfold sqrtQuarticReadout
  rw [vectorSpinorQuartic_smul]
  rw [sqrt_c4_mul]
  ring

/-- Vector-sector finite Dirac--Schwinger--Zwanziger-style skew pairing. -/
def vectorDSZPairing (V₁ V₂ : Matrix (Fin 2) (Fin 12) ℝ) : ℝ :=
  ∑ a : Fin 12, eta66 a * (V₁ 0 a * V₂ 1 a - V₁ 1 a * V₂ 0 a)

/-- Spinor-sector finite skew pairing, pairing the two 16-coordinate halves. -/
def spinorDSZPairing (Ψ₁ Ψ₂ : Matrix (Fin 1) (Fin 32) ℝ) : ℝ :=
  ∑ a : Fin 16,
    let idx1 : Fin 32 := ⟨a.val, by linarith [a.isLt]⟩
    let idx2 : Fin 32 := ⟨a.val + 16, by linarith [a.isLt]⟩
    Ψ₁ 0 idx1 * Ψ₂ 0 idx2 - Ψ₁ 0 idx2 * Ψ₂ 0 idx1

/-- Combined finite vector--spinor skew pairing. -/
def vectorSpinorDSZPairing (S₁ S₂ : VectorSpinorState56) : ℝ :=
  vectorDSZPairing S₁.vectorCharge S₂.vectorCharge +
    spinorDSZPairing S₁.spinorCharge S₂.spinorCharge

/-- The vector-sector finite DSZ pairing is skew-symmetric. -/
theorem vectorDSZPairing_skew (V₁ V₂ : Matrix (Fin 2) (Fin 12) ℝ) :
    vectorDSZPairing V₁ V₂ = -vectorDSZPairing V₂ V₁ := by
  unfold vectorDSZPairing
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The spinor-sector finite DSZ pairing is skew-symmetric. -/
theorem spinorDSZPairing_skew (Ψ₁ Ψ₂ : Matrix (Fin 1) (Fin 32) ℝ) :
    spinorDSZPairing Ψ₁ Ψ₂ = -spinorDSZPairing Ψ₂ Ψ₁ := by
  unfold spinorDSZPairing
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The combined finite vector--spinor DSZ pairing is skew-symmetric. -/
theorem vectorSpinorDSZPairing_skew (S₁ S₂ : VectorSpinorState56) :
    vectorSpinorDSZPairing S₁ S₂ = -vectorSpinorDSZPairing S₂ S₁ := by
  unfold vectorSpinorDSZPairing
  rw [vectorDSZPairing_skew, spinorDSZPairing_skew]
  ring

/-!
Closed finite algebra in this file:

* `vectorQuadratic_smul`
* `spinorQuadratic_smul`
* `vectorSpinorQuartic_smul`
* `vectorSpinorQuartic_nonneg`
* `sqrtQuarticReadout_smul`
* `vectorSpinorDSZPairing_skew`

Open closure debt, deliberately not encoded as declarations:

* identification with the genuine `E₇(₇)` invariant;
* representation-theoretic equivalence to a Freudenthal construction;
* black-hole/horizon entropy and holographic area-law interpretations;
* multipartite-qubit entanglement classification.
-/

end InfoGeometry.Exceptional.VectorSpinorQuartic
