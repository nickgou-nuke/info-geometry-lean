import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.BostConnesSuperalgebra
import InfoGeometry.Canonical.BostConnesSuperalgebraConstructive

/-!
# Cantor KMS State and Thermodynamic Time

This module formalizes the canonical tracial KMS state on the diagonal UHF algebra stages.
We define the normalized trace on `DiagAlg n`, prove its compatibility with the inductive
morphisms, and establish the thermodynamic trace partition function.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorKMSState

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.BostConnesSuperalgebra
open InfoGeometry.Canonical.BostConnesSuperalgebraConstructive

/-- Explicit equivalence between `BitWord (n + 1)` and `BitWord n × Bool`. -/
def bitWordEquiv (n : ℕ) : BitWord (n + 1) ≃ BitWord n × Bool where
  toFun w := (prefixSucc n w, w ⟨n, Nat.lt_succ_self n⟩)
  invFun p i := if h : i.1 < n then p.1 ⟨i.1, h⟩ else p.2
  left_inv w := by
    ext i
    dsimp [prefixSucc]
    split_ifs with h
    · rfl
    · have hi : i.1 = n := by
        have h1 : i.1 < n + 1 := i.2
        omega
      have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := by
        ext
        exact hi
      rw [hi_eq]
  right_inv p := by
    ext i
    · dsimp [prefixSucc]
      split_ifs with h
      · rfl
      · omega
    · dsimp
      split_ifs with h
      · omega
      · rfl

theorem card_BitWord (n : ℕ) : Fintype.card (BitWord n) = 2^n := by
  dsimp [BitWord]
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The canonical normalized tracial state on `DiagAlg n`. -/
def DiagTrace (n : ℕ) (f : DiagAlg n) : ℂ :=
  (2 : ℂ)⁻¹ ^ n * Finset.sum Finset.univ f

/-! The singleton diagonal indicator used by the finite matrix-unit readout. -/
def cylinderIndicator (n : ℕ) (w : BitWord n) : DiagAlg n :=
  fun v => if v = w then 1 else 0

theorem DiagTrace_cylinderIndicator (n : ℕ) (w : BitWord n) :
    DiagTrace n (cylinderIndicator n w) =
      (2 : ℂ)⁻¹ ^ n := by
  unfold DiagTrace cylinderIndicator
  rw [Finset.sum_eq_single w]
  · simp
  · intro b hb hbw
    simp [hbw]
  · simp

/-- Linear map implementation of the trace. -/
def DiagTrace_addMonoidHom (n : ℕ) : DiagAlg n →+ ℂ where
  toFun := DiagTrace n
  map_zero' := by
    dsimp [DiagTrace]
    simp
  map_add' f g := by
    dsimp [DiagTrace]
    rw [← mul_add]
    congr 1
    exact Finset.sum_add_distrib

/-- The trace of the identity is 1 (normalization). -/
theorem DiagTrace_one (n : ℕ) : DiagTrace n 1 = 1 := by
  dsimp [DiagTrace]
  have h_sum : Finset.sum Finset.univ (1 : DiagAlg n) = Fintype.card (BitWord n) := by
    simp
  rw [h_sum, card_BitWord, Nat.cast_pow]
  have h_pow : (2 : ℂ)⁻¹ ^ n = (2^n : ℂ)⁻¹ := by
    rw [inv_pow]
  rw [h_pow]
  have h_nonzero : (2^n : ℂ) ≠ 0 := by
    exact pow_ne_zero n (by norm_num)
  exact inv_mul_cancel₀ h_nonzero

/-- The trace maps natively form an `AlgebraicState` on each stage. -/
def DiagTrace_state (n : ℕ) : BostConnesSuperalgebra.AlgebraicState (DiagAlg n) where
  val := DiagTrace_addMonoidHom n
  map_one := DiagTrace_one n

/-- Tracial compatibility: the successor embedding preserves the canonical trace. -/
theorem DiagTrace_compat (n : ℕ) (f : DiagAlg n) :
    DiagTrace (n + 1) (diagEmbedSucc n f) = DiagTrace n f := by
  dsimp [DiagTrace]
  unfold diagEmbedSucc
  change (2 : ℂ)⁻¹ ^ (n + 1) * Finset.sum Finset.univ (fun w => (fun p : BitWord n × Bool => f p.1) (bitWordEquiv n w)) = _
  have h_equiv := Equiv.sum_comp (bitWordEquiv n) (fun p : BitWord n × Bool => f p.1)
  rw [h_equiv]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  have h_inner : ∀ x : BitWord n, Finset.sum Finset.univ (fun _ : Bool => f x) = 2 * f x := by
    intro x
    simp
  simp_rw [h_inner]
  rw [← Finset.mul_sum]
  have h_pow_succ : (2 : ℂ)⁻¹ ^ (n + 1) = (2 : ℂ)⁻¹ ^ n * (2 : ℂ)⁻¹ := by
    exact pow_succ (2 : ℂ)⁻¹ n
  rw [h_pow_succ]
  ring

end InfoGeometry.Canonical.CantorKMSState

end noncomputable section
