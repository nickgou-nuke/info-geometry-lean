/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ChiralOperatorChargeFiltration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# Integer charge windows and colimit readouts

The free operator envelope has an honest integer word charge.  This owner
records the finite window `[-2,2]` without identifying its endpoints
cyclotomically, and connects compatible finite-stage readouts to the native
TensorTower colimit calculus over a general (not necessarily commutative)
operator ring `R`.
-/

namespace InfoGeometry.Algebra

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

def ChiralChargeWindow (N : ℕ) : Set (List ChiralGenerator) :=
  {w | -(N : ℤ) ≤ wordDegree w ∧ wordDegree w ≤ N}

/-- The words visible in the finite integer-charge window `[-N,N]`.

This is a carrier for the filtration only.  It is deliberately not declared
to be an algebra: concatenation can leave a fixed window.
-/
def ChiralChargeWindowCarrier (N : ℕ) :=
  {w : List ChiralGenerator // w ∈ ChiralChargeWindow N}

/-- Enlarging a charge window gives a canonical inclusion of carriers. -/
def chiralChargeWindowInclusion {N M : ℕ} (hNM : N ≤ M) :
    ChiralChargeWindowCarrier N → ChiralChargeWindowCarrier M :=
  fun w => ⟨w.1, by
    rcases w.2 with ⟨hlo, hhi⟩
    constructor <;> omega⟩

theorem chiralChargeWindowInclusion_val
    {N M : ℕ} (hNM : N ≤ M)
    (w : ChiralChargeWindowCarrier N) :
    (chiralChargeWindowInclusion hNM w).1 = w.1 ∧
    wordDegree (chiralChargeWindowInclusion hNM w).1 = wordDegree w.1 ∧
    (chiralChargeWindowInclusion hNM w).1 ∈ ChiralChargeWindow M := by
  rcases w.2 with ⟨hlo, hhi⟩
  constructor
  · rfl
  constructor
  · rfl
  · change -(M : ℤ) ≤ wordDegree w.1 ∧ wordDegree w.1 ≤ M
    constructor <;> omega

/-- The finite cyclotomic readout forgets the integer window and retains the
mod-three charge. -/
def chiralWindowCyclotomicReadout (N : ℕ) :
    ChiralChargeWindowCarrier N → ZMod 3 :=
  fun w => chiralWordCyclotomicCharge w.1

theorem chiralWindowCyclotomicReadout_inclusion
    {N M : ℕ} (hNM : N ≤ M)
    (w : ChiralChargeWindowCarrier N) :
    chiralWindowCyclotomicReadout M
        (chiralChargeWindowInclusion hNM w) =
    chiralWindowCyclotomicReadout N w := by
  change chiralWordCyclotomicCharge
      (chiralChargeWindowInclusion hNM w).1 = chiralWordCyclotomicCharge w.1
  rw [(chiralChargeWindowInclusion_val hNM w).1]

/-- Concatenation is compatible with the charge filtration when the windows
are added.  This is the finite-stage multiplicative law behind the colimit
readout; it does not identify the resulting words. -/
def chiralChargeWindowAppend
    {N M : ℕ}
    (u : ChiralChargeWindowCarrier N)
    (v : ChiralChargeWindowCarrier M) :
    ChiralChargeWindowCarrier (N + M) :=
  ⟨u.1 ++ v.1, by
    rcases u.2 with ⟨hu_lo, hu_hi⟩
    rcases v.2 with ⟨hv_lo, hv_hi⟩
    change -(N + M : ℤ) ≤ wordDegree (u.1 ++ v.1) ∧
      wordDegree (u.1 ++ v.1) ≤ N + M
    rw [wordDegree_append]
    constructor <;> omega⟩

theorem chiralChargeWindowAppend_val
    {N M : ℕ}
    (u : ChiralChargeWindowCarrier N)
    (v : ChiralChargeWindowCarrier M) :
    (chiralChargeWindowAppend u v).1 = u.1 ++ v.1 ∧
    wordDegree (chiralChargeWindowAppend u v).1 =
      wordDegree u.1 + wordDegree v.1 := by
  constructor
  · rfl
  · change wordDegree (u.1 ++ v.1) = _
    rw [wordDegree_append]

theorem chiralWindowCyclotomicReadout_append
    {N M : ℕ}
    (u : ChiralChargeWindowCarrier N)
    (v : ChiralChargeWindowCarrier M) :
    chiralWindowCyclotomicReadout (N + M)
        (chiralChargeWindowAppend u v) =
      chiralWindowCyclotomicReadout N u +
        chiralWindowCyclotomicReadout M v := by
  simp [chiralWindowCyclotomicReadout,
    chiralChargeWindowAppend, chiralWordCyclotomicCharge_append]

theorem chiralGenerator_mem_chargeWindow_one
    (g : ChiralGenerator) :
    [g] ∈ ChiralChargeWindow 1 := by
  cases g <;> simp [ChiralChargeWindow, wordDegree, generatorDegree]

theorem chiralPair_mem_chargeWindow_two
    (g h : ChiralGenerator) :
    [g, h] ∈ ChiralChargeWindow 2 := by
  cases g <;> cases h <;>
    simp [ChiralChargeWindow, wordDegree, generatorDegree]

theorem sPlus_pair_mem_chargeWindow_two (i j : Fin 3) :
    wordDegree [.sPlus i, .sPlus j] = 2 ∧
    [.sPlus i, .sPlus j] ∈ ChiralChargeWindow 2 := by
  have hdegree := sPlus_pair_has_charge_two i j
  refine ⟨hdegree, ?_⟩
  change -(2 : ℤ) ≤ wordDegree [.sPlus i, .sPlus j] ∧
    wordDegree [.sPlus i, .sPlus j] ≤ 2
  rw [hdegree]
  norm_num

theorem sMinus_pair_mem_chargeWindow_two (i j : Fin 3) :
    wordDegree [.sMinus i, .sMinus j] = -2 ∧
    [.sMinus i, .sMinus j] ∈ ChiralChargeWindow 2 := by
  have hdegree := sMinus_pair_has_charge_neg_two i j
  refine ⟨hdegree, ?_⟩
  change -(2 : ℤ) ≤ wordDegree [.sMinus i, .sMinus j] ∧
    wordDegree [.sMinus i, .sMinus j] ≤ 2
  rw [hdegree]
  norm_num

theorem sPlus_triple_not_mem_chargeWindow_two (i j k : Fin 3) :
    wordDegree [.sPlus i, .sPlus j, .sPlus k] = 3 ∧
    ¬ ([.sPlus i, .sPlus j, .sPlus k] ∈ ChiralChargeWindow 2) := by
  have hdegree := sPlus_triple_has_charge_three i j k
  refine ⟨hdegree, ?_⟩
  change ¬ (-(2 : ℤ) ≤ wordDegree [.sPlus i, .sPlus j, .sPlus k] ∧
    wordDegree [.sPlus i, .sPlus j, .sPlus k] ≤ 2)
  rw [hdegree]
  norm_num

theorem sMinus_triple_not_mem_chargeWindow_two (i j k : Fin 3) :
    wordDegree [.sMinus i, .sMinus j, .sMinus k] = -3 ∧
    ¬ ([.sMinus i, .sMinus j, .sMinus k] ∈ ChiralChargeWindow 2) := by
  have hdegree := sMinus_triple_has_charge_neg_three i j k
  refine ⟨hdegree, ?_⟩
  change ¬ (-(2 : ℤ) ≤ wordDegree [.sMinus i, .sMinus j, .sMinus k] ∧
    wordDegree [.sMinus i, .sMinus j, .sMinus k] ≤ 2)
  rw [hdegree]
  norm_num

/-- At cutoff two, signed pairs lie on the boundary and have distinct integer
degrees, while the corresponding triples lie outside the window. The
cyclotomic readout records the pair charges modulo three. -/
theorem chiralWindow_two_boundary_and_cyclotomic_classification
    (i j k : Fin 3) :
    wordDegree [.sPlus i, .sPlus j] = 2 ∧
    wordDegree [.sMinus i, .sMinus j] = -2 ∧
    wordDegree [.sPlus i, .sPlus j, .sPlus k] = 3 ∧
    wordDegree [.sMinus i, .sMinus j, .sMinus k] = -3 ∧
    [.sPlus i, .sPlus j] ∈ ChiralChargeWindow 2 ∧
    [.sMinus i, .sMinus j] ∈ ChiralChargeWindow 2 ∧
    ¬ ([.sPlus i, .sPlus j, .sPlus k] ∈ ChiralChargeWindow 2) ∧
    ¬ ([.sMinus i, .sMinus j, .sMinus k] ∈ ChiralChargeWindow 2) ∧
    chiralWordCyclotomicCharge [.sPlus i, .sPlus j] = (-1 : ZMod 3) ∧
    chiralWordCyclotomicCharge [.sMinus i, .sMinus j] = (1 : ZMod 3) := by
  have hp := sPlus_pair_mem_chargeWindow_two i j
  have hm := sMinus_pair_mem_chargeWindow_two i j
  have hpt := sPlus_triple_not_mem_chargeWindow_two i j k
  have hmt := sMinus_triple_not_mem_chargeWindow_two i j k
  rcases hp with ⟨hpdeg, hpmem⟩
  rcases hm with ⟨hmdeg, hmmem⟩
  rcases hpt with ⟨hptdeg, hptout⟩
  rcases hmt with ⟨hmtdeg, hmtout⟩
  refine ⟨hpdeg, hmdeg, hptdeg, hmtdeg, hpmem, hmmem, hptout, hmtout, ?_, ?_⟩
  · rw [chiralWordCyclotomicCharge, hpdeg]
    decide
  · rw [chiralWordCyclotomicCharge, hmdeg]
    decide

theorem chiralWindow_two_separates_integer_from_cyclotomic :
    chiralChargeModThree 2 = chiralChargeModThree (-1) ∧
    chiralChargeModThree (-2) = chiralChargeModThree 1 := by
  constructor
  · calc
      chiralChargeModThree 2 =
          chiralChargeModThree ((-1 : ℤ) + 3) := by
            exact congrArg chiralChargeModThree (by norm_num : (2 : ℤ) = -1 + 3)
      _ = chiralChargeModThree (-1) := chiralChargeModThree_period_three (-1)
  · calc
      chiralChargeModThree (-2) = chiralChargeModThree 1 :=
        (chiralChargeModThree_period_three (-2)).symm

end InfoGeometry.Algebra

namespace InfoGeometry.Topology

section ColimitReadout

variable {R : Type*} [Ring R]
variable (A : ℕ → Type*)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (iota : ∀ n, A n →ₗ[R] A (n + 1))
variable (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf]
variable (psi : ∀ n, A n →ₗ[R] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)

include psi_comm

theorem chiral_colimit_readout_comm
    (readout : A_inf →ₗ[R] R) (n m : ℕ) (x : A n) :
    readout (psi (n + m)
      (iota_seq A iota n m x)) =
      readout (psi n x) := by
  have h_compat :
      (psi (n + m)).comp (iota_seq A iota n m) = psi n :=
    psi_comp_iota_seq A iota A_inf psi psi_comm n m
  change readout ((psi (n + m)).comp (iota_seq A iota n m) x) = _
  rw [h_compat]

end ColimitReadout

end InfoGeometry.Topology
