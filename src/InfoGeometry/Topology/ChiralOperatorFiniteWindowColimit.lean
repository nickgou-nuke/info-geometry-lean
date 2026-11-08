import InfoGeometry.Algebra.ChiralOperatorChargeFiltration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# Integer charge windows and colimit readouts

The free operator envelope has an honest integer word charge.  This owner
records the finite window `[-2,2]` without identifying its endpoints
cyclotomically, and connects compatible finite-stage readouts to the native
TensorTower colimit calculus.
-/

namespace InfoGeometry.Algebra

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

def ChiralChargeWindow (N : ℕ) (w : List ChiralGenerator) : Prop :=
  -(N : ℤ) ≤ wordDegree w ∧ wordDegree w ≤ N

/-- The words visible in the finite integer-charge window `[-N,N]`.

This is a carrier for the filtration only.  It is deliberately not declared
to be an algebra: concatenation can leave a fixed window.
-/
def ChiralChargeWindowCarrier (N : ℕ) :=
  {w : List ChiralGenerator // ChiralChargeWindow N w}

/-- Enlarging a charge window gives a canonical inclusion of carriers. -/
def chiralChargeWindowInclusion {N M : ℕ} (hNM : N ≤ M) :
    ChiralChargeWindowCarrier N → ChiralChargeWindowCarrier M :=
  fun w => ⟨w.1, by
    rcases w.2 with ⟨hlo, hhi⟩
    constructor <;> omega⟩

@[simp] theorem chiralChargeWindowInclusion_val
    {N M : ℕ} (hNM : N ≤ M)
    (w : ChiralChargeWindowCarrier N) :
    (chiralChargeWindowInclusion hNM w).1 = w.1 :=
  rfl

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
      chiralWindowCyclotomicReadout N w :=
  rfl

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

@[simp] theorem chiralChargeWindowAppend_val
    {N M : ℕ}
    (u : ChiralChargeWindowCarrier N)
    (v : ChiralChargeWindowCarrier M) :
    (chiralChargeWindowAppend u v).1 = u.1 ++ v.1 :=
  rfl

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
    ChiralChargeWindow 1 [g] := by
  cases g <;> simp [ChiralChargeWindow, wordDegree, generatorDegree]

theorem chiralPair_mem_chargeWindow_two
    (g h : ChiralGenerator) :
    ChiralChargeWindow 2 [g, h] := by
  cases g <;> cases h <;>
    simp [ChiralChargeWindow, wordDegree, generatorDegree]

theorem sPlus_pair_mem_chargeWindow_two (i j : Fin 3) :
    ChiralChargeWindow 2
      [.sPlus i, .sPlus j] := by
  simp [ChiralChargeWindow, wordDegree, generatorDegree]

theorem sMinus_pair_mem_chargeWindow_two (i j : Fin 3) :
    ChiralChargeWindow 2
      [.sMinus i, .sMinus j] := by
  simp [ChiralChargeWindow, wordDegree, generatorDegree]

theorem sPlus_triple_not_mem_chargeWindow_two (i j k : Fin 3) :
    ¬ ChiralChargeWindow 2
      [.sPlus i, .sPlus j, .sPlus k] := by
  simp [ChiralChargeWindow, wordDegree, generatorDegree]

theorem sMinus_triple_not_mem_chargeWindow_two (i j k : Fin 3) :
    ¬ ChiralChargeWindow 2
      [.sMinus i, .sMinus j, .sMinus k] := by
  simp [ChiralChargeWindow, wordDegree, generatorDegree]

theorem chiralWindow_two_separates_integer_from_cyclotomic :
    chiralChargeModThree 2 = chiralChargeModThree (-1) ∧
    chiralChargeModThree (-2) = chiralChargeModThree 1 := by
  exact ⟨chiralChargeModThree_pos_two_eq_neg_one,
    chiralChargeModThree_neg_two_eq_pos_one⟩

end InfoGeometry.Algebra

namespace InfoGeometry.Topology

section ColimitReadout

variable {R : Type*} [CommRing R]
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
  exact colimit_trace_comm
    A iota A_inf psi psi_comm readout n m x

end ColimitReadout

end InfoGeometry.Topology
