import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge
import InfoGeometry.Canonical.PrimeGasPartitions

/-!
# InfoGeometry.Canonical.CantorCliffordMellinPrimeGasBridge

Bridge:

```text
binary profile / Cantor cylinder
  -> finite Clifford/Fock occupation word
  -> prime-profile energy
  -> finite Mellin kernel
  -> bosonic / fermionic / parity-supertrace prime-gas channels
```

This file does not prove RH, analytic continuation, or infinite Euler-product
claims.  Zero-location statements must be supplied by a separate spectral-zero
witness.

The theorem-owned finite identity remains in
`PrimitiveBinarySuperZetaBridge.lean`:

```text
E(epsilon) = sum epsilon_i log p_i = log n(epsilon),
```

and the trace-channel separation remains owned by `PrimeGasPartitions.lean`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCliffordMellinPrimeGasBridge

set_option linter.dupNamespace false

open scoped BigOperators

open InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge
open InfoGeometry.Canonical.PrimeGasPartitions
open InfoGeometry.Canonical.FormalPrimeRootSystem

/-! ## 1. Binary profile layer -/

/-- A finite binary occupation profile of length `k`. -/
abbrev BinaryProfile (k : ℕ) : Type :=
  Fin k → Bool

/-- Boolean occupation as a real number. -/
def occ (b : Bool) : ℝ :=
  if b then 1 else 0

/-! ## 2. Finite prime profile and energy -/

/-- Finite prime-scale packet.  `p i` is the prime assigned to bit position `i`. -/
structure FinitePrimeProfile (k : ℕ) where
  /-- Prime label for each bit position. -/
  p : Fin k → ℕ
  /-- Prime certificate for each label. -/
  prime_law : ∀ i, Nat.Prime (p i)
  /-- Positive real base certificate for Mellin powers. -/
  p_pos : ∀ i, 0 < (p i : ℝ)

/-- Profile energy `E(epsilon) = sum epsilon_i log p_i`. -/
def profileEnergy
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (ε : BinaryProfile k) : ℝ :=
  Finset.univ.sum
    (fun i : Fin k =>
      occ (ε i) * Real.log ((P.p i : ℕ) : ℝ))

theorem occ_nonnegative (b : Bool) : 0 ≤ occ b := by
  cases b <;> simp [occ]

theorem profileEnergy_nonnegative
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (ε : BinaryProfile k) :
    0 ≤ profileEnergy P ε := by
  unfold profileEnergy
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (occ_nonnegative (ε i))
  apply Real.log_nonneg
  exact_mod_cast (P.prime_law i).one_le

/-- Squarefree integer attached to a binary prime profile: `n(epsilon) = prod p_i^epsilon_i`. -/
def profileNat
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (ε : BinaryProfile k) : ℕ :=
  Finset.univ.prod
    (fun i : Fin k =>
      if ε i then P.p i else 1)

theorem profileNat_cast
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (ε : BinaryProfile k) :
    (profileNat P ε : ℝ) =
      Finset.univ.prod (fun i : Fin k =>
        if ε i then (P.p i : ℝ) else 1) := by
  unfold profileNat
  simp

theorem profileEnergy_eq_log_profileNat
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (ε : BinaryProfile k) :
    profileEnergy P ε = Real.log (profileNat P ε : ℝ) := by
  unfold profileEnergy
  rw [profileNat_cast P ε, Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    unfold occ
    by_cases h : ε i
    · simp [h]
    · simp [h]
  · intro i hi
    by_cases h : ε i
    · simp [h, Nat.ne_of_gt (P.prime_law i).pos]
    · simp [h]

/-- Finite Mellin kernel `exp(-beta * E(epsilon))`. -/
def mellinKernel
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (β : ℝ)
    (ε : BinaryProfile k) : ℝ :=
  Real.exp (-β * profileEnergy P ε)

theorem mellinKernel_pos
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (β : ℝ)
    (ε : BinaryProfile k) :
    0 < mellinKernel P β ε := by
  unfold mellinKernel
  exact Real.exp_pos _

/--
Witness that the finite Mellin kernel equals the squarefree integer weight.

The concrete theorem is already owned upstream by the finite prime-bit lattice
lane.  This structure lets the composed bridge use the equality without
reproving it here.
-/
def MellinProfileLaw
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (β : ℝ)
    (integerWeight : BinaryProfile k → ℝ) : Prop :=
  ∀ ε : BinaryProfile k,
    mellinKernel P β ε = integerWeight ε

/-! ## 3. Finite prime-gas partition channels -/

/-- Bosonic finite prime-gas partition `Z_B = prod_i (1 - p_i^(-beta))^(-1)`. -/
noncomputable def bosonicPartition
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (β : ℝ) : ℝ :=
  Finset.univ.prod
    (fun i : Fin k =>
      (1 - Real.rpow ((P.p i : ℕ) : ℝ) (-β))⁻¹)

/-- Ordinary fermionic finite prime-gas trace `Z_F = prod_i (1 + p_i^(-beta))`. -/
noncomputable def fermionicTracePartition
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (β : ℝ) : ℝ :=
  Finset.univ.prod
    (fun i : Fin k =>
      1 + Real.rpow ((P.p i : ℕ) : ℝ) (-β))

/--
Parity supertrace finite prime-gas channel `Z_super = prod_i (1 - p_i^(-beta))`.

This is the finite inverse-zeta / Weyl-denominator analogue.
-/
noncomputable def paritySupertracePartition
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (β : ℝ) : ℝ :=
  Finset.univ.prod
    (fun i : Fin k =>
      1 - Real.rpow ((P.p i : ℕ) : ℝ) (-β))

/-- Finite channel separation as a direct proposition over three readouts. -/
def FiniteZetaChannelSeparation
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (β bosonChannel fermionTraceChannel paritySupertraceChannel : ℝ) : Prop :=
  bosonChannel = bosonicPartition P β ∧
  fermionTraceChannel = fermionicTracePartition P β ∧
  paritySupertraceChannel = paritySupertracePartition P β

theorem bosonChannel_eq_bosonicPartition
    {k : ℕ}
    {P : FinitePrimeProfile k}
    {β bosonChannel fermionTraceChannel paritySupertraceChannel : ℝ}
    (h : FiniteZetaChannelSeparation P β bosonChannel
      fermionTraceChannel paritySupertraceChannel) :
    bosonChannel = bosonicPartition P β :=
  h.1

theorem fermionTraceChannel_eq_fermionicTracePartition
    {k : ℕ}
    {P : FinitePrimeProfile k}
    {β bosonChannel fermionTraceChannel paritySupertraceChannel : ℝ}
    (h : FiniteZetaChannelSeparation P β bosonChannel
      fermionTraceChannel paritySupertraceChannel) :
    fermionTraceChannel = fermionicTracePartition P β :=
  h.2.1

theorem paritySupertraceChannel_eq_paritySupertracePartition
    {k : ℕ}
    {P : FinitePrimeProfile k}
    {β bosonChannel fermionTraceChannel paritySupertraceChannel : ℝ}
    (h : FiniteZetaChannelSeparation P β bosonChannel
      fermionTraceChannel paritySupertraceChannel) :
    paritySupertraceChannel = paritySupertracePartition P β :=
  h.2.2

/-! ## 4. Modular / Mellin shift -/

def mellinShift (β s : ℝ) : ℝ :=
  β + s

def MellinShiftLaw
    {k : ℕ}
    (P : FinitePrimeProfile k)
    (β s : ℝ) : Prop :=
  ∀ ε : BinaryProfile k,
    mellinKernel P (mellinShift β s) ε =
      mellinKernel P β ε *
        Real.exp (-s * profileEnergy P ε)

theorem mellinShiftLaw_proved
    {k : ℕ} (P : FinitePrimeProfile k) (β s : ℝ) :
    MellinShiftLaw P β s := by
  intro ε
  unfold mellinKernel mellinShift
  rw [show -(β + s) * profileEnergy P ε =
      (-β * profileEnergy P ε) + (-s * profileEnergy P ε) by ring]
  rw [Real.exp_add]

/-! ## 5. Analytic continuation predicates -/

def IsAnalyticContinuation
    (L continuation : ℂ → ℂ) (domain : Set ℂ) : Prop :=
  IsOpen domain ∧
  (∀ z, z ∈ domain → continuation z = L z) ∧
  DifferentiableOn ℂ continuation domain

def IsZeroSet
    (continuation : ℂ → ℂ) (zeroLocation : Set ℂ) : Prop :=
  ∀ z, z ∈ zeroLocation ↔ continuation z = 0

end InfoGeometry.Canonical.CantorCliffordMellinPrimeGasBridge
