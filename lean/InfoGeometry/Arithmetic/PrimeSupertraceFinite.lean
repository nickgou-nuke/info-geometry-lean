import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge
import InfoGeometry.Arithmetic.IndexTheorem
import InfoGeometry.GrandCanonical.Core

/-!
# InfoGeometry.Arithmetic.PrimeSupertraceFinite

Finite supersymmetric primon gas / prime supertrace owner surface.

This module formalizes the constructive finite skeleton:

* a finite set of prime-labelled modes;
* occupation states `ι -> Bool`;
* fermion number = number of occupied modes;
* parity sign = `+1` for even occupation and `-1` for odd occupation;
* energy `H(x) = sum_i occupied E_i`;
* finite partition and finite superpartition.
* a finite prime-bit exterior channel whose product-form supertrace is the
  finite Euler denominator.

It does not claim an infinite Euler product, analytic continuation, RH, or a
zeta zero theorem.  The infinite identity

```text
sum mu(n) n^(-beta) = 1 / zeta(beta)
```

belongs in a separate analytic property once convergence and zeta APIs are
installed.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeSupertraceFinite

open InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge
open InfoGeometry.Arithmetic.IndexTheorem

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## 1. Finite occupation space -/

/-- A finite occupation state over mode labels `ι`. -/
abbrev Occupation (ι : Type*) :=
  ι → Bool

namespace Occupation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite set of occupied modes. -/
def occupied
    (x : Occupation ι) : Finset ι :=
  Finset.univ.filter fun i => x i

/-- Fermion number: number of occupied modes. -/
def fermionNumber
    (x : Occupation ι) : ℕ :=
  (occupied x).card

/-- Occupation parity: even or odd fermion number. -/
def isEven
    (x : Occupation ι) : Prop :=
  fermionNumber x % 2 = 0

/-- Parity sign `(-1)^F`, valued in `ℝ`. -/
def paritySign
    (x : Occupation ι) : ℝ :=
  if fermionNumber x % 2 = 0 then 1 else -1

omit [DecidableEq ι] in
theorem paritySign_eq_neg_one_pow_fermionNumber
    (x : Occupation ι) :
    paritySign x = (-1 : ℝ) ^ fermionNumber x := by
  unfold paritySign
  by_cases h : fermionNumber x % 2 = 0
  · rw [if_pos h]
    exact (Even.neg_one_pow (Nat.even_iff.mpr h)).symm
  · rw [if_neg h]
    exact (Odd.neg_one_pow
      (Nat.not_even_iff_odd.mp (fun he => h (Nat.even_iff.mp he)))).symm

/-- Empty occupation state. -/
def empty : Occupation ι :=
  fun _ => false

/-- Fully occupied state. -/
def full : Occupation ι :=
  fun _ => true

omit [DecidableEq ι] in
@[simp]
theorem occupied_empty :
    occupied (empty : Occupation ι) = ∅ := by
  ext i
  simp [occupied, empty]

omit [DecidableEq ι] in
@[simp]
theorem fermionNumber_empty :
    fermionNumber (empty : Occupation ι) = 0 := by
  simp [fermionNumber]

omit [DecidableEq ι] in
@[simp]
theorem paritySign_empty :
    paritySign (empty : Occupation ι) = 1 := by
  simp [paritySign]

/-- Toggle one occupation bit. -/
def toggle
    (k : ι)
    (x : Occupation ι) : Occupation ι :=
  fun i => if i = k then ! x i else x i

omit [Fintype ι] in
/-- Toggling the same bit twice is identity. -/
theorem toggle_involutive
    (k : ι)
    (x : Occupation ι) :
    toggle k (toggle k x) = x := by
  funext i
  by_cases h : i = k
  · simp [toggle, h]
  · simp [toggle, h]

end Occupation

/-! ## 2. Finite Hamiltonian and partition functions -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Finite energy readout attached to each mode.

For a finite prime mode model, use `modeEnergy i = log (p_i)`.
-/
abbrev ModeEnergy (ι : Type*) :=
  ι → ℝ

/-- Energy of an occupation state: `H(x) = sum occupied E_i`. -/
def occupationEnergy
    (E : ModeEnergy ι)
    (x : Occupation ι) : ℝ :=
  Finset.sum (Occupation.occupied x) E

/-- Gibbs weight of an occupation state. -/
def occupationGibbsWeight
    (E : ModeEnergy ι)
    (β : ℝ)
    (x : Occupation ι) : ℝ :=
  Real.exp (-β * occupationEnergy E x)

/-- Finite occupation partition over all finite occupations. -/
def finitePartition
    (E : ModeEnergy ι)
    (β : ℝ) : ℝ :=
  Finset.sum Finset.univ (fun x : Occupation ι =>
    occupationGibbsWeight E β x)

/-- The occupation partition is the canonical finite grand-canonical
partition for the same energy readout. -/
theorem finitePartition_eq_grandCanonical_partition
    (E : ModeEnergy ι) (β : ℝ) :
    finitePartition E β =
      InfoGeometry.GrandCanonical.partition
        (occupationEnergy E) β := by
  rfl

/-- Occupation-state weights become canonical normalized weights after the
partition factor is restored. -/
theorem occupationGibbsWeight_eq_partition_mul_grandCanonical_gibbsWeight
    (E : ModeEnergy ι) (β : ℝ) (x : Occupation ι) :
    occupationGibbsWeight E β x =
      InfoGeometry.GrandCanonical.partition
        (occupationEnergy E) β *
      InfoGeometry.GrandCanonical.gibbsWeight
        (occupationEnergy E) β x := by
  unfold occupationGibbsWeight InfoGeometry.GrandCanonical.gibbsWeight
  change Real.exp (-β * occupationEnergy E x) =
    InfoGeometry.GrandCanonical.partition (occupationEnergy E) β *
      (Real.exp (-β * occupationEnergy E x) /
        InfoGeometry.GrandCanonical.partition (occupationEnergy E) β)
  field_simp [InfoGeometry.GrandCanonical.partition_pos
    (occupationEnergy E) β]
  exact (div_self (InfoGeometry.GrandCanonical.partition_pos
    (occupationEnergy E) β).ne').symm

/-- Finite superpartition / Witten-index-style readout. -/
def finiteSuperPartition
    (E : ModeEnergy ι)
    (β : ℝ) : ℝ :=
  Finset.sum Finset.univ (fun x : Occupation ι =>
    Occupation.paritySign x * occupationGibbsWeight E β x)

omit [DecidableEq ι] in
@[simp]
theorem occupationEnergy_empty
    (E : ModeEnergy ι) :
    occupationEnergy E (Occupation.empty : Occupation ι) = 0 := by
  simp [occupationEnergy]

omit [DecidableEq ι] in
@[simp]
theorem occupationGibbsWeight_empty
    (E : ModeEnergy ι)
    (β : ℝ) :
    occupationGibbsWeight E β (Occupation.empty : Occupation ι) = 1 := by
  simp [occupationGibbsWeight]

omit [DecidableEq ι] in
/-- Gibbs weights are nonnegative. -/
theorem occupationGibbsWeight_nonneg
    (E : ModeEnergy ι)
    (β : ℝ)
    (x : Occupation ι) :
    0 ≤ occupationGibbsWeight E β x := by
  unfold occupationGibbsWeight
  positivity

omit [DecidableEq ι] in
lemma occupationGibbsWeight_pos
    (E : ModeEnergy ι) (β : ℝ) (x : Occupation ι) :
    0 < occupationGibbsWeight E β x := by
  unfold occupationGibbsWeight
  exact Real.exp_pos _

/-- The finite partition is nonnegative. -/
theorem finitePartition_nonneg
    (E : ModeEnergy ι)
    (β : ℝ) :
    0 ≤ finitePartition E β := by
  unfold finitePartition
  refine Finset.sum_nonneg ?_
  intro x _hx
  exact occupationGibbsWeight_nonneg E β x

/--
The finite partition contains the empty-state contribution `1`, hence is at
least `1`.
-/
theorem one_le_finitePartition
    (E : ModeEnergy ι)
    (β : ℝ) :
    1 ≤ finitePartition E β := by
  classical
  simpa [finitePartition] using
    (Finset.single_le_sum
      (s := (Finset.univ : Finset (Occupation ι)))
      (a := Occupation.empty)
      (f := fun x : Occupation ι => occupationGibbsWeight E β x)
      (fun x _hx => occupationGibbsWeight_nonneg E β x)
      (Finset.mem_univ (Occupation.empty : Occupation ι)))

lemma finitePartition_pos
    (E : ModeEnergy ι) (β : ℝ) :
    0 < finitePartition E β := by
  exact lt_of_lt_of_le zero_lt_one (one_le_finitePartition E β)

lemma finitePartition_ne_zero
    (E : ModeEnergy ι) (β : ℝ) :
    finitePartition E β ≠ 0 :=
  (finitePartition_pos E β).ne'

/-- The finite Gibbs partition factors into the two local occupation choices
    at each mode. -/
theorem finitePartition_eq_product_one_add_exp_neg_mul
    (E : ModeEnergy ι)
    (β : ℝ) :
    finitePartition E β =
      ∏ i : ι, (1 + Real.exp (-β * E i)) := by
  classical
  unfold finitePartition occupationGibbsWeight occupationEnergy
  have hfactor (x : Occupation ι) :
      Real.exp (-β * (Finset.sum (Occupation.occupied x) E)) =
        ∏ i : ι, if x i then Real.exp (-β * E i) else 1 := by
    have henergy : Finset.sum (Occupation.occupied x) E =
        ∑ i : ι, if x i then E i else 0 := by
      unfold Occupation.occupied
      rw [Finset.sum_filter]
    have hscale : -β * (∑ i : ι, if x i then E i else 0) =
        ∑ i : ι, (-β) * (if x i then E i else 0) := by
      exact Finset.mul_sum (Finset.univ : Finset ι)
        (fun i => if x i then E i else 0) (-β)
    rw [henergy, hscale, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : x i <;> simp [h]
  rw [show (∑ x : Occupation ι,
      Real.exp (-β * ∑ i ∈ Occupation.occupied x, E i)) =
      ∑ x : Occupation ι, ∏ i : ι, if x i then Real.exp (-β * E i) else 1 by
        apply Finset.sum_congr rfl
        intro x hx
        exact hfactor x]
  have hlocal (i : ι) :
      ((∑ b : Bool, if b then Real.exp (-β * E i) else 1) : ℝ) =
        1 + Real.exp (-β * E i) := by
    simp
    ring
  rw [← Finset.prod_congr rfl (fun i _hi => hlocal i)]
  rw [← Finset.sum_prod_piFinset]
  rw [Fintype.piFinset_univ]

/-! ## 3. Even/odd split of the finite supertrace -/

/-- Even occupation states. -/
noncomputable def evenOccupations : Finset (Occupation ι) := by
  classical
  exact Finset.univ.filter fun x => Occupation.isEven x

/-- Odd occupation states. -/
noncomputable def oddOccupations : Finset (Occupation ι) := by
  classical
  exact Finset.univ.filter fun x => ¬ Occupation.isEven x

/-- Even-sector finite partition. -/
def evenPartition
    (E : ModeEnergy ι)
    (β : ℝ) : ℝ :=
  Finset.sum evenOccupations (fun x =>
    occupationGibbsWeight E β x)

/-- Odd-sector finite partition. -/
def oddPartition
    (E : ModeEnergy ι)
    (β : ℝ) : ℝ :=
  Finset.sum oddOccupations (fun x =>
    occupationGibbsWeight E β x)

lemma evenPartition_nonneg
    (E : ModeEnergy ι) (β : ℝ) :
    0 ≤ evenPartition E β := by
  unfold evenPartition
  exact Finset.sum_nonneg (fun x _hx => occupationGibbsWeight_nonneg E β x)

lemma oddPartition_nonneg
    (E : ModeEnergy ι) (β : ℝ) :
    0 ≤ oddPartition E β := by
  unfold oddPartition
  exact Finset.sum_nonneg (fun x _hx => occupationGibbsWeight_nonneg E β x)

/-- The finite superpartition is the even partition minus the odd partition. -/
theorem finiteSuperPartition_eq_even_sub_odd
    (E : ModeEnergy ι)
    (β : ℝ) :
    finiteSuperPartition E β =
      evenPartition E β - oddPartition E β := by
  classical
  unfold finiteSuperPartition evenPartition oddPartition evenOccupations oddOccupations
  have hEven :
      Finset.sum (Finset.univ.filter fun x : Occupation ι => Occupation.isEven x)
        (fun x => Occupation.paritySign x * occupationGibbsWeight E β x)
      =
      Finset.sum (Finset.univ.filter fun x : Occupation ι => Occupation.isEven x)
        (fun x => occupationGibbsWeight E β x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxEven : Occupation.isEven x := (Finset.mem_filter.mp hx).2
    have hxEven' : Occupation.fermionNumber x % 2 = 0 := by
      simpa [Occupation.isEven] using hxEven
    simp [Occupation.paritySign, hxEven']
  have hOdd :
      Finset.sum (Finset.univ.filter fun x : Occupation ι => ¬ Occupation.isEven x)
        (fun x => Occupation.paritySign x * occupationGibbsWeight E β x)
      =
      - Finset.sum (Finset.univ.filter fun x : Occupation ι => ¬ Occupation.isEven x)
        (fun x => occupationGibbsWeight E β x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxOdd : ¬ Occupation.isEven x := (Finset.mem_filter.mp hx).2
    have hxOdd' : Occupation.fermionNumber x % 2 ≠ 0 := by
      simpa [Occupation.isEven] using hxOdd
    simp [Occupation.paritySign, hxOdd']
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Occupation ι)))
      (p := fun x => Occupation.isEven x)
      (f := fun x =>
        Occupation.paritySign x * occupationGibbsWeight E β x)
  calc
    (∑ x : Occupation ι,
        Occupation.paritySign x * occupationGibbsWeight E β x)
        =
      Finset.sum (Finset.univ.filter fun x : Occupation ι => Occupation.isEven x)
          (fun x => Occupation.paritySign x * occupationGibbsWeight E β x)
        +
        Finset.sum (Finset.univ.filter fun x : Occupation ι => ¬ Occupation.isEven x)
          (fun x => Occupation.paritySign x * occupationGibbsWeight E β x) := by
        simpa using hsplit.symm
    _ =
      Finset.sum (Finset.univ.filter fun x : Occupation ι => Occupation.isEven x)
          (fun x => occupationGibbsWeight E β x)
        -
        Finset.sum (Finset.univ.filter fun x : Occupation ι => ¬ Occupation.isEven x)
          (fun x => occupationGibbsWeight E β x) := by
        rw [hEven, hOdd]
        ring

/-- The generic finite occupation superpartition is the product of its local
    signed mode factors.  This is the finite algebraic bridge between the
    occupation-state readout and the exterior/Euler denominator readout. -/
theorem finiteSuperPartition_eq_product_one_sub_exp_neg_mul
    (E : ModeEnergy ι)
    (β : ℝ) :
    finiteSuperPartition E β =
      ∏ i : ι, (1 - Real.exp (-β * E i)) := by
  classical
  unfold finiteSuperPartition occupationGibbsWeight occupationEnergy
  have hfactor (x : Occupation ι) :
      Occupation.paritySign x *
          Real.exp (-β * (Finset.sum (Occupation.occupied x) E)) =
        ∏ i : ι, if x i then -Real.exp (-β * E i) else 1 := by
    have hparity : Occupation.paritySign x =
        ∏ i : ι, if x i then (-1 : ℝ) else 1 := by
      unfold Occupation.paritySign Occupation.fermionNumber Occupation.occupied
      rw [← Finset.prod_filter]
      simp only [Finset.prod_const]
      change (if (Finset.univ.filter (fun i => x i = true)).card % 2 = 0 then 1 else -1) =
        (-1 : ℝ) ^ (Finset.univ.filter (fun i => x i = true)).card
      by_cases h : (Finset.univ.filter (fun i => x i = true)).card % 2 = 0
      · rw [if_pos h]
        exact (Even.neg_one_pow (Nat.even_iff.mpr h)).symm
      · rw [if_neg h]
        exact (Odd.neg_one_pow
          (Nat.not_even_iff_odd.mp (fun he => h (Nat.even_iff.mp he)))).symm
    have henergy : Finset.sum (Occupation.occupied x) E =
        ∑ i : ι, if x i then E i else 0 := by
      unfold Occupation.occupied
      rw [Finset.sum_filter]
    have hscale : -β * (∑ i : ι, if x i then E i else 0) =
        ∑ i : ι, (-β) * (if x i then E i else 0) := by
      exact Finset.mul_sum (Finset.univ : Finset ι)
        (fun i => if x i then E i else 0) (-β)
    rw [hparity, henergy, hscale, Real.exp_sum]
    calc
      (∏ i : ι, if x i then (-1 : ℝ) else 1) *
          (∏ i : ι, Real.exp (-β * (if x i then E i else 0))) =
          ∏ i : ι,
            (if x i then (-1 : ℝ) else 1) *
              Real.exp (-β * (if x i then E i else 0)) := by
                rw [Finset.prod_mul_distrib]
      _ = ∏ i : ι, if x i then -Real.exp (-β * E i) else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases h : x i <;> simp [h]
  rw [show (∑ x : Occupation ι,
      Occupation.paritySign x * Real.exp (-β * ∑ i ∈ Occupation.occupied x, E i)) =
      ∑ x : Occupation ι, ∏ i : ι, if x i then -Real.exp (-β * E i) else 1 by
        apply Finset.sum_congr rfl
        intro x hx
        exact hfactor x]
  have hlocal (i : ι) :
      ((∑ b : Bool, if b then -Real.exp (-β * E i) else 1) : ℝ) =
        1 - Real.exp (-β * E i) := by
    simp
    ring
  rw [← Finset.prod_congr rfl (fun i _hi => hlocal i)]
  rw [← Finset.sum_prod_piFinset]
  rw [Fintype.piFinset_univ]

/-- At zero inverse temperature, the signed Gibbs readout is the finite
    parity/Witten sum. -/
theorem finiteSuperPartition_zero_eq_paritySum
    (E : ModeEnergy ι) :
    finiteSuperPartition E 0 =
      ∑ x : Occupation ι, Occupation.paritySign x := by
  simp [finiteSuperPartition, occupationGibbsWeight]

/-- Character form of the zero-parameter finite Witten readout. -/
theorem finiteSuperPartition_zero_eq_fermionCharacterSum
    (E : ModeEnergy ι) :
    finiteSuperPartition E 0 =
      ∑ x : Occupation ι, (-1 : ℝ) ^ Occupation.fermionNumber x := by
  rw [finiteSuperPartition_zero_eq_paritySum]
  apply Finset.sum_congr rfl
  intro x hx
  exact Occupation.paritySign_eq_neg_one_pow_fermionNumber x

/-- A nonempty finite mode register has vanishing zero-parameter Witten
    superpartition. -/
theorem finiteSuperPartition_zero_eq_zero
    [Nonempty ι]
    (E : ModeEnergy ι) :
    finiteSuperPartition E 0 = 0 := by
  rw [finiteSuperPartition_eq_product_one_sub_exp_neg_mul]
  simp

/-! ## 4. Generic finite occupation index -/

/-
The occupation supertrace has a genuine finite Euler-index realization.  The
complex below is the zero-differential two-term complex whose graded carriers
are the even and odd occupation sectors.  This is deliberately an algebraic
finite statement; it does not identify a divisor or analytic residue index.
-/

abbrev evenOccupationCarrier (ι : Type*) [Fintype ι] [DecidableEq ι] : Type _ :=
  {x : Occupation ι // x ∈ evenOccupations} → ℚ

abbrev oddOccupationCarrier (ι : Type*) [Fintype ι] [DecidableEq ι] : Type _ :=
  {x : Occupation ι // x ∈ oddOccupations} → ℚ

def occupationParityComplex (ι : Type*) [Fintype ι] [DecidableEq ι] :
    FiniteTwoTermComplex
      (K := ℚ)
      (Vp := evenOccupationCarrier (ι := ι))
      (Vm := oddOccupationCarrier (ι := ι)) :=
  zeroFiniteTwoTermComplex

theorem occupationParitySum_eq_even_card_sub_odd_card :
    (∑ x : Occupation ι,
      if Occupation.isEven x then (1 : ℤ) else -1) =
      (evenOccupations (ι := ι)).card - (oddOccupations (ι := ι)).card := by
  classical
  have hterm (x : Occupation ι) :
      (if Occupation.isEven x then (1 : ℤ) else -1) =
        (if Occupation.isEven x then (1 : ℤ) else 0) -
          (if ¬ Occupation.isEven x then (1 : ℤ) else 0) := by
    by_cases h : Occupation.isEven x <;> simp [h]
  calc
    (∑ x : Occupation ι,
        if Occupation.isEven x then (1 : ℤ) else -1) =
        ∑ x : Occupation ι,
          ((if Occupation.isEven x then (1 : ℤ) else 0) -
            (if ¬ Occupation.isEven x then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hterm x
    _ = (evenOccupations (ι := ι)).card -
          (oddOccupations (ι := ι)).card := by
      rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      simp [evenOccupations, oddOccupations]

theorem finiteKernelIndex_occupationParity :
    finiteKernelIndex (occupationParityComplex (ι := ι)) =
      ∑ x : Occupation ι,
        if Occupation.isEven x then (1 : ℤ) else -1 := by
  change finiteKernelIndex (zeroFiniteTwoTermComplex
    (K := ℚ)
    (Vp := evenOccupationCarrier (ι := ι))
    (Vm := oddOccupationCarrier (ι := ι))) = _
  rw [finiteKernelIndex_zero]
  simp only [evenOccupationCarrier, oddOccupationCarrier,
    Module.finrank_fintype_fun_eq_card]
  rw [occupationParitySum_eq_even_card_sub_odd_card]
  simp only [Fintype.card_coe]

theorem finiteSuperPartition_zero_eq_real_kernelIndex
    (E : ModeEnergy ι) :
    (finiteKernelIndex (occupationParityComplex (ι := ι)) : ℝ) =
      finiteSuperPartition E 0 := by
  rw [finiteKernelIndex_occupationParity,
    finiteSuperPartition_zero_eq_paritySum]
  norm_cast
  simp [Occupation.paritySign, Occupation.isEven]

/-! ## 4. Prime-labelled finite models -/

/-- A finite prime-labelled mode model. -/
structure FinitePrimeModeModel
    (ι : Type*) [Fintype ι] where
  /-- Natural-number label of each mode. -/
  label : ι → ℕ
  /-- Every mode label is prime. -/
  label_prime :
    ∀ i : ι, Nat.Prime (label i)

/-- Energy of a finite prime mode: `E_i = log p_i`. -/
def FinitePrimeModeModel.energy
    {ι : Type*} [Fintype ι]
    (M : FinitePrimeModeModel ι) :
    ModeEnergy ι :=
  fun i => Real.log (M.label i : ℝ)

/-- Finite primon partition for a finite prime-mode model. -/
def FinitePrimeModeModel.partition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FinitePrimeModeModel ι)
    (β : ℝ) : ℝ :=
  finitePartition M.energy β

/-- Finite supersymmetric primon superpartition. -/
def FinitePrimeModeModel.superPartition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FinitePrimeModeModel ι)
    (β : ℝ) : ℝ :=
  finiteSuperPartition M.energy β

/-- Finite primon partition is nonnegative. -/
theorem FinitePrimeModeModel.partition_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FinitePrimeModeModel ι)
    (β : ℝ) :
    0 ≤ M.partition β :=
  finitePartition_nonneg M.energy β

lemma FinitePrimeModeModel.partition_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FinitePrimeModeModel ι) (β : ℝ) :
    0 < M.partition β := by
  exact finitePartition_pos M.energy β

/-! ## 5. Finite prime-bit exterior denominator -/

/--
The finite prime-bit lattice owner from `PrimitiveBinarySuperZetaBridge`.

This file does not duplicate the finite bit-energy/Mellin theorem; it reuses
that owner surface and adds the finite exterior supertrace denominator.
-/
abbrev FinitePrimeBitLattice :=
  InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge.FinitePrimeBitLattice

namespace FinitePrimeBitLattice

variable (P : FinitePrimeBitLattice)

/-- Fermion number of a finite prime-bit profile. -/
def bitFermionNumber
    (ε : P.Profile) : ℕ :=
  Occupation.fermionNumber ε

/-- Fermion parity sign of a finite prime-bit profile, valued in `ℝ`. -/
def bitFermionParity
    (ε : P.Profile) : ℝ :=
  Occupation.paritySign ε

/-- Local Mellin/Gibbs weight of a prime mode. -/
def localPrimeWeight
    (β : ℝ)
    (i : P.Index) : ℝ :=
  Real.exp (-β * Real.log (P.prime i : ℝ))

/--
Product-form finite exterior supertrace.

Each occupied prime mode contributes the signed local factor `-p_i^{-β}`;
each unoccupied mode contributes `1`.
-/
def finiteExteriorProductSupertrace
    (β : ℝ) : ℝ :=
  ∑ ε : P.Profile,
    ∏ i : P.Index, if ε i then -P.localPrimeWeight β i else 1

/-- Finite Euler/Weyl denominator over the prime-bit lattice. -/
def finiteExteriorEulerDenominator
    (β : ℝ) : ℝ :=
  ∏ i : P.Index, (1 - P.localPrimeWeight β i)

/--
The finite exterior prime supertrace equals the finite Euler denominator.

This is the constructive finite Witten-index theorem:

`Σ_ε Π_i signedWeight(i, ε_i) = Π_i (1 - exp(-β log p_i))`.

The infinite inverse-zeta statement is deliberately not asserted here.
-/
theorem finiteExteriorProductSupertrace_eq_denominator
    (β : ℝ) :
    P.finiteExteriorProductSupertrace β =
      P.finiteExteriorEulerDenominator β := by
  classical
  unfold finiteExteriorProductSupertrace finiteExteriorEulerDenominator localPrimeWeight
  have hlocal :
      ∀ i : P.Index,
        ((∑ b : Bool,
          if b then -Real.exp (-β * Real.log (P.prime i : ℝ)) else 1) : ℝ)
          =
        1 - Real.exp (-β * Real.log (P.prime i : ℝ)) := by
    intro i
    simp
    ring
  rw [← Finset.prod_congr rfl (fun i _hi => hlocal i)]
  rw [← Finset.sum_prod_piFinset]
  rw [Fintype.piFinset_univ]

/-- The occupation-state superpartition at prime-log energies agrees with the
    existing finite prime-bit exterior denominator. -/
theorem finiteSuperPartition_primeEnergy_eq_exteriorEulerDenominator
    (P : FinitePrimeBitLattice)
    (β : ℝ) :
    finiteSuperPartition
        (fun i : P.Index => Real.log (P.prime i : ℝ)) β =
      P.finiteExteriorEulerDenominator β := by
  rw [finiteSuperPartition_eq_product_one_sub_exp_neg_mul]
  rfl

/-- The occupation superpartition and the exterior product supertrace are the
    same finite signed Gibbs readout.  Both remain finite carriers; no
    infinite inverse-zeta or analytic trace identity is inferred. -/
theorem finiteSuperPartition_primeEnergy_eq_exteriorProductSupertrace
    (P : FinitePrimeBitLattice)
    (β : ℝ) :
    finiteSuperPartition
        (fun i : P.Index => Real.log (P.prime i : ℝ)) β =
      P.finiteExteriorProductSupertrace β := by
  rw [finiteSuperPartition_primeEnergy_eq_exteriorEulerDenominator]
  exact (P.finiteExteriorProductSupertrace_eq_denominator β).symm

/--
The finite prime-bit supertrace has one coherent readout: the occupation
superpartition, the exterior-product supertrace, and the local Euler
denominator agree exactly at every finite inverse-temperature stage.

This is a finite algebraic packet. The infinite inverse-zeta comparison is
kept separate in `SupersymmetricPrimonZetaCalibration`.
-/
theorem finitePrimeBitSupertrace_readout_packet
    (P : FinitePrimeBitLattice) (β : ℝ) :
    P.finiteExteriorProductSupertrace β =
        P.finiteExteriorEulerDenominator β ∧
      finiteSuperPartition
          (fun i : P.Index => Real.log (P.prime i : ℝ)) β =
        P.finiteExteriorProductSupertrace β ∧
      finiteSuperPartition
          (fun i : P.Index => Real.log (P.prime i : ℝ)) β =
        P.finiteExteriorEulerDenominator β := by
  refine ⟨P.finiteExteriorProductSupertrace_eq_denominator β,
    finiteSuperPartition_primeEnergy_eq_exteriorProductSupertrace P β,
    finiteSuperPartition_primeEnergy_eq_exteriorEulerDenominator P β⟩

/-- The zero-parameter exterior supertrace is the finite prime-bit parity sum. -/
theorem finiteExteriorProductSupertrace_zero_eq_bitParitySum
    (P : FinitePrimeBitLattice) :
    P.finiteExteriorProductSupertrace 0 =
      ∑ ε : P.Profile, P.bitFermionParity ε := by
  rw [finiteExteriorProductSupertrace_eq_denominator]
  rw [← finiteSuperPartition_primeEnergy_eq_exteriorEulerDenominator]
  simpa [FinitePrimeBitLattice.bitFermionParity] using
    (finiteSuperPartition_zero_eq_paritySum
      (fun i : P.Index => Real.log (P.prime i : ℝ)))

/-- A nonempty finite prime register has vanishing zero-parameter exterior
    supertrace. -/
theorem finiteExteriorProductSupertrace_zero_eq_zero
    (P : FinitePrimeBitLattice)
    [Nonempty P.Index] :
    P.finiteExteriorProductSupertrace 0 = 0 := by
  rw [finiteExteriorProductSupertrace_eq_denominator]
  unfold finiteExteriorEulerDenominator localPrimeWeight
  have hcard : Fintype.card P.Index ≠ 0 := Fintype.card_ne_zero
  simp [hcard]

/--
Re-export of the finite bit-energy identity from the primitive binary bridge:

`E(ε) = log n(ε)`.
-/
theorem bitEnergy_eq_log_bitInteger
    (ε : P.Profile) :
    P.bitEnergy ε = Real.log (P.bitInteger ε : ℝ) :=
  PrimitiveBinarySuperZetaBridge.FinitePrimeBitLattice.bitEnergy_eq_log_bitInteger P ε

/--
Re-export of the primitive Mellin/Gibbs identity from the primitive binary
bridge, gated by the nontrivial readout condition `1 < n(ε)`.
-/
theorem primitiveMellinKernel_bitInteger_eq_exp_neg_mul_bitEnergy
    (ε : P.Profile) (β : ℝ)
    (hε : 1 < P.bitInteger ε) :
    primitiveMellinKernel (P.bitInteger ε) β =
      Real.exp (-β * P.bitEnergy ε) :=
  by
    exact
      InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge.FinitePrimeBitLattice.primitiveMellinKernel_bitInteger_eq_exp_neg_mul_bitEnergy
        P ε β hε

end FinitePrimeBitLattice


end InfoGeometry.Arithmetic.PrimeSupertraceFinite
