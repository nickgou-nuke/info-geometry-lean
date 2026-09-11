import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge
import InfoGeometry.Meta.SocketTarget

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

belongs in a separate analytic witness once convergence and zeta APIs are
installed.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeSupertraceFinite

open InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge

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

/-! ## 6. Infinite zeta/supertrace witness socket -/

/--
Witness-gated infinite supersymmetric primon zeta calibration.

This is where the analytic identity

```text
sum mu(n) n^(-beta) = 1 / zeta(beta)
```

belongs.  It is not proved by the finite occupation skeleton.
-/
structure SupersymmetricPrimonZetaCalibration where
  /-- Inverse temperature domain, e.g. `1 < beta`. -/
  BetaAdmissible : ℝ → Prop
  /-- Infinite supertrace readout. -/
  supertrace : ℝ → ℝ
  /-- Zeta readout. -/
  zeta : ℝ → ℝ
  /-- Nonvanishing of zeta on the admissible domain. -/
  zeta_ne_zero :
    ∀ β : ℝ, BetaAdmissible β → zeta β ≠ 0
  /-- Analytic calibration law. -/
  supertrace_eq_inv_zeta :
    ∀ β : ℝ, BetaAdmissible β →
      supertrace β = 1 / zeta β

namespace SupersymmetricPrimonZetaCalibration

variable (C : SupersymmetricPrimonZetaCalibration)

/-- Re-export of the supplied infinite supertrace/zeta calibration. -/
theorem supertrace_eq_inv_zeta_of_admissible
    (β : ℝ)
    (hβ : C.BetaAdmissible β) :
    C.supertrace β = 1 / C.zeta β :=
  C.supertrace_eq_inv_zeta β hβ

end SupersymmetricPrimonZetaCalibration

end InfoGeometry.Arithmetic.PrimeSupertraceFinite
