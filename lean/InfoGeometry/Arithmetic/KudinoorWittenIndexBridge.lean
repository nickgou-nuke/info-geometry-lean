import Mathlib.Tactic
import InfoGeometry.Arithmetic.IndexTheorem

/-!
# Kudinoor supersymmetry/Witten-index bridge, finite owner surface

This module records the finite theorem-backed fragment of the exposition
"Supersymmetry and the Witten Index" (Arjun Kudinoor, 2023):

* a finite graded spectrum has a boson count and a fermion count at each level;
* nonzero levels are explicitly paired by the property `boson = fermion`;
* zero levels carry weight `1`;
* therefore the weighted supertrace collapses to the zero-energy Witten index;
* two such weights give the same supertrace under the same hypotheses.

#### BUCKET 1: CLOSED FINITE THEOREMS
All theorem statements below are finite algebraic identities over `Int`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The supertrace collapse requires explicit hypotheses:
`hzero` for zero-level weight normalization and `hpair` for nonzero
boson/fermion pairing.

#### BUCKET 3: OPEN CLOSURE DEBT
No Hilbert-space analysis, self-adjointness, heat-kernel theorem,
Atiyah-Singer index theorem, nonlinear sigma model, Dirac operator geometry,
or continuum Witten-index theorem is proved here.
-/

namespace InfoGeometry.Arithmetic.KudinoorWittenIndexBridge

open scoped BigOperators
open InfoGeometry.Arithmetic.IndexTheorem

set_option linter.unusedSectionVars false

variable {ι : Type*} [DecidableEq ι]

/-- Boson-minus-fermion count at one finite energy level. -/
def levelSuperdimension (boson fermion : ι → Nat) (i : ι) : Int :=
  (boson i : Int) - (fermion i : Int)

/-- Finite Witten index: the signed dimension of the zero-energy sector. -/
def finiteWittenIndex
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) : Int :=
  ∑ i ∈ levels.filter zero, levelSuperdimension boson fermion i

/-! ## Finite kernel realization of the zero-level index -/

/-- Rational carrier with one basis vector for every zero-level boson state. -/
abbrev zeroLevelBosonCarrier
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson : ι → Nat) : Type :=
  Fin (∑ i ∈ levels.filter zero, boson i) → ℚ

/-- Rational carrier with one basis vector for every zero-level fermion state. -/
abbrev zeroLevelFermionCarrier
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (fermion : ι → Nat) : Type :=
  Fin (∑ i ∈ levels.filter zero, fermion i) → ℚ

/-- The explicit zero-differential complex carried by the zero-energy modes. -/
def zeroLevelParityComplex
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) :
    FiniteTwoTermComplex
      (K := ℚ)
      (Vp := zeroLevelBosonCarrier levels zero boson)
      (Vm := zeroLevelFermionCarrier levels zero fermion) :=
  zeroFiniteTwoTermComplex

/-- The genuine finite kernel index equals the zero-level Witten index. -/
theorem finiteKernelIndex_zeroLevel_eq_finiteWittenIndex
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) :
    finiteKernelIndex (zeroLevelParityComplex levels zero boson fermion) =
      finiteWittenIndex levels zero boson fermion := by
  unfold zeroLevelParityComplex
  rw [finiteKernelIndex_zero]
  simp only [zeroLevelBosonCarrier, zeroLevelFermionCarrier,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  push_cast
  simp [finiteWittenIndex, levelSuperdimension, Finset.sum_sub_distrib]

/--
An explicit finite order-to-kernel correspondence identifies the genuine
zero-level kernel index with the signed divisor charge.  The correspondence
is an input: no analytic residue theorem or infinite spectral identification
is hidden in this finite bridge.
-/
theorem finiteKernelIndex_eq_finiteDivisorIndex_of_order_correspondence
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) (order : ι → Int)
    (horder : ∀ i ∈ levels.filter zero,
      order i = levelSuperdimension boson fermion i) :
    finiteKernelIndex (zeroLevelParityComplex levels zero boson fermion) =
      finiteDivisorIndex (levels.filter zero) order := by
  rw [finiteKernelIndex_zeroLevel_eq_finiteWittenIndex]
  unfold finiteWittenIndex finiteDivisorIndex
  apply Finset.sum_congr rfl
  intro i hi
  exact (horder i hi).symm

/-- Finite weighted supertrace over a supplied level weight. -/
def finiteWeightedSupertrace
    (levels : Finset ι) (boson fermion : ι → Nat) (weight : ι → Int) : Int :=
  ∑ i ∈ levels, levelSuperdimension boson fermion i * weight i

/--
Finite Kudinoor/Witten-index collapse.

If all zero levels have weight `1`, and every nonzero level is paired
boson-for-fermion, then the weighted supertrace is exactly the zero-sector
Witten index.
-/
theorem finiteWeightedSupertrace_eq_finiteWittenIndex
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) (weight : ι → Int)
    (hzero : ∀ i ∈ levels, zero i → weight i = 1)
    (hpair : ∀ i ∈ levels, ¬ zero i → boson i = fermion i) :
    finiteWeightedSupertrace levels boson fermion weight =
      finiteWittenIndex levels zero boson fermion := by
  classical
  unfold finiteWeightedSupertrace finiteWittenIndex
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hz : zero i
  · simp [hz, hzero i hi hz]
  · have hbf : boson i = fermion i := hpair i hi hz
    simp [hz, levelSuperdimension, hbf]

/--
Under the same explicit order correspondence, a paired finite weighted
supertrace is the signed divisor charge.  This is the finite algebraic bridge
between the parity readout and divisor language.
-/
theorem finiteWeightedSupertrace_eq_finiteDivisorIndex_of_order_correspondence
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) (weight : ι → Int) (order : ι → Int)
    (hzero : ∀ i ∈ levels, zero i → weight i = 1)
    (hpair : ∀ i ∈ levels, ¬ zero i → boson i = fermion i)
    (horder : ∀ i ∈ levels.filter zero,
      order i = levelSuperdimension boson fermion i) :
    finiteWeightedSupertrace levels boson fermion weight =
      finiteDivisorIndex (levels.filter zero) order := by
  rw [finiteWeightedSupertrace_eq_finiteWittenIndex
    levels zero boson fermion weight hzero hpair]
  unfold finiteWittenIndex finiteDivisorIndex
  apply Finset.sum_congr rfl
  intro i hi
  exact (horder i hi).symm

/-- The finite weighted supertrace is the kernel index of the explicit
zero-level parity complex when the nonzero levels pair. -/
theorem finiteWeightedSupertrace_eq_zeroLevelKernelIndex
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) (weight : ι → Int)
    (hzero : ∀ i ∈ levels, zero i → weight i = 1)
    (hpair : ∀ i ∈ levels, ¬ zero i → boson i = fermion i) :
    finiteWeightedSupertrace levels boson fermion weight =
      finiteKernelIndex (zeroLevelParityComplex levels zero boson fermion) := by
  rw [finiteWeightedSupertrace_eq_finiteWittenIndex
    levels zero boson fermion weight hzero hpair,
    finiteKernelIndex_zeroLevel_eq_finiteWittenIndex]

/--
Finite beta/weight-independence shadow.

Two supplied weights give the same supertrace when each is normalized to `1`
on zero levels and nonzero levels are explicitly paired.
-/
theorem finiteWeightedSupertrace_weight_independent
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) (weight₁ weight₂ : ι → Int)
    (hzero₁ : ∀ i ∈ levels, zero i → weight₁ i = 1)
    (hzero₂ : ∀ i ∈ levels, zero i → weight₂ i = 1)
    (hpair : ∀ i ∈ levels, ¬ zero i → boson i = fermion i) :
    finiteWeightedSupertrace levels boson fermion weight₁ =
      finiteWeightedSupertrace levels boson fermion weight₂ := by
  rw [finiteWeightedSupertrace_eq_finiteWittenIndex
        levels zero boson fermion weight₁ hzero₁ hpair,
      finiteWeightedSupertrace_eq_finiteWittenIndex
        levels zero boson fermion weight₂ hzero₂ hpair]

/-- If every finite level is paired, the supplied weighted supertrace vanishes. -/
theorem finiteWeightedSupertrace_eq_zero_of_all_paired
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) (weight : ι → Int)
    (hpair : ∀ i ∈ levels, ¬ zero i → boson i = fermion i)
    (hnozero : ∀ i ∈ levels, ¬ zero i) :
    finiteWeightedSupertrace levels boson fermion weight = 0 := by
  unfold finiteWeightedSupertrace
  apply Finset.sum_eq_zero
  intro i hi
  have hbf : boson i = fermion i := hpair i hi (hnozero i hi)
  simp [levelSuperdimension, hbf]

/-- Finite capstone: the weighted supertrace collapses to the Witten index and is
independent of a second normalized weight. -/
theorem kudinoor_finite_witten_index_capstone
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) (weight₁ weight₂ : ι → Int)
    (hzero₁ : ∀ i ∈ levels, zero i → weight₁ i = 1)
    (hzero₂ : ∀ i ∈ levels, zero i → weight₂ i = 1)
    (hpair : ∀ i ∈ levels, ¬ zero i → boson i = fermion i) :
    finiteWeightedSupertrace levels boson fermion weight₁ =
      finiteWittenIndex levels zero boson fermion ∧
    finiteWeightedSupertrace levels boson fermion weight₂ =
      finiteWittenIndex levels zero boson fermion ∧
    finiteWeightedSupertrace levels boson fermion weight₁ =
      finiteWeightedSupertrace levels boson fermion weight₂ :=
  ⟨finiteWeightedSupertrace_eq_finiteWittenIndex
      levels zero boson fermion weight₁ hzero₁ hpair,
    finiteWeightedSupertrace_eq_finiteWittenIndex
      levels zero boson fermion weight₂ hzero₂ hpair,
    finiteWeightedSupertrace_weight_independent
      levels zero boson fermion weight₁ weight₂ hzero₁ hzero₂ hpair⟩

end InfoGeometry.Arithmetic.KudinoorWittenIndexBridge
