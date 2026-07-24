import Mathlib

/-!
# Kudinoor supersymmetry/Witten-index bridge, finite owner surface

This module records the finite theorem-backed fragment of the exposition
"Supersymmetry and the Witten Index" (Arjun Kudinoor, 2023):

* a finite graded spectrum has a boson count and a fermion count at each level;
* nonzero levels are explicitly paired by the hypothesis `boson = fermion`;
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

/-- Finite weighted supertrace over a supplied level weight. -/
def finiteWeightedSupertrace
    (levels : Finset ι) (boson fermion : ι → Nat) (weight : ι → Int) : Int :=
  ∑ i ∈ levels, levelSuperdimension boson fermion i * weight i

/-- Explicit nonzero pairing makes the level superdimension vanish. -/
theorem nonzero_level_superdimension_zero
    (boson fermion : ι → Nat) {i : ι}
    (hpair : boson i = fermion i) :
    levelSuperdimension boson fermion i = 0 := by
  simp [levelSuperdimension, hpair]

/-- A zero level with weight `1` contributes its ordinary superdimension. -/
theorem zero_weighted_level_eq_unweighted
    (boson fermion : ι → Nat) (weight : ι → Int) {i : ι}
    (hweight : weight i = 1) :
    levelSuperdimension boson fermion i * weight i =
      levelSuperdimension boson fermion i := by
  simp [hweight]

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

/--
Finite capstone: the weighted supertrace collapses to the Witten index and is
independent of a second normalized weight.
-/
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
