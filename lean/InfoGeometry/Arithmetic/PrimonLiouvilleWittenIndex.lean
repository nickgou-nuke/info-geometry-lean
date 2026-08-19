import Mathlib.Tactic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic
import InfoGeometry.Arithmetic.PrimeBosonFermionGas
import InfoGeometry.Arithmetic.PrimonFinite

/-!
# InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex

Finite projected hyperbolic chiral index layer for the primon gas.

This file keeps the hyperbolic/Dirac picture theorem-safe:

* the stable branch is the one-lane square-free fermionic Witten index;
* the raw two-branch hyperbolic readout is a finite difference
  `stable - unstable`;
* projecting or regularizing away the unstable branch is represented by an
  explicit property packet.

No infinite Euler product, reciprocal-zeta theorem, analytic continuation,
Type III trace statement, or Riemann-zero statement is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex

open PrimonFinite

variable {PrimeLabel R : Type*}

/-! ## 1. One-lane square-free Witten index -/

/--
One-lane finite fermionic Witten index over a finite prime-mode register.

This is exactly the finite square-free parity supertrace

`∑ T ⊆ P, (-1)^|T| ∏ p ∈ T, q p`.
-/
def oneLaneFermionicWittenIndex
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (q : PrimeLabel → R) : R :=
  STrF P q

/--
Finite square-free expansion of the one-lane Witten index.

This is the finite theorem-root of the signed fermionic product
`∏ p ∈ P, (1 - q p)`.
-/
theorem oneLaneFermionicWittenIndex_eq_product
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (q : PrimeLabel → R) :
    oneLaneFermionicWittenIndex P q = ∏ p ∈ P, (1 - q p) := by
  exact STrF_eq_prod P q

/--
Stable chiral index.

In the hyperbolic chiral picture, this is the projected contracting/Mellin
branch. It is finite here and makes no analytic limit claim.
-/
def stableChiralIndex
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (qStable : PrimeLabel → R) : R :=
  oneLaneFermionicWittenIndex P qStable

/-- Product form of the stable chiral index. -/
theorem stableChiralIndex_eq_product
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (qStable : PrimeLabel → R) :
    stableChiralIndex P qStable = ∏ p ∈ P, (1 - qStable p) := by
  exact oneLaneFermionicWittenIndex_eq_product P qStable

/--
Unstable chiral index.

This is the finite algebraic expanding branch. It is not discarded by
definition.
-/
def unstableChiralIndex
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (qUnstable : PrimeLabel → R) : R :=
  oneLaneFermionicWittenIndex P qUnstable

/-- Product form of the unstable chiral index. -/
theorem unstableChiralIndex_eq_product
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (qUnstable : PrimeLabel → R) :
    unstableChiralIndex P qUnstable = ∏ p ∈ P, (1 - qUnstable p) := by
  exact oneLaneFermionicWittenIndex_eq_product P qUnstable

/-! ## 2. Raw two-branch hyperbolic index -/

/--
Finite two-branch Liouville/Witten readout.

The raw hyperbolic chiral index contains the stable branch minus the unstable
branch. Any identification with a purely stable readout must be supplied by a
separate regularization/projection property.
-/
def directSumLiouvilleWittenIndex
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (qStable qUnstable : PrimeLabel → R) : R :=
  stableChiralIndex P qStable - unstableChiralIndex P qUnstable

/-- Alias for the raw finite hyperbolic chiral index. -/
def rawHyperbolicChiralIndex
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (qStable qUnstable : PrimeLabel → R) : R :=
  directSumLiouvilleWittenIndex P qStable qUnstable

/--
The raw finite hyperbolic chiral index is the stable branch minus the unstable
branch.
-/
theorem rawHyperbolicChiralIndex_eq_stable_sub_unstable
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (qStable qUnstable : PrimeLabel → R) :
    rawHyperbolicChiralIndex P qStable qUnstable =
      stableChiralIndex P qStable - unstableChiralIndex P qUnstable := by
  rfl

/-- Product-side form of the finite two-branch readout. -/
theorem directSumLiouvilleWittenIndex_eq_products
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (qStable qUnstable : PrimeLabel → R) :
    directSumLiouvilleWittenIndex P qStable qUnstable =
      (∏ p ∈ P, (1 - qStable p)) - (∏ p ∈ P, (1 - qUnstable p)) := by
  rw [directSumLiouvilleWittenIndex, stableChiralIndex_eq_product,
    unstableChiralIndex_eq_product]

/-- Product-side form of the raw finite hyperbolic chiral index. -/
theorem rawHyperbolicChiralIndex_eq_products
    [DecidableEq PrimeLabel] [CommRing R]
    (P : Finset PrimeLabel)
    (qStable qUnstable : PrimeLabel → R) :
    rawHyperbolicChiralIndex P qStable qUnstable =
      (∏ p ∈ P, (1 - qStable p)) - (∏ p ∈ P, (1 - qUnstable p)) := by
  rw [rawHyperbolicChiralIndex, directSumLiouvilleWittenIndex_eq_products]

/-! ## 3. Stable-branch projection / regularization -/

def stableBranchRegularization
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (modes : Finset PrimeLabel) (qStable : PrimeLabel → R)
    (regularizedReadout : R) : Prop :=
  regularizedReadout = stableChiralIndex modes qStable

theorem stableBranchRegularization_eq_stable
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (modes : Finset PrimeLabel) (qStable : PrimeLabel → R)
    (regularizedReadout : R)
    (h : stableBranchRegularization modes qStable regularizedReadout) :
    regularizedReadout = stableChiralIndex modes qStable :=
  h

/-! ## 4. Readout packets and guardrails -/

def projectedHyperbolicChiralIndex
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    [TopologicalSpace R]
    (modes : Finset PrimeLabel) (qStable qUnstable : PrimeLabel → R)
    (rawReadout stableReadout unstableReadout : R)
    (stableSequence : ℕ → R) (stableLimit : R) : Prop :=
  rawReadout = stableReadout - unstableReadout ∧
  stableReadout = stableChiralIndex modes qStable ∧
  unstableReadout = unstableChiralIndex modes qUnstable ∧
  Filter.Tendsto stableSequence Filter.atTop (nhds stableLimit) ∧
  stableLimit = stableReadout ∧
  rawReadout ≠ stableReadout

theorem projectedHyperbolicChiralIndex_raw_split
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    [TopologicalSpace R]
    (modes : Finset PrimeLabel) (qStable qUnstable : PrimeLabel → R)
    (rawReadout stableReadout unstableReadout : R)
    (stableSequence : ℕ → R) (stableLimit : R)
    (h : projectedHyperbolicChiralIndex modes qStable qUnstable
      rawReadout stableReadout unstableReadout stableSequence stableLimit) :
    rawReadout = stableReadout - unstableReadout := h.1

theorem projectedHyperbolicChiralIndex_stable_oneLane
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    [TopologicalSpace R]
    (modes : Finset PrimeLabel) (qStable qUnstable : PrimeLabel → R)
    (rawReadout stableReadout unstableReadout : R)
    (stableSequence : ℕ → R) (stableLimit : R)
    (h : projectedHyperbolicChiralIndex modes qStable qUnstable
      rawReadout stableReadout unstableReadout stableSequence stableLimit) :
    stableReadout = stableChiralIndex modes qStable := h.2.1

theorem projectedHyperbolicChiralIndex_unstable_oneLane
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    [TopologicalSpace R]
    (modes : Finset PrimeLabel) (qStable qUnstable : PrimeLabel → R)
    (rawReadout stableReadout unstableReadout : R)
    (stableSequence : ℕ → R) (stableLimit : R)
    (h : projectedHyperbolicChiralIndex modes qStable qUnstable
      rawReadout stableReadout unstableReadout stableSequence stableLimit) :
    unstableReadout = unstableChiralIndex modes qUnstable := h.2.2.1

universe u v

namespace MellinThermalVsDiracHeatKernel

/-- Disjoint carrier separating the Mellin/thermal lane from the Dirac heat lane. -/
def ReadoutSpecies (M : Type u) (D : Type v) : Type (max u v) := Sum M D

/-- Embed a Mellin/thermal readout into the separated readout species. -/
def mellinSpecies {M : Type u} {D : Type v} (x : M) : ReadoutSpecies M D :=
  Sum.inl x

/-- Embed a Dirac heat readout into the separated readout species. -/
def diracSpecies {M : Type u} {D : Type v} (x : D) : ReadoutSpecies M D :=
  Sum.inr x

/-- The Mellin/thermal lane and Dirac heat lane remain disjoint in the separated species carrier. -/
theorem readoutSpecies_separate {M : Type u} {D : Type v} (x : M) (y : D) :
    mellinSpecies (D := D) x ≠ diracSpecies (M := M) y := by
  intro h
  cases h

/-- The separated species carrier remembers each Mellin/thermal readout exactly. -/
@[simp] theorem mellinSpecies_injective {M : Type u} {D : Type v}
    {x y : M} (h : mellinSpecies (D := D) x = mellinSpecies y) : x = y := by
  injection h

/-- The separated species carrier remembers each Dirac heat readout exactly. -/
@[simp] theorem diracSpecies_injective {M : Type u} {D : Type v}
    {x y : D} (h : diracSpecies (M := M) x = diracSpecies y) : x = y := by
  injection h

end MellinThermalVsDiracHeatKernel

end InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex
