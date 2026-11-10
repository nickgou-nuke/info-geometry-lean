/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
  explicit witness packet.

No infinite Euler product, reciprocal-zeta theorem, analytic continuation,
Type III trace statement, or Riemann-zero statement is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

open PrimonFinite

section NonCommRingHyperbolicChiralIndex

variable {PrimeLabel B : Type*} [Ring B]

/-- Ordered stable chiral Euler product `(modes.map (fun p => 1 - qStable p)).prod` in `[Ring B]`. -/
def ringStableChiralIndexList (modes : List PrimeLabel) (qStable : PrimeLabel → B) : B :=
  (modes.map (fun p => 1 - qStable p)).prod

/-- Ordered unstable chiral Euler product `(modes.map (fun p => 1 - qUnstable p)).prod` in `[Ring B]`. -/
def ringUnstableChiralIndexList (modes : List PrimeLabel) (qUnstable : PrimeLabel → B) : B :=
  (modes.map (fun p => 1 - qUnstable p)).prod

/-- Ordered raw two-branch hyperbolic chiral index `stable - unstable` in `[Ring B]`. -/
def ringRawHyperbolicChiralIndexList
    (modes : List PrimeLabel) (qStable qUnstable : PrimeLabel → B) : B :=
  ringStableChiralIndexList modes qStable - ringUnstableChiralIndexList modes qUnstable

/-- Two-mode non-commutative expansion of the raw hyperbolic chiral index in `[Ring B]`. -/
theorem ringRawHyperbolicChiralIndexList_two_modes
    (p₁ p₂ : PrimeLabel) (qStable qUnstable : PrimeLabel → B) :
    ringRawHyperbolicChiralIndexList [p₁, p₂] qStable qUnstable =
      (qUnstable p₁ - qStable p₁) + (qUnstable p₂ - qStable p₂) +
        (qStable p₁ * qStable p₂ - qUnstable p₁ * qUnstable p₂) := by
  simp [ringRawHyperbolicChiralIndexList, ringStableChiralIndexList, ringUnstableChiralIndexList]
  noncomm_ring

end NonCommRingHyperbolicChiralIndex

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

This is the finite algebraic placeholder for the expanding branch. It is not
discarded by definition.
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
separate regularization/projection witness.
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

/-! ## 3. Stable-branch projection / regularization witnesses -/

/--
Witness packet for a model that projects or regularizes the raw hyperbolic
readout to the stable branch.

The two propositions record the model-dependent facts that the stable branch is
selected and the unstable branch has been removed. The actual readout equality
is kept as a separate field.
-/
structure StableBranchRegularization
    (PrimeLabel R : Type*) [DecidableEq PrimeLabel] [CommRing R] where
  modes : Finset PrimeLabel
  qStable : PrimeLabel → R
  qUnstable : PrimeLabel → R
  regularizedReadout : R
  regularized_eq_stable :
    regularizedReadout = stableChiralIndex modes qStable

namespace StableBranchRegularization

variable [DecidableEq PrimeLabel] [CommRing R]
variable (B : StableBranchRegularization PrimeLabel R)

/-- The supplied regularized readout is the stable chiral branch. -/
theorem regularized_eq_stable_branch :
    B.regularizedReadout = stableChiralIndex B.modes B.qStable :=
  B.regularized_eq_stable

end StableBranchRegularization

/-! ## 4. Readout packets and guardrails -/

/--
Finite projected hyperbolic chiral index packet.

This connects a raw two-branch readout to its stable and unstable finite lanes.
Any inverse-zeta or analytic interpretation is deliberately only a witness
field, not a theorem in this file.
-/
structure ProjectedHyperbolicChiralIndexPacket
    (PrimeLabel R : Type*) [DecidableEq PrimeLabel] [CommRing R]
    [TopologicalSpace R] where
  modes : Finset PrimeLabel
  qStable : PrimeLabel → R
  qUnstable : PrimeLabel → R
  rawReadout : R
  stableReadout : R
  unstableReadout : R
  raw_eq_stable_sub_unstable :
    rawReadout = stableReadout - unstableReadout
  stable_eq_index :
    stableReadout = stableChiralIndex modes qStable
  unstable_eq_index :
    unstableReadout = unstableChiralIndex modes qUnstable
  /-- A topological sequence of stable-branch approximants. -/
  stableSequence : ℕ → R
  /-- Its limiting stable-branch readout. -/
  stableLimit : R
  stableSequence_converges :
    Filter.Tendsto stableSequence Filter.atTop (nhds stableLimit)
  stableLimit_eq_stableReadout :
    stableLimit = stableReadout
  /-- Explicit guardrail when the two finite branches are distinct. -/
  raw_not_stable_without_projection : rawReadout ≠ stableReadout

namespace ProjectedHyperbolicChiralIndexPacket

variable [DecidableEq PrimeLabel] [CommRing R] [TopologicalSpace R]
variable (P : ProjectedHyperbolicChiralIndexPacket PrimeLabel R)

/-- The raw packet readout splits as stable minus unstable. -/
theorem raw_split :
    P.rawReadout = P.stableReadout - P.unstableReadout :=
  P.raw_eq_stable_sub_unstable

/-- The stable packet readout is the one-lane finite Witten index. -/
theorem stable_is_oneLane :
    P.stableReadout = stableChiralIndex P.modes P.qStable :=
  P.stable_eq_index

/-- The unstable packet readout is the one-lane finite Witten index. -/
theorem unstable_is_oneLane :
    P.unstableReadout = unstableChiralIndex P.modes P.qUnstable :=
  P.unstable_eq_index

/-- Product-side form of the stable packet readout. -/
theorem stable_eq_product :
    P.stableReadout = ∏ p ∈ P.modes, (1 - P.qStable p) := by
  rw [P.stable_eq_index, stableChiralIndex_eq_product]

/-- Product-side form of the unstable packet readout. -/
theorem unstable_eq_product :
    P.unstableReadout = ∏ p ∈ P.modes, (1 - P.qUnstable p) := by
  rw [P.unstable_eq_index, unstableChiralIndex_eq_product]

end ProjectedHyperbolicChiralIndexPacket

/--
Guardrail separating the Mellin/thermal kernel from the ordinary Dirac heat
kernel.

The reciprocal-zeta/Möbius thermal lane uses a readout of the form `e^{-sH}`.
An ordinary Dirac heat kernel would use `e^{-tD²}` and requires its own
separate owner surface.
-/
structure MellinThermalVsDiracHeatKernelGuard where
  Hamiltonian : Type*
  DiracOperator : Type*
  mellinThermalReadout : Type*
  diracHeatReadout : Type*

namespace MellinThermalVsDiracHeatKernelGuard

/-- Disjoint carrier separating the Mellin/thermal lane from the Dirac heat lane. -/
def ReadoutSpecies (G : MellinThermalVsDiracHeatKernelGuard) : Type :=
  Sum G.mellinThermalReadout G.diracHeatReadout

/-- Embed a Mellin/thermal readout into the separated readout species. -/
def mellinSpecies (G : MellinThermalVsDiracHeatKernelGuard)
    (x : G.mellinThermalReadout) : G.ReadoutSpecies :=
  Sum.inl x

/-- Embed a Dirac heat readout into the separated readout species. -/
def diracSpecies (G : MellinThermalVsDiracHeatKernelGuard)
    (x : G.diracHeatReadout) : G.ReadoutSpecies :=
  Sum.inr x

/-- The Mellin/thermal lane and Dirac heat lane remain disjoint in the separated species carrier. -/
theorem readoutSpecies_separate
    (G : MellinThermalVsDiracHeatKernelGuard)
    (x : G.mellinThermalReadout) (y : G.diracHeatReadout) :
    G.mellinSpecies x ≠ G.diracSpecies y := by
  intro h
  cases h

/-- The separated species carrier remembers each Mellin/thermal readout exactly. -/
theorem mellinSpecies_injective
    (G : MellinThermalVsDiracHeatKernelGuard)
    {x y : G.mellinThermalReadout}
    (h : G.mellinSpecies x = G.mellinSpecies y) : x = y := by
  injection h

/-- The separated species carrier remembers each Dirac heat readout exactly. -/
theorem diracSpecies_injective
    (G : MellinThermalVsDiracHeatKernelGuard)
    {x y : G.diracHeatReadout}
    (h : G.diracSpecies x = G.diracSpecies y) : x = y := by
  injection h

end MellinThermalVsDiracHeatKernelGuard

/-- Ground inhabitant of `StableBranchRegularization` over `ℤ`. -/
def intEmptyStableBranchRegularization : StableBranchRegularization ℕ ℤ where
  modes := ∅
  qStable := fun idx => (idx : ℤ)
  qUnstable := fun idx => (idx : ℤ)
  regularizedReadout := 1
  regularized_eq_stable := by
    simp [stableChiralIndex, oneLaneFermionicWittenIndex, STrF, parity, weight]

/-- Ground inhabitant of `ProjectedHyperbolicChiralIndexPacket` over `ℝ`. -/
def realSingletonProjectedHyperbolicChiralIndexPacket :
    ProjectedHyperbolicChiralIndexPacket ℕ ℝ where
  modes := ∅
  qStable := fun idx => (idx : ℝ)
  qUnstable := fun idx => (idx : ℝ)
  rawReadout := 0
  stableReadout := 1
  unstableReadout := 1
  raw_eq_stable_sub_unstable := by norm_num
  stable_eq_index := by simp [stableChiralIndex, oneLaneFermionicWittenIndex, STrF, parity, weight]
  unstable_eq_index := by simp [unstableChiralIndex, oneLaneFermionicWittenIndex, STrF, parity, weight]
  stableSequence := fun _ => 1
  stableLimit := 1
  stableSequence_converges := tendsto_const_nhds
  stableLimit_eq_stableReadout := rfl
  raw_not_stable_without_projection := by norm_num

/-- Ground inhabitant of `MellinThermalVsDiracHeatKernelGuard`. -/
def unitMellinThermalVsDiracHeatKernelGuard : MellinThermalVsDiracHeatKernelGuard where
  Hamiltonian := ℤ
  DiracOperator := ℤ
  mellinThermalReadout := ℤ
  diracHeatReadout := ℤ

end InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex
