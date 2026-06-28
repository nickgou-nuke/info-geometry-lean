import Mathlib
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

open InfoGeometry.Arithmetic.PrimonFinite

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
    (PrimeLabel R : Type*) [DecidableEq PrimeLabel] [CommRing R] where
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
  /-- Optional external analytic bridge for the stable branch. -/
  stableAnalyticWitness : Type*
  /-- Guardrail: the raw two-branch readout is not the stable branch by default. -/
  raw_not_stable_without_projection_guard : Type*

namespace ProjectedHyperbolicChiralIndexPacket

variable [DecidableEq PrimeLabel] [CommRing R]
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
@[simp] theorem mellinSpecies_injective
    (G : MellinThermalVsDiracHeatKernelGuard)
    {x y : G.mellinThermalReadout}
    (h : G.mellinSpecies x = G.mellinSpecies y) : x = y := by
  injection h

/-- The separated species carrier remembers each Dirac heat readout exactly. -/
@[simp] theorem diracSpecies_injective
    (G : MellinThermalVsDiracHeatKernelGuard)
    {x y : G.diracHeatReadout}
    (h : G.diracSpecies x = G.diracSpecies y) : x = y := by
  injection h

end MellinThermalVsDiracHeatKernelGuard

end InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex
