/-
InfoGeometry/OperatorAlgebra/AndreevBoundary.lean

Andreev boundary condition as a closure involution.

This module formalizes the algebraic content of Andreev reflection:

  electron-like quasiparticle ↔ hole-like quasiparticle

at a normal/superconducting boundary.

The hole-like channel is a quasiparticle hole, not a physical positron.

This file does not assert that every superconducting surface hosts Majorana
modes. Topological edge protection is a separate witness.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ClosureInvolution
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AndreevBoundary

open ClosureInvolution

/-! ## 1. Quasiparticle side labels -/

/--
Boundary quasiparticle channel.

`electronLike` and `holeLike` are Bogoliubov/Andreev channel labels.
The `holeLike` channel is a quasiparticle hole, not a physical positron.
-/
inductive AndreevChannel where
  | electronLike
  | holeLike
deriving DecidableEq, Repr

namespace AndreevChannel

/-- Electron/hole channel flip. -/
def flip : AndreevChannel → AndreevChannel
  | electronLike => holeLike
  | holeLike => electronLike

@[simp]
theorem flip_electronLike :
    flip electronLike = holeLike :=
  rfl

@[simp]
theorem flip_holeLike :
    flip holeLike = electronLike :=
  rfl

@[simp]
theorem flip_involutive
    (c : AndreevChannel) :
    flip (flip c) = c := by
  cases c <;> rfl

theorem not_eq_flip
    (c : AndreevChannel) :
    c ≠ flip c := by
  cases c <;> simp

end AndreevChannel

/-! ## 2. Concrete finite Andreev amplitude model -/

/--
Finite real Andreev amplitude space.

An element assigns an amplitude/readout to the electron-like and hole-like
channels.
-/
abbrev AndreevAmplitude : Type :=
  AndreevChannel → ℝ

/-- Linear flip on Andreev amplitudes. -/
def andreevFlipLinear : AndreevAmplitude →ₗ[ℝ] AndreevAmplitude where
  toFun := fun ψ c => ψ (AndreevChannel.flip c)
  map_add' := by
    intro ψ φ
    ext c
    simp
  map_smul' := by
    intro a ψ
    ext c
    simp

/-- The Andreev flip is involutive. -/
theorem andreevFlipLinear_sq
    (ψ : AndreevAmplitude) :
    andreevFlipLinear (andreevFlipLinear ψ) = ψ := by
  ext c
  cases c <;> rfl

/-- Concrete closure involution on finite Andreev amplitudes. -/
def finiteAndreevClosure :
    LinearClosureInvolution AndreevAmplitude where
  theta := andreevFlipLinear
  theta_involutive := andreevFlipLinear_sq

/-- Electron-like basis amplitude. -/
def electronAmplitude : AndreevAmplitude :=
  fun c => if c = AndreevChannel.electronLike then 1 else 0

/-- Hole-like basis amplitude. -/
def holeAmplitude : AndreevAmplitude :=
  fun c => if c = AndreevChannel.holeLike then 1 else 0

/-- The finite closure sends the electron-like basis to the hole-like basis. -/
theorem finiteClosure_theta_electron :
    finiteAndreevClosure.theta electronAmplitude =
      holeAmplitude := by
  ext c
  cases c <;>
    simp [finiteAndreevClosure, andreevFlipLinear, electronAmplitude, holeAmplitude]

/-- The finite closure sends the hole-like basis to the electron-like basis. -/
theorem finiteClosure_theta_hole :
    finiteAndreevClosure.theta holeAmplitude =
      electronAmplitude := by
  ext c
  cases c <;>
    simp [finiteAndreevClosure, andreevFlipLinear, electronAmplitude, holeAmplitude]

/-- The finite Andreev diagonal is fixed. -/
theorem finite_electron_hole_diagonal_fixed :
    electronAmplitude + holeAmplitude ∈ finiteAndreevClosure.Fixed :=
  finiteAndreevClosure.diagonal_fixed_of_swap
    finiteClosure_theta_electron
    finiteClosure_theta_hole

/-- The finite electron/hole imbalance is anti-fixed. -/
theorem finite_electron_hole_imbalance_anti_fixed :
    finiteAndreevClosure.theta
        (electronAmplitude - holeAmplitude)
      =
        -(electronAmplitude - holeAmplitude) :=
  finiteAndreevClosure.difference_anti_fixed_of_swap
    finiteClosure_theta_electron
    finiteClosure_theta_hole

/-! ## 3. Boundary closure witness -/

/--
Constructive witness that a boundary process satisfies the Andreev swap.

This packages the swap certificates as first-class data.
-/
structure AndreevSwapWitness
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (closure : LinearClosureInvolution V)
    (electron hole : V) : Type where
  theta_electron : closure.theta electron = hole
  theta_hole : closure.theta hole = electron

/--
The Andreev diagonal is fixed by electron/hole closure, given a swap witness.
-/
theorem electron_hole_diagonal_fixed_of_swap_witness
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (closure : LinearClosureInvolution V)
    (electron hole : V)
    (w : AndreevSwapWitness closure electron hole) :
    electron + hole ∈ closure.Fixed :=
  closure.diagonal_fixed_of_swap w.theta_electron w.theta_hole


/-! ## 4. Andreev closure datum -/

/--
Andreev boundary datum.

`V` is a real module of boundary quasiparticle amplitudes/readouts.

The datum supplies an involution `closure` and two distinguished amplitudes:
an electron-like boundary mode and its reflected hole-like mode.

Only the electron-to-hole reflection is primitive. The reverse reflection is
derived from closure involutivity.
-/
structure AndreevBoundaryDatum
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Electron/hole closure involution. -/
  closure : LinearClosureInvolution V

  /-- Incoming electron-like boundary amplitude. -/
  electron : V

  /-- Reflected hole-like boundary amplitude. -/
  hole : V

  /-- The closure sends the electron-like channel to the hole-like channel. -/
  theta_electron :
    closure.theta electron = hole

namespace AndreevBoundaryDatum

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (A : AndreevBoundaryDatum V)

/--
The closure sends the hole-like channel back to the electron-like channel.

This is derived, not separately assumed.
-/
theorem theta_hole :
    A.closure.theta A.hole = A.electron := by
  have h := A.closure.theta_involutive A.electron
  rw [A.theta_electron] at h
  exact h

/--
The Andreev diagonal is fixed by electron/hole closure.

This is the PR-safe algebraic form of the “Majorana diagonal.”
-/
theorem electron_hole_diagonal_fixed :
    A.electron + A.hole ∈ A.closure.Fixed :=
  A.closure.diagonal_fixed_of_swap
    A.theta_electron
    A.theta_hole

/-- Pointwise fixed-form of the Andreev diagonal. -/
theorem theta_diagonal_eq_diagonal :
    A.closure.theta (A.electron + A.hole) =
      A.electron + A.hole :=
  (A.closure.mem_fixed_iff (A.electron + A.hole)).mp
    A.electron_hole_diagonal_fixed

/--
A closure-fixed boundary mode is unchanged by the Andreev mirror.

This is the formal “Majorana transparency” statement. It does not say this
mode is physically unique; uniqueness/protection requires a separate witness.
-/
theorem transparent_of_fixed
    {γ : V}
    (hγ : γ ∈ A.closure.Fixed) :
    A.closure.theta γ = γ :=
  (A.closure.mem_fixed_iff γ).mp hγ

/-- The Andreev diagonal is transparent to the boundary closure. -/
theorem electron_hole_diagonal_transparent :
    A.closure.theta (A.electron + A.hole) =
      A.electron + A.hole :=
  transparent_of_fixed A A.electron_hole_diagonal_fixed

/--
The electron/hole imbalance is anti-fixed.

This is the chiral/charge-imbalance component reversed by Andreev closure.
-/
theorem electron_hole_imbalance_anti_fixed :
    A.closure.theta (A.electron - A.hole) =
      -(A.electron - A.hole) :=
  A.closure.difference_anti_fixed_of_swap
    A.theta_electron
    A.theta_hole

/--
The closure image of the electron is the hole.
-/
theorem reflected_hole_eq_theta_electron :
    A.hole = A.closure.theta A.electron :=
  A.theta_electron.symm

/--
The closure image of the hole is the electron.
-/
theorem reflected_electron_eq_theta_hole :
    A.electron = A.closure.theta A.hole :=
  A.theta_hole.symm

end AndreevBoundaryDatum

/-! ## 5. Concrete finite Andreev boundary -/

/-- Concrete finite Andreev boundary datum. -/
def finiteAndreevBoundaryDatum :
    AndreevBoundaryDatum AndreevAmplitude where
  closure := finiteAndreevClosure
  electron := electronAmplitude
  hole := holeAmplitude
  theta_electron := finiteClosure_theta_electron

/-- The finite Andreev boundary diagonal is fixed. -/
theorem finiteAndreevBoundary_diagonal_fixed :
    finiteAndreevBoundaryDatum.electron +
        finiteAndreevBoundaryDatum.hole
      ∈ finiteAndreevBoundaryDatum.closure.Fixed :=
  finiteAndreevBoundaryDatum.electron_hole_diagonal_fixed

/-- The finite Andreev boundary imbalance is anti-fixed. -/
theorem finiteAndreevBoundary_imbalance_anti_fixed :
    finiteAndreevBoundaryDatum.closure.theta
        (finiteAndreevBoundaryDatum.electron -
          finiteAndreevBoundaryDatum.hole)
      =
        -(finiteAndreevBoundaryDatum.electron -
          finiteAndreevBoundaryDatum.hole) :=
  finiteAndreevBoundaryDatum.electron_hole_imbalance_anti_fixed

/--
Constructive packet for Andreev boundary closure claims.

This packages the boundary datum together with first-class witnesses for
(1) diagonal fixedness and (2) imbalance anti-fixedness.
-/
structure BoundaryClosureWitness
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  boundary : AndreevBoundaryDatum V
  diagonal_fixed_cert :
    boundary.electron + boundary.hole ∈ boundary.closure.Fixed
  imbalance_anti_fixed_cert :
    boundary.closure.theta (boundary.electron - boundary.hole) =
      -(boundary.electron - boundary.hole)

namespace BoundaryClosureWitness

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (W : BoundaryClosureWitness V)

/-- Read back closure-fixed diagonal from the constructive packet. -/
theorem diagonal_fixed :
    W.boundary.electron + W.boundary.hole ∈ W.boundary.closure.Fixed :=
  W.diagonal_fixed_cert

/-- Read back anti-fixed imbalance from the constructive packet. -/
theorem imbalance_anti_fixed :
    W.boundary.closure.theta (W.boundary.electron - W.boundary.hole) =
      -(W.boundary.electron - W.boundary.hole) :=
  W.imbalance_anti_fixed_cert

/-- Canonical constructor from any Andreev boundary datum. -/
def ofBoundary
    (A : AndreevBoundaryDatum V) : BoundaryClosureWitness V where
  boundary := A
  diagonal_fixed_cert := A.electron_hole_diagonal_fixed
  imbalance_anti_fixed_cert := A.electron_hole_imbalance_anti_fixed

end BoundaryClosureWitness

/-! ## 6. Charge/condensate accounting -/

/--
Charge/condensate accounting for an Andreev boundary process.

The sign convention is encoded by `chargeOf` and `condensateTransfer`.

The explicit balance equation is:

`chargeOf electron = chargeOf hole + condensateTransfer`.

This does not hard-code whether electron charge is represented as `-e`, `+e`,
or as a current-oriented quantity. The convention is carried by `chargeOf`.
-/
structure AndreevChargeLedger
    (V Charge : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Charge] where
  boundary :
    AndreevBoundaryDatum V

  /-- Charge/current readout for a boundary amplitude. -/
  chargeOf :
    V → Charge

  /-- Charge/current transferred into the superconducting condensate. -/
  condensateTransfer :
    Charge

  /--
  Explicit charge/current balance law for the Andreev event.
  -/
  charge_balance :
    chargeOf boundary.electron =
      chargeOf boundary.hole + condensateTransfer

/--
Constructive witness for the explicit charge balance law of an Andreev process.
-/
structure ChargeBalanceWitness
    {V Charge : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Charge]
    (L : AndreevChargeLedger V Charge) : Type where
  certificate :
    L.chargeOf L.boundary.electron =
      L.chargeOf L.boundary.hole + L.condensateTransfer

namespace AndreevChargeLedger

variable
    {V Charge : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Charge]

variable (L : AndreevChargeLedger V Charge)

/-- The explicit charge-balance equation. -/
theorem charge_balance_holds :
    L.chargeOf L.boundary.electron =
      L.chargeOf L.boundary.hole + L.condensateTransfer :=
  L.charge_balance

/--
The charge-balance equation is valid, given a witness.
-/
theorem charge_balance_valid_of_witness
    (w : ChargeBalanceWitness L) :
    L.chargeOf L.boundary.electron =
      L.chargeOf L.boundary.hole + L.condensateTransfer :=
  w.certificate

/-- The Andreev diagonal is closure-fixed. -/
theorem diagonal_fixed :
    L.boundary.electron + L.boundary.hole ∈ L.boundary.closure.Fixed :=
  L.boundary.electron_hole_diagonal_fixed

/--
Witness-only surface for closure-fixed diagonal readout.
-/
theorem diagonal_fixed_of_boundary_witness
    (W : BoundaryClosureWitness V)
    (hboundary : W.boundary = L.boundary) :
    L.boundary.electron + L.boundary.hole ∈ L.boundary.closure.Fixed := by
  simpa [hboundary] using W.diagonal_fixed

/-- The Andreev imbalance is anti-fixed. -/
theorem imbalance_anti_fixed :
    L.boundary.closure.theta
        (L.boundary.electron - L.boundary.hole)
      =
        -(L.boundary.electron - L.boundary.hole) :=
  L.boundary.electron_hole_imbalance_anti_fixed

/--
The boundary charge defect equals the condensate transfer, in the chosen sign
convention.
-/
theorem boundary_charge_defect_eq_condensateTransfer :
    L.chargeOf L.boundary.electron -
        L.chargeOf L.boundary.hole =
      L.condensateTransfer := by
  rw [L.charge_balance]
  abel

/-- Equivalent balance form with all terms on one side. -/
theorem charge_balance_zero_form :
    L.chargeOf L.boundary.electron -
        L.chargeOf L.boundary.hole -
        L.condensateTransfer =
      0 := by
  rw [L.boundary_charge_defect_eq_condensateTransfer]
  abel

end AndreevChargeLedger

/-! ## 7. Owner theorems discharged constructively -/

/-- Constructive proof of the finite Andreev diagonal owner target. -/
theorem finiteAndreevDiagonalOwnerTarget :
    electronAmplitude + holeAmplitude ∈ finiteAndreevClosure.Fixed :=
  finite_electron_hole_diagonal_fixed

/-- Constructive proof of the finite Andreev imbalance owner target. -/
theorem finiteAndreevImbalanceOwnerTarget :
    finiteAndreevClosure.theta
        (electronAmplitude - holeAmplitude)
      =
        -(electronAmplitude - holeAmplitude) :=
  finite_electron_hole_imbalance_anti_fixed

@[owner_target_tag]
theorem finiteAndreevBoundary_packet :
    electronAmplitude + holeAmplitude ∈ finiteAndreevClosure.Fixed ∧
      finiteAndreevClosure.theta
          (electronAmplitude - holeAmplitude)
        =
          -(electronAmplitude - holeAmplitude) :=
  ⟨finiteAndreevDiagonalOwnerTarget, finiteAndreevImbalanceOwnerTarget⟩

end InfoGeometry.OperatorAlgebra.AndreevBoundary
