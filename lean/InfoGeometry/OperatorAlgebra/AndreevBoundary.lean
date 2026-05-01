/-
InfoGeometry/OperatorAlgebra/AndreevBoundary.lean

Andreev boundary condition as a closure involution.

This module formalizes the algebraic content of Andreev reflection:

  electron-like quasiparticle ↔ hole-like quasiparticle

at a normal/superconducting boundary.

It does not assert that every superconducting surface hosts Majorana modes.
Topological edge protection is a separate witness.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.ClosureInvolution

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AndreevBoundary

open InfoGeometry.OperatorAlgebra.ClosureInvolution

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

/-! ## 2. Andreev closure datum -/

/--
Andreev boundary datum.

`V` is a real module of boundary quasiparticle amplitudes/readouts.

The datum supplies an involution `closure` and two distinguished amplitudes:
an electron-like boundary mode and its reflected hole-like mode.
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

  /-- The closure sends the hole-like channel back to the electron-like channel. -/
  theta_hole :
    closure.theta hole = electron

namespace AndreevBoundaryDatum

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (A : AndreevBoundaryDatum V)

/--
The Andreev diagonal is fixed by electron/hole closure.

This is the PR-safe algebraic form of the “Majorana diagonal.”
-/
theorem electron_hole_diagonal_fixed :
    A.electron + A.hole ∈ A.closure.Fixed :=
  A.closure.diagonal_fixed_of_swap
    A.theta_electron
    A.theta_hole

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

/-! ## 3. Charge/condensate accounting socket -/

/--
Charge/condensate accounting for an Andreev boundary process.

This deliberately does not hard-code charge signs. Different conventions use
electron charge `-e`, hole charge `+e`, or normalized current directions.

The supplied law is the bookkeeping witness saying that the boundary process is
charge-balanced by condensate transfer.
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
  Charge/current balance law for the Andreev event.

  The exact sign convention is model-dependent and is supplied here.
  -/
  charge_balance_law : Prop

  /-- Proof/certificate of the charge balance law. -/
  charge_balance_certificate :
    charge_balance_law

namespace AndreevChargeLedger

variable
    {V Charge : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Charge]

variable (L : AndreevChargeLedger V Charge)

/-- The supplied charge-balance law is available. -/
theorem charge_balance_valid :
    L.charge_balance_law :=
  L.charge_balance_certificate

/-- The Andreev diagonal is closure-fixed. -/
theorem diagonal_fixed :
    L.boundary.electron + L.boundary.hole ∈ L.boundary.closure.Fixed :=
  L.boundary.electron_hole_diagonal_fixed

/-- The Andreev imbalance is anti-fixed. -/
theorem imbalance_anti_fixed :
    L.boundary.closure.theta
        (L.boundary.electron - L.boundary.hole)
      =
        -(L.boundary.electron - L.boundary.hole) :=
  L.boundary.electron_hole_imbalance_anti_fixed

end AndreevChargeLedger

/-! ## 4. Optional topological edge witness -/

/--
Topological-superconductor edge witness.

This is separate from ordinary Andreev reflection. It records the extra fact
that a closure-fixed boundary amplitude is protected as an edge mode.

Without this witness, the Andreev boundary only gives electron/hole inversion,
not Majorana protection.
-/
structure TopologicalEdgeWitness
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  boundary :
    AndreevBoundaryDatum V

  /-- Boundary mode/readout. -/
  edgeMode :
    V

  /-- The edge mode is closure-fixed. -/
  edgeMode_fixed :
    edgeMode ∈ boundary.closure.Fixed

  /-- Topological protection law, supplied by the concrete model. -/
  topological_protection_law : Prop

  /-- Proof/certificate of topological protection. -/
  topological_protection_certificate :
    topological_protection_law

namespace TopologicalEdgeWitness

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (T : TopologicalEdgeWitness V)

/-- The edge mode is fixed by closure. -/
theorem theta_edgeMode_eq_edgeMode :
    T.boundary.closure.theta T.edgeMode = T.edgeMode :=
  (T.boundary.closure.mem_fixed_iff T.edgeMode).mp T.edgeMode_fixed

/-- The supplied topological protection certificate is available. -/
theorem topological_protection_valid :
    T.topological_protection_law :=
  T.topological_protection_certificate

end TopologicalEdgeWitness

end InfoGeometry.OperatorAlgebra.AndreevBoundary
