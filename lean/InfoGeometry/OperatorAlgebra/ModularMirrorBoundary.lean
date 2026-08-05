/-
InfoGeometry/OperatorAlgebra/ModularMirrorBoundary.lean

Closure/mirror boundary algebra.

This module abstracts the common algebraic core of:

* Andreev electron/hole reflection;
* modular J-type reflection;
* horizon membrane mirror interfaces.

It proves:

* the reflected output is forced by involutivity;
* the diagonal input + output is closure-fixed;
* the imbalance input - output is anti-fixed;
* a fixed mode is transparent to the mirror;
* uniqueness of the transparent mode requires an explicit one-dimensional
  fixed-sector witness.

It does not assert that black-hole horizons are literal superconductors.
It does not assert that every horizon has Andreev physics.
It does not assert that every fixed diagonal is a protected Majorana edge mode.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ClosureInvolution
import InfoGeometry.OperatorAlgebra.AndreevBoundary
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ModularMirrorBoundary

open InfoGeometry.OperatorAlgebra.ClosureInvolution
open InfoGeometry.OperatorAlgebra.AndreevBoundary

/-! ## 1. Abstract closure mirror -/

/--
A closure mirror boundary.

`input` is the incoming mode/readout.

`output` is the reflected mode/readout.

The primitive law is `θ input = output`. The reverse law is derived from
`θ² = id`.
-/
structure ClosureMirrorBoundary
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Closure / modular / particle-hole mirror involution. -/
  closure : LinearClosureInvolution V

  /-- Incoming mode/readout. -/
  input : V

  /-- Reflected mode/readout. -/
  output : V

  /-- Mirror reflection law. -/
  theta_input :
    closure.theta input = output

namespace ClosureMirrorBoundary

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (M : ClosureMirrorBoundary V)

/--
The mirror sends the reflected output back to the input.

This is derived from involutivity, not separately assumed.
-/
theorem theta_output :
    M.closure.theta M.output = M.input := by
  have h := M.closure.theta_involutive M.input
  rw [M.theta_input] at h
  exact h

/-- The closure-fixed diagonal mode. -/
def diagonal : V :=
  M.input + M.output

/-- The anti-fixed imbalance mode. -/
def imbalance : V :=
  M.input - M.output

/-- A mode is transparent to the mirror if reflection leaves it unchanged. -/
def IsTransparent
    (ψ : V) : Prop :=
  M.closure.theta ψ = ψ

/-- The diagonal mode is fixed by the closure mirror. -/
theorem diagonal_fixed :
    M.diagonal ∈ M.closure.Fixed := by
  apply (M.closure.mem_fixed_iff M.diagonal).mpr
  dsimp [diagonal]
  calc
    M.closure.theta (M.input + M.output)
        = M.closure.theta M.input + M.closure.theta M.output := by
            exact M.closure.theta.map_add M.input M.output
    _ = M.output + M.input := by
            rw [M.theta_input, M.theta_output]
    _ = M.input + M.output := by
            abel

/-- The diagonal mode is transparent to the mirror. -/
theorem diagonal_transparent :
    M.IsTransparent M.diagonal :=
  (M.closure.mem_fixed_iff M.diagonal).mp M.diagonal_fixed

/-- Transparency is equivalent to membership in the closure fixed sector. -/
theorem transparent_iff_fixed
    (ψ : V) :
    M.IsTransparent ψ ↔ ψ ∈ M.closure.Fixed := by
  constructor
  · intro h
    exact (M.closure.mem_fixed_iff ψ).mpr h
  · intro h
    exact (M.closure.mem_fixed_iff ψ).mp h

/-- The imbalance mode is anti-fixed by the closure mirror. -/
theorem imbalance_anti_fixed :
    M.closure.theta M.imbalance = -M.imbalance := by
  dsimp [imbalance]
  calc
    M.closure.theta (M.input - M.output)
        = M.closure.theta M.input - M.closure.theta M.output := by
            exact M.closure.theta.map_sub M.input M.output
    _ = M.output - M.input := by
            rw [M.theta_input, M.theta_output]
    _ = -(M.input - M.output) := by
            abel

end ClosureMirrorBoundary

/-! ## 2. Andreev boundary as a closure mirror -/

namespace ClosureMirrorBoundary

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Every Andreev boundary datum gives a closure mirror boundary. -/
def ofAndreevBoundary
    (A : AndreevBoundaryDatum V) :
    ClosureMirrorBoundary V where
  closure := A.closure
  input := A.electron
  output := A.hole
  theta_input := A.theta_electron

/-- The Andreev electron/hole diagonal is transparent as a closure mirror mode. -/
theorem andreev_diagonal_transparent
    (A : AndreevBoundaryDatum V) :
    (ofAndreevBoundary A).IsTransparent
      ((ofAndreevBoundary A).diagonal) :=
  (ofAndreevBoundary A).diagonal_transparent

/-- The Andreev imbalance is anti-fixed as a closure mirror mode. -/
theorem andreev_imbalance_anti_fixed
    (A : AndreevBoundaryDatum V) :
    (ofAndreevBoundary A).closure.theta
        ((ofAndreevBoundary A).imbalance)
      =
        -((ofAndreevBoundary A).imbalance) :=
  (ofAndreevBoundary A).imbalance_anti_fixed

end ClosureMirrorBoundary

/-! ## 3. Balance / no-leakage ledger -/

/--
A balance ledger for a mirror boundary.

This is the formal version of “no unresolved leakage.”

It does not say the reservoir is zero. It says that the input/output defect is
accounted for by a reservoir transfer.
-/
structure MirrorBalanceLedger
    (V Quantity : Type*)
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Quantity] where
  mirror :
    ClosureMirrorBoundary V

  /-- Quantity/readout assigned to a mode. -/
  quantityOf :
    V → Quantity

  /-- Reservoir transfer needed to close the ledger. -/
  reservoirTransfer :
    Quantity

  /--
  Explicit balance equation.

  `quantity(input) = quantity(output) + reservoirTransfer`.
  -/
  balance :
    quantityOf mirror.input =
      quantityOf mirror.output + reservoirTransfer

namespace MirrorBalanceLedger

variable
    {V Quantity : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Quantity]

variable (L : MirrorBalanceLedger V Quantity)

/-- The boundary quantity defect equals the reservoir transfer. -/
theorem boundary_defect_eq_reservoirTransfer :
    L.quantityOf L.mirror.input -
        L.quantityOf L.mirror.output =
      L.reservoirTransfer := by
  rw [L.balance]
  abel

/-- Equivalent zero-sum balance form. -/
theorem balance_zero_form :
    L.quantityOf L.mirror.input -
        L.quantityOf L.mirror.output -
        L.reservoirTransfer =
      0 := by
  rw [L.boundary_defect_eq_reservoirTransfer]
  abel

/-- The balanced mirror still has a transparent diagonal. -/
theorem diagonal_transparent :
    L.mirror.IsTransparent L.mirror.diagonal :=
  L.mirror.diagonal_transparent

end MirrorBalanceLedger

/-! ## 4. Horizon membrane socket -/

/--
A horizon membrane mirror socket.

This captures the membrane-paradigm fact that a horizon can be modeled as a
finite-resistance membrane/mirror.

Positive surface resistance explicitly prevents treating this socket as a
zero-resistance superconductor without extra data.
-/
structure HorizonMembraneMirror
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    extends ClosureMirrorBoundary V where
  /-- Effective membrane surface resistance. -/
  surfaceResistance : ℝ

  /-- The membrane resistance is positive. -/
  surfaceResistance_pos :
    0 < surfaceResistance

namespace HorizonMembraneMirror

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (H : HorizonMembraneMirror V)

/-- The horizon membrane socket is not a zero-resistance surface. -/
theorem surfaceResistance_ne_zero :
    H.surfaceResistance ≠ 0 :=
  ne_of_gt H.surfaceResistance_pos

/-- Zero surface resistance is excluded by the membrane witness. -/
theorem not_zero_surfaceResistance :
    ¬ H.surfaceResistance = 0 :=
  H.surfaceResistance_ne_zero

/-- The horizon membrane diagonal is transparent with respect to its closure mirror. -/
theorem diagonal_transparent :
    H.toClosureMirrorBoundary.IsTransparent
      H.toClosureMirrorBoundary.diagonal :=
  H.toClosureMirrorBoundary.diagonal_transparent

/-- The horizon membrane imbalance is anti-fixed. -/
theorem imbalance_anti_fixed :
    H.closure.theta
        H.toClosureMirrorBoundary.imbalance
      =
        -H.toClosureMirrorBoundary.imbalance :=
  H.toClosureMirrorBoundary.imbalance_anti_fixed

end HorizonMembraneMirror

/-! ## 5. Optional one-dimensional transparency witness -/

/--
A witness that the transparent/fixed sector is generated by the mirror
diagonal.

This is the extra hypothesis needed to say the diagonal is the only transparent
mode up to scalar multiple.
-/
structure UniqueTransparentLine
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : ClosureMirrorBoundary V) where
  /-- Every transparent mode lies in the span of the diagonal. -/
  transparent_mem_diagonal_span :
    ∀ ψ : V,
      M.IsTransparent ψ →
        ψ ∈ Submodule.span ℝ ({M.diagonal} : Set V)

namespace UniqueTransparentLine

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {M : ClosureMirrorBoundary V}

variable (U : UniqueTransparentLine M)

/-- Uniqueness of transparent modes, up to the diagonal line. -/
theorem transparent_lies_in_diagonal_span
    (U : UniqueTransparentLine M)
    {ψ : V}
    (hψ : M.IsTransparent ψ) :
    ψ ∈ Submodule.span ℝ ({M.diagonal} : Set V) :=
  UniqueTransparentLine.transparent_mem_diagonal_span U ψ hψ

/-- The diagonal itself lies in the transparent line. -/
theorem diagonal_mem_diagonal_span :
    M.diagonal ∈ Submodule.span ℝ ({M.diagonal} : Set V) :=
  Submodule.subset_span (by simp)

end UniqueTransparentLine

/-! ## 6. Optional flux-expulsion / Meissner-like witness -/

/--
A witness-gated flux-expulsion socket.

This is suitable for extremal black-hole Meissner-like effects or genuine
superconducting Meissner effects, but the expulsion theorem is not automatic
from closure-mirror algebra.
-/
structure FluxExpulsionWitness
    (Cap Flux : Type*) [Zero Flux] where
  /-- Flux through a boundary cap/surface. -/
  fluxThrough :
    Cap → Flux

  /-- Expulsion condition. -/
  flux_expelled :
    ∀ c : Cap, fluxThrough c = 0

namespace FluxExpulsionWitness

variable
    {Cap Flux : Type*} [Zero Flux]

variable (F : FluxExpulsionWitness Cap Flux)

/-- The supplied flux-expulsion witness gives zero flux through every cap. -/
theorem fluxThrough_eq_zero
    (c : Cap) :
    F.fluxThrough c = 0 :=
  F.flux_expelled c

end FluxExpulsionWitness

/-! ## 7. Boundary readout -/

/--
Modular mirror boundary readout.

Every closure mirror has a transparent diagonal and an anti-fixed imbalance.
-/
theorem modularMirrorBoundaryOwnerTarget :
  ∀ (V : Type*) [AddCommGroup V] [Module ℝ V],
  ∀ M : ClosureMirrorBoundary V,
    M.IsTransparent M.diagonal ∧
    M.closure.theta M.imbalance = -M.imbalance := by
  intro V _ _ M
  exact
    ⟨M.diagonal_transparent,
      M.imbalance_anti_fixed⟩

end InfoGeometry.OperatorAlgebra.ModularMirrorBoundary
