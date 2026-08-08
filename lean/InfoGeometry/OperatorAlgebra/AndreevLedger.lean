/-
InfoGeometry/OperatorAlgebra/AndreevLedger.lean

Andreev reflection as a particle-hole closure ledger.

This module formalizes the algebraic core only:

* a particle-hole closure involution;
* an Andreev electron/hole swap pair;
* the closure-fixed diagonal mode `electron + hole`;
* the anti-fixed orthogonal mode `electron - hole`;
* a BdG Hamiltonian ledger where particle-hole symmetry flips energy;
* a property-gated Majorana zero-mode and vortex-core memory layer.

No Navier-Stokes regularity statement is asserted.
No claim is made that every vortex hosts a Majorana zero mode.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ClosureInvolution

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AndreevLedger

open InfoGeometry.OperatorAlgebra.ClosureInvolution

/-! ## 1. Andreev particle-hole closure ledger -/

/--
An Andreev ledger is a real-linear particle-hole closure involution equipped
with a positive superconducting gap scale.

This is a real doubled/BdG-style model. In the complex Hilbert-space
presentation, particle-hole symmetry is antiunitary; here it is represented as
a real-linear closure involution.
-/
structure Ledger
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    extends LinearClosureInvolution V where
  /-- Superconducting gap scale. -/
  delta : ℝ

  /-- The gap is positive. -/
  delta_pos : 0 < delta

namespace Ledger

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (A : Ledger V)

/-- Subgap energy condition. -/
def SubgapEnergy
    (ε : ℝ) : Prop :=
  |ε| < A.delta

/-- Zero energy lies inside the positive superconducting gap. -/
theorem zero_subgap :
    A.SubgapEnergy 0 := by
  simpa [SubgapEnergy] using A.delta_pos

end Ledger

/-! ## 2. Andreev reflection pair -/

/--
An Andreev reflection pair.

`electron_to_hole` records the particle-hole reflection:

`θ electron = hole`.

The reverse identity is derived from involutivity.
-/
structure AndreevPair
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Ledger V) where
  electron : V
  hole : V
  electron_to_hole :
    A.theta electron = hole

namespace AndreevPair

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {A : Ledger V}

variable (P : AndreevPair A)

/-- The reverse particle-hole reflection is forced by involutivity. -/
theorem hole_to_electron :
    A.theta P.hole = P.electron := by
  have h := A.theta_involutive P.electron
  rw [P.electron_to_hole] at h
  exact h

/-- The even/diagonal Majorana candidate: `γ₊ = electron + hole`. -/
def evenMajorana : V :=
  P.electron + P.hole

/-- The odd/anti-diagonal particle-hole mode: `γ₋ = electron - hole`. -/
def oddMajorana : V :=
  P.electron - P.hole

/--
The diagonal Andreev mode is fixed by particle-hole closure.

This is the algebraic core of the “Majorana equals particle-hole diagonal”
statement.
-/
theorem evenMajorana_fixed :
    P.evenMajorana ∈ A.Fixed := by
  apply (A.mem_fixed_iff P.evenMajorana).mpr
  dsimp [evenMajorana]
  calc
    A.theta (P.electron + P.hole)
        = A.theta P.electron + A.theta P.hole := by
            exact A.theta.map_add P.electron P.hole
    _ = P.hole + P.electron := by
            rw [P.electron_to_hole, P.hole_to_electron]
    _ = P.electron + P.hole := by
            abel

/-- The diagonal Andreev mode is pointwise fixed by particle-hole closure. -/
@[simp]
theorem theta_evenMajorana_eq_evenMajorana :
    A.theta P.evenMajorana = P.evenMajorana := by
  exact (A.mem_fixed_iff P.evenMajorana).mp P.evenMajorana_fixed

/-- The odd Andreev mode is anti-fixed by particle-hole closure. -/
theorem oddMajorana_antiFixed :
    A.theta P.oddMajorana = -P.oddMajorana := by
  dsimp [oddMajorana]
  calc
    A.theta (P.electron - P.hole)
        = A.theta P.electron - A.theta P.hole := by
            exact A.theta.map_sub P.electron P.hole
    _ = P.hole - P.electron := by
            rw [P.electron_to_hole, P.hole_to_electron]
    _ = -(P.electron - P.hole) := by
            abel

end AndreevPair

/-! ## 3. BdG Hamiltonian particle-hole ledger -/

/--
A BdG Hamiltonian ledger over an Andreev particle-hole closure.

The anticommutation law is written as

`H (θ v) = - θ (H v)`,

so an energy-`ε` mode is sent to an energy-`-ε` mode.
-/
structure BdGHamiltonianLedger
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    extends Ledger V where
  /-- Real-linear BdG Hamiltonian. -/
  H : V →ₗ[ℝ] V

  /-- Particle-hole anticommutation. -/
  particle_hole_anticommutes :
    ∀ v : V,
      H (theta v) = -theta (H v)

namespace BdGHamiltonianLedger

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : BdGHamiltonianLedger V)

/-- Energy eigenvector predicate. -/
def IsEnergyEigenvector
    (ψ : V)
    (ε : ℝ) : Prop :=
  B.H ψ = ε • ψ

/-- Zero-energy mode predicate. -/
def IsZeroMode
    (ψ : V) : Prop :=
  B.H ψ = 0

/-- Particle-hole symmetry flips the BdG energy. -/
theorem particle_hole_flips_energy
    {ψ : V}
    {ε : ℝ}
    (hψ : B.IsEnergyEigenvector ψ ε) :
    B.IsEnergyEigenvector (B.theta ψ) (-ε) := by
  unfold IsEnergyEigenvector at hψ ⊢
  calc
    B.H (B.theta ψ)
        = -B.theta (B.H ψ) := by
            exact B.particle_hole_anticommutes ψ
    _ = -B.theta (ε • ψ) := by
            rw [hψ]
    _ = -(ε • B.theta ψ) := by
            rw [B.theta.map_smul]
    _ = (-ε) • B.theta ψ := by
            simp

/-- Particle-hole symmetry preserves the zero-energy subspace. -/
theorem particle_hole_preserves_zeroMode
    {ψ : V}
    (hψ : B.IsZeroMode ψ) :
    B.IsZeroMode (B.theta ψ) := by
  unfold IsZeroMode at hψ ⊢
  calc
    B.H (B.theta ψ)
        = -B.theta (B.H ψ) := by
            exact B.particle_hole_anticommutes ψ
    _ = -B.theta 0 := by
            rw [hψ]
    _ = 0 := by
            simp

end BdGHamiltonianLedger

/-! ## 4. Majorana zero-mode witnesses -/

/--
A Majorana zero-mode property.

This is intentionally proof-bearing:

* `zero_energy` says the mode is a BdG zero mode;
* `fixed` says the mode is particle-hole self-conjugate.
-/
structure MajoranaZeroMode
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : BdGHamiltonianLedger V) where
  mode : V
  zero_energy :
    B.IsZeroMode mode
  fixed :
    mode ∈ B.Fixed

namespace MajoranaZeroMode

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {B : BdGHamiltonianLedger V}

/--
Construct a Majorana zero-mode property from an Andreev pair, provided the
diagonal mode is zero-energy for the supplied BdG Hamiltonian.
-/
def ofAndreevPair
    (P : AndreevPair B.toLedger)
    (hzero : B.IsZeroMode P.evenMajorana) :
    MajoranaZeroMode B where
  mode := P.evenMajorana
  zero_energy := hzero
  fixed := P.evenMajorana_fixed

/-- A Majorana zero mode is fixed by particle-hole closure. -/
theorem theta_mode_eq_mode
    (M : MajoranaZeroMode B) :
    B.theta M.mode = M.mode :=
  (B.mem_fixed_iff M.mode).mp M.fixed

end MajoranaZeroMode

/-! ## 5. Vortex-core memory, property-gated (Native Closure Mandated: Closure Debt) -/

/--
A property that a particular vortex core carries a Majorana zero mode.

This is deliberately not derived from the mere existence of a vortex. In
physical models, vortex-core Majorana modes require topological superconducting
conditions and an actual BdG/topological proof.
-/
structure VortexCoreMajoranaWitness
    (Core V : Type*)
    [AddCommGroup V] [Module ℝ V]
    (B : BdGHamiltonianLedger V) where
  /-- Vortex core label/location. -/
  core : Core

  /-- Majorana zero mode attached to this core. -/
  majorana : MajoranaZeroMode B

  /-- Core-indexed linear subspace of states localized at the vortex core. -/
  localizationSubspace : Core → Submodule ℝ V

  /-- The Majorana mode belongs to the localization subspace of its core. -/
  localized_at_core :
    majorana.mode ∈ localizationSubspace core

namespace VortexCoreMajoranaWitness

variable
    {Core V : Type*}
    [AddCommGroup V] [Module ℝ V]
    {B : BdGHamiltonianLedger V}

variable (W : VortexCoreMajoranaWitness Core V B)

/-- The vortex-core property supplies a BdG zero mode. -/
theorem core_mode_zero :
    B.IsZeroMode W.majorana.mode :=
  W.majorana.zero_energy

/-- The vortex-core property supplies particle-hole self-conjugacy. -/
theorem core_mode_fixed :
    W.majorana.mode ∈ B.Fixed :=
  W.majorana.fixed

/-- The vortex-core Majorana mode lies in the core's owned localization
subspace. -/
theorem core_mode_localized :
    W.majorana.mode ∈ W.localizationSubspace W.core :=
  W.localized_at_core

end VortexCoreMajoranaWitness

end InfoGeometry.OperatorAlgebra.AndreevLedger
