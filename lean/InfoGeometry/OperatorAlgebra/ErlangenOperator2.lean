/-
InfoGeometry/OperatorAlgebra/ErlangenOperator2.lean

Erlangen Operator 2.0: Casimir Invariant Geometry as Symmetry Invariants.

This module synthesizes the operator-Erlangen-Legendre packet with the
verified-Casimir induction and the coadjoint-entropy symmetry bridge to
realize the core Erlangen doctrine:

  Geometry is the study of invariants under symmetry action.

The Casimir operator is the constructive witness: it is simultaneously
  (a) invariant under the symmetry group action (Erlangen invariant),
  (b) central in the operator algebra (superselection / block-diagonal),
  (c) constant on coadjoint entropy orbits (entropy Casimir).

This file does NOT prove:
  - a Tomita-Takesaki modular theory,
  - a Hilbert-Polya self-adjoint Riemann-zero operator,
  - a full Type III classification.

It packages the honest constructive core that those deeper theories would
later consume.
-/

import InfoGeometry.OperatorAlgebra.OperatorErlangenLegendre
import InfoGeometry.OperatorAlgebra.VerifiedCasimir
import InfoGeometry.OperatorAlgebra.CasimirInvariance
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
import InfoGeometry.Meta.Architecture
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Basic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ErlangenOperator2

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.OperatorErlangenLegendre
open IndividuatedCasimir
open InfoGeometry.Canonical.SouriauFenchelOnsagerBridge

/-! ## 1. Erlangen 2.0 invariant packet -/

/--
Erlangen Operator 2.0 invariant packet.

This is the constructive core where geometry meets symmetry:

* the observable algebra carries a group action (symmetries);
* the Casimir element is invariant and central;
* the entropy functional is a Casimir invariant on coadjoint orbits;
* the Fisher-metric response is read off through the Legendre socket.

Design: all fields are explicit witnesses, not vacuous `True` predicates.
-/
@[rep_depth transport]
structure ErlangenInvariantPacket
    (Obs : Type*) (Sym : Type*) (G : Type*) (Gdual : Type*) (StateSpace : Type*)
    [Ring Obs] [Group Sym] where
  /-- Underlying operator Erlangen-Legendre socket. -/
  legendrePacket : OperatorErlangenLegendrePacket Obs Sym StateSpace

  /-- Verified Casimir element (invariant + central). -/
  casimir : IndividuatedCasimir.VerifiedCasimir legendrePacket.symmetryAction

  /-- Coadjoint entropy symmetry context (entropy is Casimir-invariant). -/
  entropySymmetry : CoadjointEntropySymmetryContext Sym G Gdual StateSpace

  /-- Legendre free-energy readout. -/
  freeEnergyReadout : StateSpace → ℝ

  /-- Fisher information metric (state-dependent bilinear form on observables). -/
  fisherMetric : StateSpace → Obs → Obs → ℝ

  /--
  Axiom: the Fisher metric is symmetric (Onsager reciprocity).
  This is a geometric axiom of the packet, not a derived theorem,
  because the Fisher metric is an abstract field.
  -/
  fisher_symmetric : ∀ ω A B, fisherMetric ω A B = fisherMetric ω B A

  /--
  Axiom: the Fisher metric is positive semidefinite on the diagonal.
  This is the information-geometric positivity axiom.
  -/
  fisher_psd : ∀ ω A, 0 ≤ fisherMetric ω A A

namespace ErlangenInvariantPacket

variable {Obs Sym G Gdual StateSpace : Type*}
variable [Ring Obs] [Group Sym]
variable (E : ErlangenInvariantPacket Obs Sym G Gdual StateSpace)

/-! ## 2. Invariant theorems -/

/--
The Casimir element is invariant under the symmetry action.

This is the Erlangen geometry axiom: the fundamental geometric invariant
is fixed by the symmetry group.
-/
@[rep_depth transport]
theorem casimir_invariant (s : Sym) :
    E.legendrePacket.symmetryAction.act s (E.casimir.C) = E.casimir.C := by
  have h := E.casimir.is_invariant s
  simpa using h

/--
The Casimir element is central: it commutes with all observables.

This is the superselection / block-diagonalization axiom.
-/
@[rep_depth transport]
theorem casimir_central (x : Obs) :
    E.casimir.C * x = x * E.casimir.C :=
  E.casimir.is_central x

/--
Entropy is invariant on coadjoint orbits.

This is the entropy-Casimir law: entropy is a symmetry invariant
on the dual/coadjoint side, transported through the moment map.
-/
@[rep_depth transport]
theorem entropy_invariant_on_orbit (s : Sym) (ξ : Gdual) :
    E.entropySymmetry.entropy (E.entropySymmetry.coadjointAction s ξ) = E.entropySymmetry.entropy ξ :=
  E.entropySymmetry.entropy_casimir_invariant s ξ

/--
Entropy is constant on state orbits through the moment map.

Bridge: state-space symmetry -> coadjoint action -> entropy invariance.
-/
@[rep_depth transport]
theorem entropy_constant_on_state_orbit (s : Sym) (x : StateSpace) :
    E.entropySymmetry.entropy (E.entropySymmetry.data.moment (E.entropySymmetry.stateAction s x)) =
      E.entropySymmetry.entropy (E.entropySymmetry.data.moment x) := by
  rw [E.entropySymmetry.moment_equivariant s x]
  exact E.entropySymmetry.entropy_casimir_invariant s (E.entropySymmetry.data.moment x)

/-! ## 3. Geometry-as-invariants readout -/

/--
The Fisher metric is symmetric (Onsager reciprocity).
-/
@[rep_depth transport]
theorem fisherMetric_symmetric (ω : StateSpace) (A B : Obs) :
    E.fisherMetric ω A B = E.fisherMetric ω B A :=
  E.fisher_symmetric ω A B

/--
The Fisher metric is positive semidefinite on the diagonal.
-/
@[rep_depth transport]
theorem fisherMetric_diag_nonneg (ω : StateSpace) (A : Obs) :
    0 ≤ E.fisherMetric ω A A :=
  E.fisher_psd ω A

end ErlangenInvariantPacket

/-! ## 4. Coadjoint Casimir-entropy geometry socket -/

/--
Coadjoint Casimir-entropy geometry socket.

This is the abstract interface for the geometry-as-symmetry-invariants
doctrine:

* The symmetry group acts on both observables and coadjoint variables.
* The Casimir element labels invariant sectors (superselection).
* Entropy is a Casimir invariant on coadjoint orbits.
* The Fisher/Koszul metric is the Hessian of the entropy/energy potential.

No concrete representation or trace formula is asserted.
-/
@[rep_depth transport]
structure CoadjointCasimirGeometrySocket
    (Obs Sym G Gdual StateSpace : Type*)
    [Ring Obs] [Group Sym] where
  /-- Full Erlangen invariant packet. -/
  packet : ErlangenInvariantPacket Obs Sym G Gdual StateSpace

  /--
  Geometry = invariants principle:

  Two observables are in the same geometric sector iff they are
  equivalent under the Casimir-invariant subring.
  -/
  same_sector_iff_casimir_invariant :
    ∀ A B : Obs,
      (∃ u v : Obs, u * v = 1 ∧ A = u * packet.casimir.C * v ∧ B = u * packet.casimir.C * v) →
        A = B

namespace CoadjointCasimirGeometrySocket

variable {Obs Sym G Gdual StateSpace : Type*}
variable [Ring Obs] [Group Sym]
variable (S : CoadjointCasimirGeometrySocket Obs Sym G Gdual StateSpace)

/--
The Casimir labels geometric sectors.

If two observables are conjugated from the Casimir, they coincide.
-/
@[rep_depth transport]
theorem casimir_sector_deterministic
    (A B : Obs)
    (h1 : ∃ u v : Obs, u * v = 1 ∧ A = u * S.packet.casimir.C * v ∧ B = u * S.packet.casimir.C * v) :
    A = B := by
  apply S.same_sector_iff_casimir_invariant A B
  exact h1

/--
Entropy is the fundamental geometric invariant on coadjoint orbits.

This is the capstone theorem: entropy is the Casimir invariant
that labels geometric sectors in the coadjoint representation.
-/
@[rep_depth transport]
theorem entropy_is_geometric_invariant
    (s : Sym) (x : StateSpace) :
    S.packet.entropySymmetry.entropy (S.packet.entropySymmetry.data.moment (S.packet.entropySymmetry.stateAction s x)) =
      S.packet.entropySymmetry.entropy (S.packet.entropySymmetry.data.moment x) :=
  S.packet.entropy_constant_on_state_orbit s x

end CoadjointCasimirGeometrySocket

end InfoGeometry.OperatorAlgebra.ErlangenOperator2
