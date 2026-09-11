/-
InfoGeometry/OperatorAlgebra/VortexPunctureRepair.lean

Localized puncture repair for vortex/impurity defects.

This module treats vortex cores and impurity-induced subgap states as localized
repair data. It does not prove superconducting regularity, Navier-Stokes
regularity, or Majorana protection beyond the explicit algebraic laws stored
below.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ClosureInvolution
import InfoGeometry.OperatorAlgebra.ChiralResidueAudit

noncomputable section

namespace InfoGeometry.OperatorAlgebra.VortexPunctureRepair

open InfoGeometry.OperatorAlgebra.ClosureInvolution
open InfoGeometry.OperatorAlgebra.ChiralResidueAudit

/-! ## 1. Localized punctures -/

/--
A localized puncture in a superconducting/order-parameter ledger.

`winding` records the topological phase winding. The unresolved singular locus
is defined intrinsically by nonzero winding rather than by an independent
proposition field.
-/
structure LocalizedPuncture where
  winding : ℤ

/-- A puncture is topologically nontrivial if its winding is nonzero. -/
def LocalizedPuncture.Nontrivial
    (P : LocalizedPuncture) : Prop :=
  P.winding ≠ 0

/-- The localized puncture is singular precisely when it carries nonzero
topological winding. -/
def LocalizedPuncture.Singular
    (P : LocalizedPuncture) : Prop :=
  P.Nontrivial

namespace LocalizedPuncture

variable (P : LocalizedPuncture)

/-- Nonzero winding is exactly nontriviality. -/
theorem nontrivial_iff :
    P.Nontrivial ↔ P.winding ≠ 0 :=
  Iff.rfl

/-- Singularity is the native nonzero-winding condition. -/
theorem singular_iff :
    P.Singular ↔ P.winding ≠ 0 :=
  Iff.rfl

end LocalizedPuncture

/-! ## 2. Vortex core data -/

/--
Vortex core datum.

`Memory` is the carrier for core/subgap/bound-state readouts.

The closure involution is the electron-hole / Majorana closure symmetry.
-/
structure VortexCoreDatum
    (Memory : Type*) [AddCommGroup Memory] [Module ℝ Memory] where
  closure : LinearClosureInvolution Memory
  puncture : LocalizedPuncture

  /-- Hidden/core state. -/
  coreState : Memory

  /-- Observable boundary/subgap readout of the core. -/
  boundaryReadout : Memory

namespace VortexCoreDatum

variable
    {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]

variable (V : VortexCoreDatum Memory)

end VortexCoreDatum

/-! ## 3. Majorana plug / fixed-point repair -/

/--
A Majorana-style plug for a localized puncture.

The plug is a closure-fixed state installed at the puncture.
-/
structure MajoranaPlugWitness
    (Memory : Type*) [AddCommGroup Memory] [Module ℝ Memory]
    (V : VortexCoreDatum Memory) where
  plug : Memory

  /-- The plug is fixed by the closure involution. -/
  plug_fixed : plug ∈ V.closure.Fixed

  /-- The core state is recovered/resolved by the plug. -/
  core_eq_plug : V.coreState = plug

namespace MajoranaPlugWitness

variable
    {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]
    {V : VortexCoreDatum Memory}

variable (P : MajoranaPlugWitness Memory V)

/-- The plug is pointwise fixed by closure. -/
theorem theta_plug_eq_plug :
    V.closure.theta P.plug = P.plug :=
  (V.closure.mem_fixed_iff P.plug).mp P.plug_fixed

/-- The core state is closure-fixed because it equals the plug. -/
theorem theta_coreState_eq_coreState
    (P : MajoranaPlugWitness Memory V) :
    V.closure.theta V.coreState = V.coreState := by
  rw [MajoranaPlugWitness.core_eq_plug P]
  exact P.theta_plug_eq_plug

end MajoranaPlugWitness

/-! ## 4. YSR / subgap localized repair datum -/

/--
Localized subgap repair witness.

This abstracts YSR-type or vortex-core subgap localization.

It says an unresolved localized defect is isolated into a controlled subgap
state. It does not assert topological Majorana protection unless paired with a
`MajoranaPlugWitness`.
-/
structure SubgapRepairWitness
    (Memory : Type*) [AddCommGroup Memory] [Module ℝ Memory]
    (V : VortexCoreDatum Memory) where
  /-- Localized subgap state. -/
  subgapState : Memory

  /-- The core state is represented by the localized subgap state. -/
  core_eq_subgap : V.coreState = subgapState

  /-- A repaired core has no residual mismatch with its localized state. -/
  residual_eq_zero : V.coreState - subgapState = 0

namespace SubgapRepairWitness

variable
    {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]
    {V : VortexCoreDatum Memory}

variable (S : SubgapRepairWitness Memory V)

/-- The core state is represented by the subgap state. -/
theorem core_eq_subgap_state :
    V.coreState = S.subgapState :=
  S.core_eq_subgap

/-- Resolution is the vanishing of the core/subgap residual. -/
def Resolved : Prop :=
  V.coreState - S.subgapState = 0

/-- Every subgap repair witness is resolved by its concrete residual law. -/
theorem resolved :
    S.Resolved :=
  S.residual_eq_zero

/-- The residual formulation is equivalent to the represented-core law. -/
theorem resolved_iff_core_eq_subgap :
    S.Resolved ↔ V.coreState = S.subgapState := by
  exact sub_eq_zero

end SubgapRepairWitness

/-! ## 5. Audit bridge -/

/--
A vortex repair bridge connecting chiral audit to localized repair.

This is the point where an obstructed audit can be repaired before a later
flow/backend theorem is invoked.
-/
structure VortexRepairBridge
    (Memory : Type*) [AddCommGroup Memory] [Module ℝ Memory] where
  context : ChiralAuditContext

  /-- Input residue before local repair. -/
  inputResidue : ChiralResidue Memory

  /-- Output residue after local repair. -/
  repairedResidue : ChiralResidue Memory

  /-- The repaired residue is benign for the genesis context. -/
  repaired_benign :
    IsBenign context repairedResidue

namespace VortexRepairBridge

variable
    {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]

variable (B : VortexRepairBridge Memory)

/-- The repaired residue passes the chiral audit. -/
theorem audit_repaired_benign :
    audit B.context B.repairedResidue = ChiralAuditVerdict.benign :=
  (B.context.audit_benign_iff B.repairedResidue).mpr B.repaired_benign

end VortexRepairBridge

end InfoGeometry.OperatorAlgebra.VortexPunctureRepair
