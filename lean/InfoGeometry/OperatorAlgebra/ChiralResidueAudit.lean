/-
InfoGeometry/OperatorAlgebra/ChiralResidueAudit.lean

Chiral residue audit for crossover data.

This module formalizes the audit layer only.

It does not prove Navier-Stokes regularity or singularity formation.
It classifies chiral residues and exposes the witness boundary required to
turn an audit verdict into a flow-regularity theorem.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ClosureInvolution

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralResidueAudit

open InfoGeometry.OperatorAlgebra.ClosureInvolution

/-! ## 1. Chiral parity -/

/--
Chiral parity of a surviving crossover residue.

This is an orientation label, not a moral predicate by itself.
-/
inductive ChiralParity where
  | left
  | right
deriving DecidableEq, Repr

namespace ChiralParity

/-- Chiral reversal. -/
def flip : ChiralParity → ChiralParity
  | left => right
  | right => left

@[simp]
theorem flip_left :
    flip left = right :=
  rfl

@[simp]
theorem flip_right :
    flip right = left :=
  rfl

@[simp]
theorem flip_involutive
    (p : ChiralParity) :
    flip (flip p) = p := by
  cases p <;> rfl

/-- Opposite parity. -/
def Opposite
    (p q : ChiralParity) : Prop :=
  q = flip p

theorem not_eq_flip
    (p : ChiralParity) :
    p ≠ flip p := by
  cases p <;> simp

end ChiralParity

/-! ## 2. Chiral residues -/

/--
A chiral crossover residue.

`Memory` is the carrier of surviving residue data.

The residue is required to lie in the fixed sector of a closure involution. This
is the algebraic content of “the residue survives the `e₋ ↔ e₊` inversion.”
-/
structure ChiralResidue
    (Memory : Type*) [AddCommGroup Memory] [Module ℝ Memory] where
  /-- Closure/Möbius/Majorana involution. -/
  closure : LinearClosureInvolution Memory

  /-- Surviving residue. -/
  residue : Memory

  /-- Integer divisor weight. -/
  weight : ℤ

  /-- Chiral orientation of the residue. -/
  parity : ChiralParity

  /-- The residue survives closure inversion. -/
  residue_fixed :
    residue ∈ closure.Fixed

namespace ChiralResidue

variable
    {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]

variable (R : ChiralResidue Memory)

/-- The residue is fixed by the closure involution. -/
theorem theta_residue_eq_residue :
    R.closure.theta R.residue = R.residue :=
  (R.closure.mem_fixed_iff R.residue).mp R.residue_fixed

end ChiralResidue

/-! ## 3. Audit context and verdict -/

/--
Audit context for a new genesis/quench.

`genesisOrientation` is the chiral orientation required by the new metric
quench.
-/
structure ChiralAuditContext where
  genesisOrientation : ChiralParity

/--
Audit verdict.

`benign` means parity is aligned with the target genesis orientation.
`obstructed` means parity is misaligned.

This is a classification, not yet a flow theorem.
-/
inductive ChiralAuditVerdict where
  | benign
  | obstructed
deriving DecidableEq, Repr

/-- Parity alignment predicate. -/
def ParityAligned
    {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]
    (C : ChiralAuditContext)
    (R : ChiralResidue Memory) : Prop :=
  R.parity = C.genesisOrientation

/-- A residue is benign if its parity matches the genesis orientation. -/
def IsBenign
    {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]
    (C : ChiralAuditContext)
    (R : ChiralResidue Memory) : Prop :=
  ParityAligned C R

/-- A residue is obstructed if its parity does not match the genesis orientation. -/
def IsObstructed
    {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]
    (C : ChiralAuditContext)
    (R : ChiralResidue Memory) : Prop :=
  ¬ ParityAligned C R

/-- Run the chiral audit. -/
def audit
    {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]
    (C : ChiralAuditContext)
    (R : ChiralResidue Memory) :
    ChiralAuditVerdict :=
  if R.parity = C.genesisOrientation then
    ChiralAuditVerdict.benign
  else
    ChiralAuditVerdict.obstructed

namespace ChiralAuditContext

variable
    {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]

variable (C : ChiralAuditContext)
variable (R : ChiralResidue Memory)

/-- The audit returns benign exactly when parity is aligned. -/
theorem audit_benign_iff :
    audit C R = ChiralAuditVerdict.benign ↔
      ParityAligned C R := by
  unfold audit ParityAligned
  by_cases h : R.parity = C.genesisOrientation
  · simp [h]
  · simp [h]

/-- The audit returns obstructed exactly when parity is not aligned. -/
theorem audit_obstructed_iff :
    audit C R = ChiralAuditVerdict.obstructed ↔
      IsObstructed C R := by
  unfold audit IsObstructed ParityAligned
  by_cases h : R.parity = C.genesisOrientation
  · simp [h]
  · simp [h]

/-- Benign and obstructed classifications are mutually exclusive. -/
theorem not_benign_and_obstructed :
    ¬ (IsBenign C R ∧ IsObstructed C R) := by
  intro h
  exact h.2 h.1

end ChiralAuditContext

/-! ## 4. Flow-regularity backend -/

/--
A generic flow-regularity backend.

This deliberately abstracts over Navier-Stokes. It records the extra analytic
bridge required to turn a residue audit into a regularity or obstruction
statement.
-/
structure FlowRegularityBackend
    (Residue Flow : Type*) where
  /-- Flow induced by a residue. -/
  flowOf : Residue → Flow

  /-- Global regularity predicate. -/
  GloballyRegular : Flow → Prop

  /-- Obstruction/singularity predicate. -/
  Obstructed : Flow → Prop

  /-- Regularizing residue predicate. -/
  Regularizing : Residue → Prop

  /-- Obstructing residue predicate. -/
  Obstructing : Residue → Prop

  /-- Regularizing residues induce globally regular flows. -/
  regular_of_regularizing :
    ∀ r : Residue,
      Regularizing r →
        GloballyRegular (flowOf r)

  /-- Obstructing residues induce obstructed flows. -/
  obstructed_of_obstructing :
    ∀ r : Residue,
      Obstructing r →
        Obstructed (flowOf r)

  /-- An obstructed flow is not globally regular. -/
  obstructed_not_regular :
    ∀ f : Flow,
      Obstructed f →
        ¬ GloballyRegular f

namespace FlowRegularityBackend

variable {Residue Flow : Type*}
variable (B : FlowRegularityBackend Residue Flow)

/-- A regularizing residue induces a globally regular flow. -/
theorem globallyRegular_of_regularizing
    {r : Residue}
    (hr : B.Regularizing r) :
    B.GloballyRegular (B.flowOf r) :=
  B.regular_of_regularizing r hr

/-- An obstructing residue induces a non-regular flow. -/
theorem not_globallyRegular_of_obstructing
    {r : Residue}
    (hr : B.Obstructing r) :
    ¬ B.GloballyRegular (B.flowOf r) := by
  apply B.obstructed_not_regular
  exact B.obstructed_of_obstructing r hr

end FlowRegularityBackend

/-! ## 5. Chiral audit to regularity bridge -/

/--
Bridge from chiral audit verdicts to a flow-regularity backend.

This is the precise place where an analytic theorem must be supplied. Without
this bridge, chiral parity is only an audit label.
-/
structure ChiralAuditRegularityBridge
    (Memory Flow : Type*) [AddCommGroup Memory] [Module ℝ Memory] where
  context : ChiralAuditContext

  backend :
    FlowRegularityBackend (ChiralResidue Memory) Flow

  /-- Benign residues are regularizing. -/
  regularizing_of_benign :
    ∀ R : ChiralResidue Memory,
      IsBenign context R →
        backend.Regularizing R

  /-- Obstructed residues are obstructing. -/
  obstructing_of_obstructed :
    ∀ R : ChiralResidue Memory,
      IsObstructed context R →
        backend.Obstructing R

namespace ChiralAuditRegularityBridge

variable
    {Memory Flow : Type*} [AddCommGroup Memory] [Module ℝ Memory]

variable (B : ChiralAuditRegularityBridge Memory Flow)

/--
Benign chiral residue induces global regularity once the Hestenes--Krein
regularity bridge is installed.
-/
theorem global_regular_of_benign
    (R : ChiralResidue Memory)
    (hR : IsBenign B.context R) :
    B.backend.GloballyRegular (B.backend.flowOf R) :=
  B.backend.globallyRegular_of_regularizing
    (B.regularizing_of_benign R hR)

/--
Obstructed chiral residue induces non-regularity once the Hestenes--Krein
regularity bridge is installed.
-/
theorem not_global_regular_of_obstructed
    (R : ChiralResidue Memory)
    (hR : IsObstructed B.context R) :
    ¬ B.backend.GloballyRegular (B.backend.flowOf R) :=
  B.backend.not_globallyRegular_of_obstructing
    (B.obstructing_of_obstructed R hR)

/--
A benign audit verdict gives global regularity, witness-gated by the installed
regularity bridge.
-/
theorem global_regular_of_audit_benign
    (R : ChiralResidue Memory)
    (hAudit :
      audit B.context R = ChiralAuditVerdict.benign) :
    B.backend.GloballyRegular (B.backend.flowOf R) := by
  apply B.global_regular_of_benign R
  exact (B.context.audit_benign_iff R).mp hAudit

/--
An obstructed audit verdict gives non-regularity, witness-gated by the installed
regularity bridge.
-/
theorem not_global_regular_of_audit_obstructed
    (R : ChiralResidue Memory)
    (hAudit :
      audit B.context R = ChiralAuditVerdict.obstructed) :
    ¬ B.backend.GloballyRegular (B.backend.flowOf R) := by
  apply B.not_global_regular_of_obstructed R
  exact (B.context.audit_obstructed_iff R).mp hAudit

end ChiralAuditRegularityBridge

end InfoGeometry.OperatorAlgebra.ChiralResidueAudit

