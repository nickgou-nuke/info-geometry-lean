import InfoGeometry.Canonical.CantorSplitNullBridge

/-!
# Finite Cantor/split-null external audit bridge

This file records the bounded external-tool status for the finite Cantor/split-null
bridge.

Closed here:
- explicit audit-status data for the external lanes actually run;
- exact readback of the observed `ok` / `timeout` statuses;
- a theorem-safe separation between the verified finite bridge and the timed-out
  Macaulay2 `deRham(0,q)` lane.

Not closed here:
- no theorem that the timed-out Macaulay2 D-module lane computed a full de Rham
  certificate;
- no upgrade from these finite audits to a global Cantor-colimit or GNS-quotient
  closure theorem.
-/

namespace InfoGeometry.Canonical.CantorSplitNullExternalAudit

open InfoGeometry.Canonical.CantorSplitNullBridge
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

inductive AuditStatus where
  | ok
  | timeout
  | missing
  | error
  deriving DecidableEq, Repr

inductive ExternalEngine where
  | macaulay2SingularLocus
  | macaulay2Derham0
  | sageGap
  | sympy
  | clifford
  | galgebra
  deriving DecidableEq, Repr

/-- Minimal readback for one bounded external lane. -/
structure ExternalAuditLane where
  engine : ExternalEngine
  status : AuditStatus
  isVerified : Bool

/-- Explicitly marked verified finite lane. -/
def Verified (lane : ExternalAuditLane) : Prop :=
  lane.isVerified = true

/-- Macaulay2 with explicit `Dmodules` load reached the singular-locus readback. -/
def observedMacaulay2SingularLocus : ExternalAuditLane where
  engine := ExternalEngine.macaulay2SingularLocus
  status := AuditStatus.ok
  isVerified := true

/-- Bounded `deRham(0,q)` timed out and is therefore unverified. -/
def observedMacaulay2Derham0 : ExternalAuditLane where
  engine := ExternalEngine.macaulay2Derham0
  status := AuditStatus.timeout
  isVerified := false

/-- Sage/GAP lane completed the finite hyperbolic-pair readback. -/
def observedSageGap : ExternalAuditLane where
  engine := ExternalEngine.sageGap
  status := AuditStatus.ok
  isVerified := true

/-- SymPy lane completed the finite split-null readback. -/
def observedSymPy : ExternalAuditLane where
  engine := ExternalEngine.sympy
  status := AuditStatus.ok
  isVerified := true

/-- clifford lane completed the split `Cl(4,4)` null-vector readback. -/
def observedClifford : ExternalAuditLane where
  engine := ExternalEngine.clifford
  status := AuditStatus.ok
  isVerified := true

/-- galgebra lane completed the split `Cl(4,4)` null-vector readback. -/
def observedGalgebra : ExternalAuditLane where
  engine := ExternalEngine.galgebra
  status := AuditStatus.ok
  isVerified := true

@[simp] theorem observedMacaulay2SingularLocus_verified :
    Verified observedMacaulay2SingularLocus := by
  rfl

@[simp] theorem observedSageGap_verified :
    Verified observedSageGap := by
  rfl

@[simp] theorem observedSymPy_verified :
    Verified observedSymPy := by
  rfl

@[simp] theorem observedClifford_verified :
    Verified observedClifford := by
  rfl

@[simp] theorem observedGalgebra_verified :
    Verified observedGalgebra := by
  rfl

theorem observedMacaulay2Derham0_not_verified :
    ¬ Verified observedMacaulay2Derham0 := by
  simp [Verified, observedMacaulay2Derham0]

/-- Exact status packet matching the observed external runs. -/
theorem observed_external_audit_packet :
    observedMacaulay2SingularLocus.status = AuditStatus.ok ∧
      observedMacaulay2Derham0.status = AuditStatus.timeout ∧
      observedSageGap.status = AuditStatus.ok ∧
      observedSymPy.status = AuditStatus.ok ∧
      observedClifford.status = AuditStatus.ok ∧
      observedGalgebra.status = AuditStatus.ok ∧
      Verified observedMacaulay2SingularLocus ∧
      ¬ Verified observedMacaulay2Derham0 ∧
      Verified observedSageGap ∧
      Verified observedSymPy ∧
      Verified observedClifford ∧
      Verified observedGalgebra := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    observedMacaulay2SingularLocus_verified,
    observedMacaulay2Derham0_not_verified,
    observedSageGap_verified,
    observedSymPy_verified,
    observedClifford_verified,
    observedGalgebra_verified⟩

/-- Honest finite package: the external-lane status packet plus the kernel-checked
Cantor/split-null bridge for the root address. -/
theorem finite_audit_plus_bridge_packet :
    observedMacaulay2Derham0.status = AuditStatus.timeout ∧
      ¬ Verified observedMacaulay2Derham0 ∧
      detZ (addressNullGenerator
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child
          ([] : FiniteBinaryWord) false)) = 0 ∧
      detZ (addressNullGenerator
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child
          ([] : FiniteBinaryWord) true)) = 0 ∧
      polarZ (addressNullGenerator
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child
          ([] : FiniteBinaryWord) false))
          (addressNullGenerator
            (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child
              ([] : FiniteBinaryWord) true)) = -1 := by
  refine ⟨rfl, observedMacaulay2Derham0_not_verified, ?_, ?_, ?_⟩
  · simpa using addressNullGenerator_child_detZ_zero ([] : FiniteBinaryWord) false
  · simpa using addressNullGenerator_child_detZ_zero ([] : FiniteBinaryWord) true
  · simpa using child_false_true_polar_pair ([] : FiniteBinaryWord)

end InfoGeometry.Canonical.CantorSplitNullExternalAudit
