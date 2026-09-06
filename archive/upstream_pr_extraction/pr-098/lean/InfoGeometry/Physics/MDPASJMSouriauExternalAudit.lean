import Mathlib.Tactic
import InfoGeometry.Physics.MDPASJMSouriauGlobalObstruction

/-!
# MDPAS/J.-M. Souriau external de Rham audit bridge

This file is theorem-safe and keeps the global story honest.

Closed here:
- explicit data structures for external de Rham audit status;
- exact arithmetic consistency of the observed bounded audit lanes;
- a finite global packet combining the cellular de Rham obstruction,
  finite symplectic carrier, 5D Kaluza--Klein split, spin-half integrality,
  and the inductive-limit carrier theorem.

Not closed here:
- no theorem claims that the timed-out Macaulay2/Dmodules lanes computed the
  full de Rham cohomology of the complement;
- no theorem upgrades the finite packet to a smooth global symplectic manifold;
- no theorem upgrades the finite KK/prequantum packet to full quantization.
-/

namespace InfoGeometry
namespace Physics
namespace MDPASJMSouriauExternalAudit

open InfoGeometry.Physics.MDPASJMSouriauGlobalObstruction
open InfoGeometry.Physics.MDPASJMSouriauGlobalObstruction.DirectLimitReadback
open InfoGeometry.Physics.MDPASJMSouriauDigest

inductive AuditStatus where
  | ok
  | timeout
  | missing
  | error
  deriving DecidableEq, Repr

inductive DeRhamMethod where
  | derham
  | dlocalizeExt
  deriving DecidableEq, Repr

/-- Finite data read back from a bounded external de Rham audit lane. -/
abbrev ExternalDeRhamAuditData :=
  ℕ × List ℕ × ℕ × AuditStatus × DeRhamMethod

namespace ExternalDeRhamAuditData

abbrev ambientDim (data : ExternalDeRhamAuditData) : ℕ := data.1

abbrev bettiNumbers (data : ExternalDeRhamAuditData) : List ℕ := data.2.1

abbrev totalRank (data : ExternalDeRhamAuditData) : ℕ := data.2.2.1

abbrev status (data : ExternalDeRhamAuditData) : AuditStatus := data.2.2.2.1

abbrev method (data : ExternalDeRhamAuditData) : DeRhamMethod := data.2.2.2.2

end ExternalDeRhamAuditData

/-- Arithmetic consistency for any explicit Betti-number vector carried by the audit. -/
def RankDataConsistent (data : ExternalDeRhamAuditData) : Prop :=
  data.totalRank = data.bettiNumbers.sum

/-- The complement under audit lives in eight affine coordinates `(a,b) ∈ Q^8`. -/
def HasAmbientDimension8 (data : ExternalDeRhamAuditData) : Prop :=
  data.ambientDim = 8

/-- Verification is determined by the native audit status, not a Boolean marker. -/
def Verified (data : ExternalDeRhamAuditData) : Prop :=
  data.status = AuditStatus.ok

/-- Observed bounded Macaulay2 `deRham(0, f)` lane: attempted, timed out, unverified. -/
def observedDegree0Audit : ExternalDeRhamAuditData :=
  (8, [], 0, AuditStatus.timeout, DeRhamMethod.derham)

/-- Observed bounded Macaulay2 full `deRham(f)` lane: attempted, timed out, unverified. -/
def observedFullDerhamAudit : ExternalDeRhamAuditData :=
  (8, [], 0, AuditStatus.timeout, DeRhamMethod.derham)

/-- Observed bounded Macaulay2 `Dlocalize + rationalFunctionExt` lane: attempted, timed out. -/
def observedDlocalizeExtAudit : ExternalDeRhamAuditData :=
  (8, [], 0, AuditStatus.timeout, DeRhamMethod.dlocalizeExt)

@[simp] theorem observedDegree0Audit_consistent :
    RankDataConsistent observedDegree0Audit := by
  rfl

@[simp] theorem observedFullDerhamAudit_consistent :
    RankDataConsistent observedFullDerhamAudit := by
  rfl

@[simp] theorem observedDlocalizeExtAudit_consistent :
    RankDataConsistent observedDlocalizeExtAudit := by
  rfl

@[simp] theorem observedDegree0Audit_ambient :
    HasAmbientDimension8 observedDegree0Audit := by
  rfl

@[simp] theorem observedFullDerhamAudit_ambient :
    HasAmbientDimension8 observedFullDerhamAudit := by
  rfl

@[simp] theorem observedDlocalizeExtAudit_ambient :
    HasAmbientDimension8 observedDlocalizeExtAudit := by
  rfl

/--
The currently observed bounded Macaulay2 lanes are explicit timeout markers,
not verified cohomology certificates.
-/
theorem observed_timeout_audit_packet :
    observedDegree0Audit.status = AuditStatus.timeout ∧
      observedFullDerhamAudit.status = AuditStatus.timeout ∧
      observedDlocalizeExtAudit.status = AuditStatus.timeout ∧
      ¬ Verified observedDegree0Audit ∧
      ¬ Verified observedFullDerhamAudit ∧
      ¬ Verified observedDlocalizeExtAudit := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simp [Verified, observedDegree0Audit]
  constructor
  · simp [Verified, observedFullDerhamAudit]
  · simp [Verified, observedDlocalizeExtAudit]

/-- Any verified external property carries its rank arithmetic by projection. -/
theorem verified_property_rank_readback
    (data : ExternalDeRhamAuditData)
    (hconsistent : RankDataConsistent data) :
    ∃ bVals : List ℕ,
      data.bettiNumbers = bVals ∧ data.totalRank = bVals.sum := by
  exact ⟨data.bettiNumbers, rfl, hconsistent⟩

/--
Finite theorem-safe packet for the global story: obstruction, symplectic,
Kaluza--Klein, prequantization, and inductive-limit carrier existence.
-/
theorem finite_global_story_packet
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {Op : Type*} [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]
    {State LieAlgebra LieDual : Type*} [AddMonoid LieAlgebra]
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) :
    ¬ Exact2 sphereArea ∧
      omega2 e0 e1 = 1 ∧
      omega2 e1 e0 = -1 ∧
      kk5Quadratic (fun i => if i = 0 then (1 : ℚ) else 0) = 1 ∧
      PrequantizationIntegral ((1 : ℚ) / 2) 1 ∧
      Nonempty (FiniteMDPASJMDirectSystem.DirectLimitCarrier T) := by
  refine ⟨sphereArea_not_exact, ?_, ?_, ?_, ?_, ?_⟩
  · simp [omega2, e0, e1]
  · simp [omega2, e0, e1]
  · simp [kk5Quadratic]
  · simpa using spin_half_integral_prequantization (1 : ℚ)
  · exact (mdpas_direct_limit_theorem T).1

end MDPASJMSouriauExternalAudit
end Physics
end InfoGeometry
