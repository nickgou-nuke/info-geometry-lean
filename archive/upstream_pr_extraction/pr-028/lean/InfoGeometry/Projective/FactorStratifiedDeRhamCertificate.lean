import Mathlib.Tactic
import InfoGeometry.Projective.NonIsoConf3RankIngestion

/-!
# Factor-stratified de Rham certificate shell

This file records the currently observed external audit surface for
`f = q(a) q(b) q(a-b)` in ambient dimension `8`.

It is theorem-honest:
- the Singular/Macaulay2 outputs are stored as plain data;
- arithmetic consequences of that data are proved in Lean;
- de Rham closure is *not* claimed unless the external lanes actually return it.
-/

namespace InfoGeometry.Projective.FactorStratifiedDeRhamCertificate

open InfoGeometry.Projective.NonIsoConf3RankIngestion
open Polynomial

/-! ## Exact arithmetic shadows of the verified external packets -/

/-- The exact quadratic Bernstein-Sato polynomial observed for each individual factor. -/
noncomputable def factorBernsteinPoly : ℤ[X] := X ^ 2 + 3 * X + 2

/-- The exact cubic Bernstein-Sato polynomial observed for the three-factor ideal. -/
noncomputable def generalBernsteinPoly : ℤ[X] := X ^ 3 + 10 * X ^ 2 + 33 * X + 36

/-- The exact finite-field complement count polynomial recorded by the audit. -/
def complementCountPoly (p : ℤ) : ℤ :=
  p ^ 8 - 3 * p ^ 7 + 7 * p ^ 5 - 4 * p ^ 4 - 4 * p ^ 3 + 3 * p ^ 2

theorem factorBernsteinPoly_factorization :
    factorBernsteinPoly = (X + 1) * (X + 2) := by
  simp [factorBernsteinPoly]
  ring

theorem generalBernsteinPoly_factorization :
    generalBernsteinPoly = (X + 3) ^ 2 * (X + 4) := by
  simp [generalBernsteinPoly]
  ring

theorem factorBernsteinPoly_eval_neg_one :
    eval (-1) factorBernsteinPoly = 0 := by
  rw [factorBernsteinPoly_factorization]
  simp

theorem factorBernsteinPoly_eval_neg_two :
    eval (-2) factorBernsteinPoly = 0 := by
  rw [factorBernsteinPoly_factorization]
  simp

theorem generalBernsteinPoly_eval_neg_three :
    eval (-3) generalBernsteinPoly = 0 := by
  rw [generalBernsteinPoly_factorization]
  simp

theorem generalBernsteinPoly_eval_neg_four :
    eval (-4) generalBernsteinPoly = 0 := by
  rw [generalBernsteinPoly_factorization]
  simp

theorem complementCountPoly_factorization (p : ℤ) :
    complementCountPoly p =
      p ^ 2 * (p - 1) ^ 2 * (p + 1) * (p ^ 3 - 2 * p ^ 2 - p + 3) := by
  unfold complementCountPoly
  ring

theorem complementCountPoly_at_three :
    complementCountPoly 3 = 1296 := by
  norm_num [complementCountPoly]

theorem complementCountPoly_at_five :
    complementCountPoly 5 = 175200 := by
  norm_num [complementCountPoly]

theorem complementCountPoly_at_seven :
    complementCountPoly 7 = 3400992 := by
  norm_num [complementCountPoly]

structure BernsteinPolynomial where
  raw : ℤ[X]
  factorized : ℤ[X]

inductive AuditStatus where
  | ok
  | timeout
  deriving DecidableEq, Repr

structure FactorStratifiedAudit where
  ambientDim : ℕ
  pairIntersectionDim : ℕ
  tripleIntersectionDim : ℕ
  singularLocusDim : ℕ
  qA : BernsteinPolynomial
  qB : BernsteinPolynomial
  qAB : BernsteinPolynomial
  generalB : BernsteinPolynomial
  fullProductStatus : AuditStatus
  degreeZeroStatus : AuditStatus
  fullDeRhamStatus : AuditStatus
  dlocalizeExtStatus : AuditStatus

/-- Codimension readback from stored ambient/stratum dimensions. -/
def pairCodim (audit : FactorStratifiedAudit) : ℕ :=
  audit.ambientDim - audit.pairIntersectionDim

/-- Triple-intersection codimension readback. -/
def tripleCodim (audit : FactorStratifiedAudit) : ℕ :=
  audit.ambientDim - audit.tripleIntersectionDim

/-- The de Rham lane is closed only when every bounded probe succeeded. -/
def DeRhamClosed (audit : FactorStratifiedAudit) : Prop :=
  audit.fullProductStatus = AuditStatus.ok ∧
    audit.degreeZeroStatus = AuditStatus.ok ∧
    audit.fullDeRhamStatus = AuditStatus.ok ∧
    audit.dlocalizeExtStatus = AuditStatus.ok

/-- Observed factor-level Bernstein-Sato / Singular data from the bounded audit. -/
noncomputable def observedAudit : FactorStratifiedAudit where
  ambientDim := 8
  pairIntersectionDim := 6
  tripleIntersectionDim := 5
  singularLocusDim := 6
  qA := { raw := factorBernsteinPoly, factorized := (X + 1) * (X + 2) }
  qB := { raw := factorBernsteinPoly, factorized := (X + 1) * (X + 2) }
  qAB := { raw := factorBernsteinPoly, factorized := (X + 1) * (X + 2) }
  generalB := { raw := generalBernsteinPoly, factorized := (X + 3) ^ 2 * (X + 4) }
  fullProductStatus := AuditStatus.timeout
  degreeZeroStatus := AuditStatus.timeout
  fullDeRhamStatus := AuditStatus.timeout
  dlocalizeExtStatus := AuditStatus.timeout

theorem observedAudit_pairCodim :
    pairCodim observedAudit = 2 := by
  rfl

theorem observedAudit_tripleCodim :
    tripleCodim observedAudit = 3 := by
  rfl

theorem observedAudit_singularLocusCodim :
    observedAudit.ambientDim - observedAudit.singularLocusDim = 2 := by
  rfl

theorem observedAudit_factorizations :
    observedAudit.qA.factorized = (X + 1) * (X + 2) ∧
    observedAudit.qB.factorized = (X + 1) * (X + 2) ∧
    observedAudit.qAB.factorized = (X + 1) * (X + 2) ∧
    observedAudit.generalB.factorized = (X + 3) ^ 2 * (X + 4) := by
  simp [observedAudit]

theorem observedAudit_not_closed :
    ¬ DeRhamClosed observedAudit := by
  simp [DeRhamClosed, observedAudit]

theorem observedAudit_fullProduct_timeout :
    observedAudit.fullProductStatus = AuditStatus.timeout := by
  rfl

theorem observedAudit_degreeZero_timeout :
    observedAudit.degreeZeroStatus = AuditStatus.timeout := by
  rfl

theorem observedAudit_fullDeRham_timeout :
    observedAudit.fullDeRhamStatus = AuditStatus.timeout := by
  rfl

theorem observedAudit_dlocalizeExt_timeout :
    observedAudit.dlocalizeExtStatus = AuditStatus.timeout := by
  rfl

/-- The current external audit can coexist with the existing rank-8 local fixture,
but it does not prove that fixture. -/
theorem candidateFixture_still_arithmetically_consistent :
    RankDataConsistent candidateLocalBettiData :=
  candidateLocalBettiData_consistent

/-- If a future external lane returns the current candidate local fixture, the
existing spin-tiling arithmetic lemma still yields total rank `32`.
This is conditional on that future return, not a claim that it has happened.
-/
theorem future_candidateFixture_spinTiled_rank32 :
    candidateLocalBettiData.totalRank * PenroseSpinTiling.spinTilingMultiplicity = 32 :=
  candidateLocalBettiData_spinTiled_rank32

end InfoGeometry.Projective.FactorStratifiedDeRhamCertificate
