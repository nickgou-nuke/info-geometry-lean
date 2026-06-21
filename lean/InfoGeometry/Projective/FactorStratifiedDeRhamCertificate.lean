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

structure BernsteinPolynomial where
  raw : String
  factorized : String

structure FactorStratifiedAudit where
  ambientDim : ℕ
  pairIntersectionDim : ℕ
  tripleIntersectionDim : ℕ
  singularLocusDim : ℕ
  qA : BernsteinPolynomial
  qB : BernsteinPolynomial
  qAB : BernsteinPolynomial
  generalB : BernsteinPolynomial
  fullProductStatus : String
  degreeZeroStatus : String
  fullDeRhamStatus : String
  dlocalizeExtStatus : String

/-- Codimension readback from stored ambient/stratum dimensions. -/
def pairCodim (audit : FactorStratifiedAudit) : ℕ :=
  audit.ambientDim - audit.pairIntersectionDim

/-- Triple-intersection codimension readback. -/
def tripleCodim (audit : FactorStratifiedAudit) : ℕ :=
  audit.ambientDim - audit.tripleIntersectionDim

/-- The de Rham lane is closed only when every bounded probe succeeded. -/
def DeRhamClosed (audit : FactorStratifiedAudit) : Prop :=
  audit.fullProductStatus = "ok" ∧
    audit.degreeZeroStatus = "ok" ∧
    audit.fullDeRhamStatus = "ok" ∧
    audit.dlocalizeExtStatus = "ok"

/-- Observed factor-level Bernstein-Sato / Singular data from the bounded audit. -/
def observedAudit : FactorStratifiedAudit where
  ambientDim := 8
  pairIntersectionDim := 6
  tripleIntersectionDim := 5
  singularLocusDim := 6
  qA := { raw := "s^2+3*s+2", factorized := "(s+1)*(s+2)" }
  qB := { raw := "s^2+3*s+2", factorized := "(s+1)*(s+2)" }
  qAB := { raw := "s^2+3*s+2", factorized := "(s+1)*(s+2)" }
  generalB := { raw := "s^3+10*s^2+33*s+36", factorized := "(s+3)^2*(s+4)" }
  fullProductStatus := "timeout"
  degreeZeroStatus := "timeout"
  fullDeRhamStatus := "timeout"
  dlocalizeExtStatus := "timeout"

theorem observedAudit_pairCodim :
    pairCodim observedAudit = 2 := by
  rfl

theorem observedAudit_tripleCodim :
    tripleCodim observedAudit = 3 := by
  rfl

theorem observedAudit_singularLocusCodim :
    observedAudit.ambientDim - observedAudit.singularLocusDim = 2 := by
  rfl

theorem observedAudit_factorStrings :
    observedAudit.qA.factorized = "(s+1)*(s+2)" ∧
    observedAudit.qB.factorized = "(s+1)*(s+2)" ∧
    observedAudit.qAB.factorized = "(s+1)*(s+2)" ∧
    observedAudit.generalB.factorized = "(s+3)^2*(s+4)" := by
  simp [observedAudit]

theorem observedAudit_not_closed :
    ¬ DeRhamClosed observedAudit := by
  simp [DeRhamClosed, observedAudit]

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
