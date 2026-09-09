import Lean
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Arithmetic.RiemannZetaEvidenceCorridor

/-!
# Audited Riemann-zeta theorem/evidence ladder

This ledger encodes the epistemic boundary of the chain

`primes → Euler product → zeta → analytic continuation → functional equation
 → critical strip → critical line → spectral operator → Hilbert--Pólya
 → zeros → explicit formula → trace formula → random matrices → GUE statistics
 → evidence without proof`.

Only declarations with actual theorem owners are marked theorem-like.  The
Hilbert--Pólya identification, full explicit formula, and GUE asymptotics remain
explicitly outside the proved corridor.
-/

open Lean Elab Command

namespace InfoGeometry.Arithmetic.RiemannZetaEvidenceLogosMap

inductive Status where
  | theorem
  | finiteConditional
  | structuralEvidence
  | numericalEvidence
  | openDebt
  | evidenceBoundary
  deriving DecidableEq, Repr, Inhabited

inductive Concept where
  | primes
  | eulerProduct
  | zetaFunction
  | analyticContinuation
  | functionalEquation
  | criticalStrip
  | criticalLine
  | spectralOperator
  | hilbertPolya
  | criticalLineZeros
  | explicitFormula
  | traceFormula
  | randomMatrices
  | gueStatistics
  | evidenceWithoutProof
  deriving DecidableEq, Repr, Inhabited

structure Entry where
  concept : Concept
  phrase : String
  status : Status
  owner : Option Name
  boundary : String
  deriving Repr, Inhabited

open InfoGeometry.Arithmetic.RiemannZetaEvidenceCorridor

def allConcepts : List Concept :=
  [ .primes
  , .eulerProduct
  , .zetaFunction
  , .analyticContinuation
  , .functionalEquation
  , .criticalStrip
  , .criticalLine
  , .spectralOperator
  , .hilbertPolya
  , .criticalLineZeros
  , .explicitFormula
  , .traceFormula
  , .randomMatrices
  , .gueStatistics
  , .evidenceWithoutProof
  ]


def entry : Concept → Entry
  | .primes =>
      ⟨.primes,
        "finite prime arithmetic entrance",
        .theorem,
        some ``finite_prime_entrance,
        "A finite exact prime-counting theorem is owned; infinitude/distribution is not inferred from this node."⟩
  | .eulerProduct =>
      ⟨.eulerProduct,
        "prime Euler product equals Riemann zeta on Re(s)>1",
        .theorem,
        some ``primeEulerProduct_eq_zeta,
        "This is the genuine infinite Euler product on the absolute-convergence half-plane."⟩
  | .zetaFunction =>
      ⟨.zetaFunction,
        "Dirichlet series agrees with Mathlib riemannZeta on Re(s)>1",
        .theorem,
        some ``dirichletSeries_eq_zeta,
        "The equality identifies the original Dirichlet series with the global Mathlib zeta object on their common domain."⟩
  | .analyticContinuation =>
      ⟨.analyticContinuation,
        "global zeta is complex differentiable away from its pole at 1",
        .theorem,
        some ``riemannZeta_differentiable_off_one,
        "This is the repository-facing analytic-continuation surface; it does not reconstruct Mathlib's continuation from scratch."⟩
  | .functionalEquation =>
      ⟨.functionalEquation,
        "completed zeta satisfies s ↦ 1-s functional equation",
        .theorem,
        some ``completed_zeta_functional_equation,
        "Exact completed-zeta symmetry."⟩
  | .criticalStrip =>
      ⟨.criticalStrip,
        "critical strip is reflection invariant",
        .theorem,
        some ``critical_strip_reflection,
        "Geometric strip invariance only; no zero-location conclusion."⟩
  | .criticalLine =>
      ⟨.criticalLine,
        "critical line is the fixed locus of s ↦ 1-star(s)",
        .theorem,
        some ``critical_line_fixed_locus,
        "Exact coordinate characterization of Re(s)=1/2."⟩
  | .spectralOperator =>
      ⟨.spectralOperator,
        "finite zeta-twisted Hestenes-Krein operator is self-adjoint on the critical line",
        .finiteConditional,
        some ``finiteCriticalLine_selfAdjoint,
        "Requires the explicit finite prime-lattice packet hypotheses; it is not an operator whose spectrum is proved to equal all zeta zeros."⟩
  | .hilbertPolya =>
      ⟨.hilbertPolya,
        "self-adjoint operator with spectrum exactly the nontrivial zero ordinates",
        .openDebt,
        none,
        "The Hilbert--Pólya identification remains conjectural; finite self-adjoint lattice theorems do not close this edge."⟩
  | .criticalLineZeros =>
      ⟨.criticalLineZeros,
        "critical-line real readout zeros equal Xi zeros at 1/2+it",
        .theorem,
        some ``actualXi_criticalLine_zero_iff,
        "Exact zero correspondence on the line; it does not assert that every nontrivial zero is on the line."⟩
  | .explicitFormula =>
      ⟨.explicitFormula,
        "Riemann-Weil explicit formula linking primes and all nontrivial zeros",
        .openDebt,
        none,
        "No full native explicit-formula owner is promoted by this corridor."⟩
  | .traceFormula =>
      ⟨.traceFormula,
        "finite Riemann-Weil prime-orbit/phase trace shadow",
        .structuralEvidence,
        some ``finite_riemann_weil_trace_packet,
        "Positive prime weights, unitary prime phases, repetition multiplicativity and even spectral modes are proved, but not the full explicit/trace formula."⟩
  | .randomMatrices =>
      ⟨.randomMatrices,
        "random-matrix comparison with zeta-zero statistics",
        .numericalEvidence,
        none,
        "Repository scripts contain numerical comparisons; no asymptotic random-matrix theorem is promoted here."⟩
  | .gueStatistics =>
      ⟨.gueStatistics,
        "Montgomery-Odlyzko/GUE local spacing statistics",
        .numericalEvidence,
        none,
        "Evidence and conjectural correspondence only; not a kernel theorem in this lane."⟩
  | .evidenceWithoutProof =>
      ⟨.evidenceWithoutProof,
        "strong arithmetic/spectral/statistical evidence without RH proof",
        .evidenceBoundary,
        none,
        "The ladder terminates explicitly before any Riemann-Hypothesis conclusion."⟩


def auditRiemannZetaEvidenceLogos : CoreM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  for c in allConcepts do
    let e := entry c
    match e.status, e.owner with
    | .theorem, some n
    | .finiteConditional, some n
    | .structuralEvidence, some n =>
        unless env.contains n do
          failures := failures.push s!"missing theorem/evidence owner {n} for {repr c}"
    | .theorem, none
    | .finiteConditional, none
    | .structuralEvidence, none =>
        failures := failures.push s!"theorem-like Riemann-zeta node has no owner: {repr c}"
    | .numericalEvidence, none
    | .openDebt, none
    | .evidenceBoundary, none => pure ()
    | .numericalEvidence, some n
    | .openDebt, some n
    | .evidenceBoundary, some n =>
        failures := failures.push s!"non-theorem node unexpectedly names theorem owner {n}: {repr c}"
  if failures.isEmpty then
    logInfo m!"Riemann-zeta evidence Logos audit PASS: {allConcepts.length} concepts."
  else
    for failure in failures do
      logError m!"RIEMANN-ZETA EVIDENCE LOGOS FAILURE: {failure}"
    throwError "Riemann-zeta evidence Logos audit failed"

elab "#audit_riemann_zeta_evidence_logos" : command =>
  Command.liftCoreM auditRiemannZetaEvidenceLogos

attribute [spine_object] Concept Entry

end InfoGeometry.Arithmetic.RiemannZetaEvidenceLogosMap

