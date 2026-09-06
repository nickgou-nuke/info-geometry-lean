import Lean
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Arithmetic.RiemannZetaGeometricDynamicsCorridor

/-!
# Extended edge-audited Riemann-zeta evidence ledger

This ledger records both concepts and directed edges for the long arithmetic →
projective → information-geometric → spectral → random-matrix pipeline.

The crucial rule is that theorem ownership of two adjacent concepts does not
promote the connecting arrow to a theorem.  Each edge receives its own status.
This prevents a chain of individually valid constructions from becoming an
implicit proof of the Riemann Hypothesis.
-/

open Lean Elab Command

namespace InfoGeometry.Arithmetic.RiemannZetaExtendedEvidenceLogosMap

inductive Status where
  | theorem
  | carrierTheorem
  | finiteConditional
  | structuralBridge
  | structuralEvidence
  | numericalEvidence
  | openDebt
  | unresolvedGlobal
  deriving DecidableEq, Repr, Inhabited

inductive Concept where
  | primeNumbers
  | arithmeticSemigroup
  | vonMangoldtWeights
  | eulerFactors
  | eulerProduct
  | dirichletSeries
  | riemannZeta
  | logarithmicDerivative
  | moebiusInversion
  | analyticContinuation
  | completedXi
  | functionalEquation
  | reflectionInvolution
  | criticalStrip
  | criticalLine
  | cayleyTransform
  | apolloniusRatioGeometry
  | distinguishedFixedPoints
  | crossRatioCoordinate
  | kleinProjectiveModel
  | kreinSplitting
  | chentsovFisherMetric
  | metriplecticDecomposition
  | hamiltonianGradientSplit
  | irrotationalGradientFlow
  | dilationFlow
  | phaseTransport
  | unitCircleEvolution
  | cylinderCompactification
  | boundaryFixedPoints
  | informationPotential
  | entropyRelativeEntropy
  | cylinderIrrotationalComponent
  | transferOperator
  | candidateSpectralOperator
  | hilbertPolya
  | spectralOrdinates
  | zetaZeros
  | zeroCountingFunction
  | weilExplicitFormula
  | vonMangoldtExplicitFormula
  | logarithmicDerivativeTrace
  | spectralTraceFormula
  | periodicOrbitExpansion
  | selbergCorrespondence
  | characteristicPolynomial
  | finiteRandomMatrix
  | unitaryHermitianEnsemble
  | pairCorrelation
  | gueUniversality
  | numericalStatisticalEvidence
  | unresolvedGlobalTheorem
  deriving DecidableEq, Repr, Inhabited

structure Edge where
  source : Concept
  target : Concept
  status : Status
  owner : Option Name
  boundary : String
  deriving Repr, Inhabited

open InfoGeometry.Arithmetic.RiemannZetaEvidenceCorridor
open InfoGeometry.Arithmetic.RiemannZetaGeometricDynamicsCorridor

/-- The requested linear order of concepts. -/
def chain : List Concept :=
  [ .primeNumbers
  , .arithmeticSemigroup
  , .vonMangoldtWeights
  , .eulerFactors
  , .eulerProduct
  , .dirichletSeries
  , .riemannZeta
  , .logarithmicDerivative
  , .moebiusInversion
  , .analyticContinuation
  , .completedXi
  , .functionalEquation
  , .reflectionInvolution
  , .criticalStrip
  , .criticalLine
  , .cayleyTransform
  , .apolloniusRatioGeometry
  , .distinguishedFixedPoints
  , .crossRatioCoordinate
  , .kleinProjectiveModel
  , .kreinSplitting
  , .chentsovFisherMetric
  , .metriplecticDecomposition
  , .hamiltonianGradientSplit
  , .irrotationalGradientFlow
  , .dilationFlow
  , .phaseTransport
  , .unitCircleEvolution
  , .cylinderCompactification
  , .boundaryFixedPoints
  , .informationPotential
  , .entropyRelativeEntropy
  , .cylinderIrrotationalComponent
  , .transferOperator
  , .candidateSpectralOperator
  , .hilbertPolya
  , .spectralOrdinates
  , .zetaZeros
  , .zeroCountingFunction
  , .weilExplicitFormula
  , .vonMangoldtExplicitFormula
  , .logarithmicDerivativeTrace
  , .spectralTraceFormula
  , .periodicOrbitExpansion
  , .selbergCorrespondence
  , .characteristicPolynomial
  , .finiteRandomMatrix
  , .unitaryHermitianEnsemble
  , .pairCorrelation
  , .gueUniversality
  , .numericalStatisticalEvidence
  , .unresolvedGlobalTheorem
  ]

/-- Sequential edges with independently audited epistemic status. -/
def edges : List Edge :=
  [ ⟨.primeNumbers, .arithmeticSemigroup, .carrierTheorem, some ``arithmeticSemigroup_mul_assoc,
      "Only the multiplicative carrier law is asserted here; unique factorization is inherited background, not reproved by this edge."⟩
  , ⟨.arithmeticSemigroup, .vonMangoldtWeights, .structuralBridge, none,
      "Mathlib owns the von Mangoldt arithmetic function, but this ledger does not claim a new categorical derivation from the semigroup carrier."⟩
  , ⟨.vonMangoldtWeights, .eulerFactors, .structuralBridge, none,
      "Prime-power support motivates local Euler data; no new equivalence theorem is asserted by adjacency."⟩
  , ⟨.eulerFactors, .eulerProduct, .structuralBridge, none,
      "The repository owns the infinite Euler product theorem; factor-to-product assembly is consumed rather than reconstructed here."⟩
  , ⟨.eulerProduct, .dirichletSeries, .theorem, some ``primeEulerProduct_eq_zeta,
      "Both presentations are identified with the same zeta object on Re(s)>1; this owner anchors the Euler side."⟩
  , ⟨.dirichletSeries, .riemannZeta, .theorem, some ``dirichletSeries_eq_zeta,
      "Exact equality on the half-plane of absolute convergence."⟩
  , ⟨.riemannZeta, .logarithmicDerivative, .theorem, some ``vonMangoldt_eq_actualZetaLogDerivative,
      "On Re(s)>1 the negative logarithmic derivative equals the von-Mangoldt L-series."⟩
  , ⟨.logarithmicDerivative, .moebiusInversion, .structuralBridge, none,
      "Both logarithmic derivative and Möbius inversion are theorem-owned arithmetic surfaces; no direct identity between these operators is asserted."⟩
  , ⟨.moebiusInversion, .analyticContinuation, .structuralBridge, none,
      "Dirichlet convolution inversion does not itself construct analytic continuation."⟩
  , ⟨.analyticContinuation, .completedXi, .theorem, some ``completed_zeta_functional_equation,
      "The completed zeta/Xi surface is consumed from Mathlib-backed analytic owners."⟩
  , ⟨.completedXi, .functionalEquation, .theorem, some ``completed_zeta_functional_equation,
      "Exact completed-zeta reflection symmetry."⟩
  , ⟨.functionalEquation, .reflectionInvolution, .theorem, some ``critical_strip_reflection,
      "The s↦1-s symmetry induces the reflected coordinate geometry."⟩
  , ⟨.reflectionInvolution, .criticalStrip, .theorem, some ``critical_strip_reflection,
      "The open critical strip is reflection invariant."⟩
  , ⟨.criticalStrip, .criticalLine, .theorem, some ``critical_line_fixed_locus,
      "The critical line is characterized as the antiunitary fixed locus; this is geometry, not RH."⟩
  , ⟨.criticalLine, .cayleyTransform, .theorem, some ``cayley_critical_line_to_unit_circle,
      "The centered imaginary axis maps exactly to the unit circle."⟩
  , ⟨.cayleyTransform, .apolloniusRatioGeometry, .theorem, some ``apollonius_unit_circle_iff_zero_leaf,
      "The native Apollonius projective ratio has an exact unit-circle/zero-leaf characterization."⟩
  , ⟨.apolloniusRatioGeometry, .distinguishedFixedPoints, .structuralBridge, none,
      "Apollonius/projective owners contain distinguished boundary data, but this exact two-fixed-point edge is not promoted here."⟩
  , ⟨.distinguishedFixedPoints, .crossRatioCoordinate, .structuralBridge, none,
      "Cross-ratio owners exist; no special zeta fixed-point cross-ratio theorem is asserted by this corridor."⟩
  , ⟨.crossRatioCoordinate, .kleinProjectiveModel, .structuralBridge, none,
      "Projective/PGL2 cross-ratio structure is native, but its identification with a unique Klein zeta model remains a structural bridge."⟩
  , ⟨.kleinProjectiveModel, .kreinSplitting, .structuralBridge, none,
      "Klein/projective and Krein owners coexist; the exact zeta-specific functorial splitting is not yet a theorem edge."⟩
  , ⟨.kreinSplitting, .chentsovFisherMetric, .structuralBridge, none,
      "The Apollonius Fisher metric is theorem-owned, but Chentsov uniqueness is a stronger independent statement."⟩
  , ⟨.chentsovFisherMetric, .metriplecticDecomposition, .structuralBridge, none,
      "Fisher and metriplectic owners are both native; no universal implication is inferred."⟩
  , ⟨.metriplecticDecomposition, .hamiltonianGradientSplit, .structuralBridge, none,
      "A Hamiltonian⊕gradient decomposition requires explicit Poisson/metric data; not supplied globally here."⟩
  , ⟨.hamiltonianGradientSplit, .irrotationalGradientFlow, .structuralBridge, none,
      "The scalar zeta gradient flow is theorem-owned, but global irrotationality on the full cylinder is not claimed."⟩
  , ⟨.irrotationalGradientFlow, .dilationFlow, .structuralBridge, none,
      "Zeta gradient and Berry--Keating dilation are separate native flows; their equality is not asserted."⟩
  , ⟨.dilationFlow, .phaseTransport, .structuralBridge, none,
      "Dilation gives additive logarithmic transport; a unique phase-transport identification requires extra data."⟩
  , ⟨.phaseTransport, .unitCircleEvolution, .theorem, some ``dilation_preserves_unit_circle,
      "The established scale-exponent chart transports dilation to the unit-circle image."⟩
  , ⟨.unitCircleEvolution, .cylinderCompactification, .structuralBridge, none,
      "Apollonius cylinder owners exist, but this edge is geometric packaging rather than a zeta theorem."⟩
  , ⟨.cylinderCompactification, .boundaryFixedPoints, .structuralBridge, none,
      "Boundary fixed-point data are not identified with all zeta spectral data."⟩
  , ⟨.boundaryFixedPoints, .informationPotential, .structuralBridge, none,
      "The nonnegative information potential is theorem-owned independently of boundary spectral identification."⟩
  , ⟨.informationPotential, .entropyRelativeEntropy, .theorem, some ``information_geometric_potential_nonnegative,
      "Exact Bregman/relative-entropy nonnegativity surface."⟩
  , ⟨.entropyRelativeEntropy, .cylinderIrrotationalComponent, .structuralBridge, none,
      "The actual zeta entropy gradient is known on beta>1, but no global critical-cylinder Helmholtz theorem is asserted."⟩
  , ⟨.cylinderIrrotationalComponent, .transferOperator, .structuralBridge, none,
      "A native Ruelle transfer operator exists; identification with the zeta cylinder gradient generator remains additional work."⟩
  , ⟨.transferOperator, .candidateSpectralOperator, .structuralEvidence, some ``uniform_transfer_preserves_one,
      "Transfer-operator normalization is proved; spectral equivalence to zeta zeros is not."⟩
  , ⟨.candidateSpectralOperator, .hilbertPolya, .finiteConditional, some ``finiteCriticalLine_selfAdjoint,
      "Finite critical-line self-adjointness is real evidence but does not produce the global Hilbert--Polya operator."⟩
  , ⟨.hilbertPolya, .spectralOrdinates, .openDebt, none,
      "No self-adjoint operator is proved to have exactly the nontrivial zero ordinates as spectrum."⟩
  , ⟨.spectralOrdinates, .zetaZeros, .theorem, some ``actualXi_criticalLine_zero_iff,
      "Exact correspondence only for ordinates already restricted to the critical line."⟩
  , ⟨.zetaZeros, .zeroCountingFunction, .openDebt, none,
      "No global native Riemann--von Mangoldt zero-counting theorem is promoted in this corridor."⟩
  , ⟨.zeroCountingFunction, .weilExplicitFormula, .openDebt, none,
      "Full Weil explicit formula remains analytic debt."⟩
  , ⟨.weilExplicitFormula, .vonMangoldtExplicitFormula, .openDebt, none,
      "The prime/zero explicit-formula identification is not closed by the existing von-Mangoldt log-derivative theorem alone."⟩
  , ⟨.vonMangoldtExplicitFormula, .logarithmicDerivativeTrace, .structuralEvidence, some ``finite_riemann_weil_trace_packet,
      "Finite prime-orbit weights and phases form a trace-shaped shadow only."⟩
  , ⟨.logarithmicDerivativeTrace, .spectralTraceFormula, .structuralEvidence, some ``finite_riemann_weil_trace_packet,
      "No equality with the full spectral trace over all zeros is claimed."⟩
  , ⟨.spectralTraceFormula, .periodicOrbitExpansion, .structuralEvidence, some ``finite_riemann_weil_trace_packet,
      "Prime powers admit periodic-orbit-shaped weights in the finite owner."⟩
  , ⟨.periodicOrbitExpansion, .selbergCorrespondence, .openDebt, none,
      "A genuine Selberg trace-formula equivalence for the zeta problem is not theorem-owned here."⟩
  , ⟨.selbergCorrespondence, .characteristicPolynomial, .structuralBridge, none,
      "Finite spectral matrices have characteristic polynomials, but no Selberg-to-zeta characteristic-polynomial theorem is asserted."⟩
  , ⟨.characteristicPolynomial, .finiteRandomMatrix, .structuralBridge, none,
      "Finite random-matrix models are evidence models, not canonical zeta operators."⟩
  , ⟨.finiteRandomMatrix, .unitaryHermitianEnsemble, .numericalEvidence, none,
      "Repository numerical scripts sample Hermitian/unitary ensembles."⟩
  , ⟨.unitaryHermitianEnsemble, .pairCorrelation, .numericalEvidence, none,
      "Finite empirical spacing/pair-correlation comparisons only."⟩
  , ⟨.pairCorrelation, .gueUniversality, .numericalEvidence, none,
      "Montgomery--Odlyzko/GUE universality is not a kernel theorem."⟩
  , ⟨.gueUniversality, .numericalStatisticalEvidence, .numericalEvidence, none,
      "Numerical agreement is evidence, not implication."⟩
  , ⟨.numericalStatisticalEvidence, .unresolvedGlobalTheorem, .unresolvedGlobal, none,
      "Terminal boundary: the accumulated arithmetic/geometric/spectral/statistical evidence does not prove RH."⟩
  ]

/-- Every listed sequential edge agrees with the requested chain order. -/
theorem edge_count_matches_chain : edges.length + 1 = chain.length := by
  decide


def auditExtendedRiemannZetaEdges : CoreM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  for e in edges do
    match e.status, e.owner with
    | .theorem, some n
    | .carrierTheorem, some n
    | .finiteConditional, some n
    | .structuralEvidence, some n =>
        unless env.contains n do
          failures := failures.push s!"missing theorem/evidence owner {n} for edge {repr e.source} -> {repr e.target}"
    | .theorem, none
    | .carrierTheorem, none
    | .finiteConditional, none
    | .structuralEvidence, none =>
        failures := failures.push s!"theorem-like edge has no owner: {repr e.source} -> {repr e.target}"
    | .structuralBridge, none
    | .numericalEvidence, none
    | .openDebt, none
    | .unresolvedGlobal, none => pure ()
    | .structuralBridge, some n
    | .numericalEvidence, some n
    | .openDebt, some n
    | .unresolvedGlobal, some n =>
        failures := failures.push s!"non-theorem edge unexpectedly names owner {n}: {repr e.source} -> {repr e.target}"
  if failures.isEmpty then
    logInfo m!"Extended Riemann-zeta edge audit PASS: {edges.length} directed edges."
  else
    for failure in failures do
      logError m!"EXTENDED RIEMANN-ZETA EDGE FAILURE: {failure}"
    throwError "extended Riemann-zeta edge audit failed"

elab "#audit_extended_riemann_zeta_edges" : command =>
  Command.liftCoreM auditExtendedRiemannZetaEdges

attribute [spine_object] Concept Edge

end InfoGeometry.Arithmetic.RiemannZetaExtendedEvidenceLogosMap
