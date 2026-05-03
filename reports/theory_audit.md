# Theory Audit Report

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

Generated: 2026-04-20 21:41:15Z

## Build toolchain status
- lake: available (/home/goutev/.elan/bin/lake)
```bash
Lake version 5.0.0-src+7e01a1b (Lean version 4.28.0)
```

## Placeholder proof debt (sorry/admit)

```text
lean/InfoGeometry/Meta/Admission.lean:141:      mkAdmissionReason syntheticDecl "trust.sorry" "error"
lean/InfoGeometry/Meta/StrictDef.lean:18:  , ``Lean.Parser.Term.«sorry»
lean/InfoGeometry/Meta/StrictDef.lean:31:      "strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its type."
lean/InfoGeometry/Meta/StrictDef.lean:34:      "strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its value."
lean/InfoGeometry/Meta/StrictDef.lean:291:It accepts only ordinary `def` syntax and rejects tactic blocks, `sorry`, and
lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean:18:It does not depend on the sorry-equivalent modular spinor layer.
lean/InfoGeometry/Canonical/OperatorPenroseUnification.lean:118:/-- Junction 5: spinor-modular identification without sorry-equivalent layer. -/
lean/InfoGeometry/Canonical/GaugeGroups.lean:14:Dead declarations (`SU2N`, `block_embedding_*`) removed — sorry-equivalent
lean/InfoGeometry/Canonical/GaugeGroups.lean:15:with zero external consumers. See `reports/dag/sorry-equivalence.md`.
lean/InfoGeometry/Canonical/ModularSpinorBridge.lean:26:**Classification: sorry-equivalent (dead-endpoint)**
lean/InfoGeometry/Canonical/ModularSpinorBridge.lean:30:`sorry` would not break any external build. See `reports/dag/sorry-equivalence.md`.
```

- Total placeholder occurrences in canonical tree: 11

## Axiom declarations

```text
```
- Total explicit axiom declarations: 0

## Namespace audit

```text
[audit] Project namespace: InfoGeometry
[audit] Scanning root:       ./lean/InfoGeometry

[audit] Files with namespace InfoGeometry*: 826
[audit] Files missing namespace InfoGeometry*: 4

=== Missing namespace InfoGeometry ===
./lean/InfoGeometry/Audit.lean
./lean/InfoGeometry/Canonical/Positivity.lean
./lean/InfoGeometry/Generated.lean
./lean/InfoGeometry/auto_blueprints.lean

=== Files declaring a non-InfoGeometry namespace (heuristic) ===

=== Namespace prefix histogram (first namespace line per file) ===
    841 InfoGeometry
     11 CertifiedInverseKernel
     10 SymmetricLieAlgebra
      7 ConformalInference
      6 CertifiedConformalInference
      5 RealSplitKreinKasparovCycle
      4 PositiveMeasure
      4 IsDrazinInverse
      4 InverseKernel
      3 ProjectivePrequantumBundle
      3 Projective
      3 IsMoorePenroseInverse
      3 GeometricQuantumTensor
      3 Canonical
      2 YangMillsMassGapBridge
      2 WeylGaugeField
      2 TransformerBlock
      2 StarCertifiedConformalInference
      2 ResidueContourHolonomyData
      2 RealSplitKreinUnboundedCycle
      2 RealMajoranaDatum
      2 PrequantumData
      2 PolarizedMajorana
      2 PolarizedDoubledAmplitude
      2 ModularRadonNikodymData
      2 MetriplecticContext
      2 LogPotential
      2 LogGenerator
      2 KreinSpace
      2 KreinGradedModule

[audit] Done.
```

## Orphaned Lean file audit

```text
[orphaned-check] Orphaned top-level Lean file in lean/: Agent.lean
```

## Quarantine Boundary Audit

```text
Quarantine import boundary check passed.
```

## Exact Constructivity Audit

```text
```

## Review-Only Surrogate Audit

```text
```

## Notes
- This report is static when lake is unavailable; full proof checking requires successful lake build.
