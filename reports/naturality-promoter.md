# Naturality Promotion Report

- module: `InfoGeometry.Canonical.All`
- namespace: `InfoGeometry`
- canonical unary morphisms: `3`
- tagged functors: `8`
- lift candidates: `2`
- known lift patterns: `3`
- normalized lift patterns: `3`
- constructor candidates: `3`
- responder candidates: `3`
- signature mismatches: `0`

## Known lift patterns

- theorem: `InfoGeometry.Canonical.GeneratedFlow.along_apply`
  heads: [`InfoGeometry.Canonical.GeneratedFlow.along`]
  normalized defeq: `true`

- theorem: `InfoGeometry.Canonical.LogGenerator.generate_apply`
  heads: [`InfoGeometry.Canonical.LogGenerator.generate`]
  normalized defeq: `true`

- theorem: `InfoGeometry.Canonical.LogGenerator.generate_eq_along`
  heads: [`InfoGeometry.Canonical.GeneratedFlow.along`, `InfoGeometry.Canonical.LogGenerator.generate`]
  normalized defeq: `true`

## Lift naturality obligations

- declaration: `InfoGeometry.Canonical.GeneratedFlow.along`
  role: `lift`
  obligation: `Lift naturality`
  explicit arity: `3`
  explicit heads: [`InfoGeometry.Canonical.GeneratedFlow`, `InfoGeometry.Canonical.LogGenerator`, `_`]
  spine inputs: [`InfoGeometry.Canonical.GeneratedFlow`, `InfoGeometry.Canonical.LogGenerator`]
  result head: `_`

- declaration: `InfoGeometry.Canonical.LogGenerator.generate`
  role: `lift`
  obligation: `Lift naturality`
  explicit arity: `3`
  explicit heads: [`InfoGeometry.Canonical.LogGenerator`, `InfoGeometry.Canonical.GeneratedFlow`, `_`]
  spine inputs: [`InfoGeometry.Canonical.LogGenerator`, `InfoGeometry.Canonical.GeneratedFlow`]
  result head: `_`

## Constructor compatibility obligations

- declaration: `InfoGeometry.Canonical.DefectiveDescentLogGenerator.toLogGenerator`
  role: `constructor`
  obligation: `Constructor compatibility`
  explicit arity: `1`
  explicit heads: [`InfoGeometry.Canonical.DefectiveDescentLogGenerator`]
  spine inputs: []
  result head: `InfoGeometry.Canonical.LogGenerator`

- declaration: `InfoGeometry.Canonical.ExactDescentLogGenerator.toLogGenerator`
  role: `constructor`
  obligation: `Constructor compatibility`
  explicit arity: `1`
  explicit heads: [`InfoGeometry.Canonical.ExactDescentLogGenerator`]
  spine inputs: []
  result head: `InfoGeometry.Canonical.LogGenerator`

- declaration: `InfoGeometry.Canonical.OperatorLogGenerator.toLogGenerator`
  role: `constructor`
  obligation: `Constructor compatibility`
  explicit arity: `1`
  explicit heads: [`InfoGeometry.Canonical.OperatorLogGenerator`]
  spine inputs: []
  result head: `InfoGeometry.Canonical.LogGenerator`

## Responder compatibility obligations

- declaration: `InfoGeometry.Canonical.GeometricResponse.along`
  role: `responder`
  obligation: `Responder compatibility`
  explicit arity: `3`
  explicit heads: [`InfoGeometry.Canonical.GeometricResponse`, `InfoGeometry.Canonical.GeneratedFlow`, `_`]
  spine inputs: [`InfoGeometry.Canonical.GeometricResponse`, `InfoGeometry.Canonical.GeneratedFlow`]
  result head: `_`

- declaration: `InfoGeometry.Canonical.GeometricResponse.fromLogGenerator`
  role: `responder`
  obligation: `Responder compatibility`
  explicit arity: `4`
  explicit heads: [`InfoGeometry.Canonical.GeometricResponse`, `InfoGeometry.Canonical.GeneratedFlow`, `InfoGeometry.Canonical.LogGenerator`, `_`]
  spine inputs: [`InfoGeometry.Canonical.GeometricResponse`, `InfoGeometry.Canonical.GeneratedFlow`, `InfoGeometry.Canonical.LogGenerator`]
  result head: `_`

- declaration: `InfoGeometry.Canonical.LogGenerator.respond`
  role: `responder`
  obligation: `Responder compatibility`
  explicit arity: `4`
  explicit heads: [`InfoGeometry.Canonical.LogGenerator`, `InfoGeometry.Canonical.GeneratedFlow`, `InfoGeometry.Canonical.GeometricResponse`, `_`]
  spine inputs: [`InfoGeometry.Canonical.LogGenerator`, `InfoGeometry.Canonical.GeneratedFlow`, `InfoGeometry.Canonical.GeometricResponse`]
  result head: `_`

## Signature mismatches

<none>
