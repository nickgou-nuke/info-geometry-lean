import InfoGeometry.Canonical.TomitaTakesakiRealification
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.TomitaTakesakiRealification

structure ThreeBucketAudit where
  bucket1ClosedFiniteTheorems : List Lean.Name
  bucket2ConditionalTheoremsFromExplicitWitnesses : List Lean.Name
  bucket3OpenClosureDebt : List String

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
-/
def bucket1ClosedFiniteTheorems : List Lean.Name :=
  [ ``kms_to_colimitBoundary_realification
  , ``connes_cocycle_to_souriau_realification
  ]

/-
#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems that compile from explicit theorem hypotheses or imported premises.]
-/
def bucket2ConditionalTheoremsFromExplicitWitnesses : List Lean.Name :=
  [ ``polar_to_kraus_realification
  , ``modular_automorphism_to_rotorFlow_realification
  ]

/-
#### BUCKET 3: OPEN CLOSURE DEBT
[Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]
-/
def bucket3OpenClosureDebt : List String :=
  [ "StandardSubspace.isStandard: prove standardness from a native standard-subspace construction"
  , "SpatialTomitaData.*_readback: construct Tomita polar data rather than projecting laws from fields"
  , "RealVonNeumannAlgebraData.weakly_closed: prove weak closure from a native operator-algebra carrier"
  , "RealTomitaAlgebraicData.*: prove cyclic, separating, modular automorphism, and J0 transport laws"
  , "SpatialAlgebraicRealificationBridge.*: prove realification transport from the spatial/algebraic construction"
  , "HestenesGeometricComplexData.* and KreinAdjointSocket.kreinAdjoint_involutive: construct Clifford reversion/Krein symmetry"
  , "CausalConeProjectorRegularization.*: prove Drazin/Moore-Penrose idempotence and splitting laws"
  , "FiveGradedConformalClosureSocket.*: prove five-grade support, bracket, and Levi/parabolic laws"
  , "MobiusLogScaleReflectionSocket.*: prove inversion, radial, log-scale, and unit-boundary laws"
  , "CompactifiedNullConeSocket.*: prove null-pairing, embedding, and origin/infinity swap laws"
  ]

def tomitaThreeBucketAudit : ThreeBucketAudit where
  bucket1ClosedFiniteTheorems := bucket1ClosedFiniteTheorems
  bucket2ConditionalTheoremsFromExplicitWitnesses := bucket2ConditionalTheoremsFromExplicitWitnesses
  bucket3OpenClosureDebt := bucket3OpenClosureDebt

end InfoGeometry.Canonical.TomitaTakesakiRealification
