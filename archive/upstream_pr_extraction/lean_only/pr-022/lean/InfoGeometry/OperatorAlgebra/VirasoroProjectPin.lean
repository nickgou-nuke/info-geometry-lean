import Mathlib

/-!
# InfoGeometry.OperatorAlgebra.VirasoroProjectPin

Non-authoritative integration socket for the external Lean project
`kkytola/VirasoroProject`.

This file is metadata + routing only:
- records the pinned external checkout,
- records conductive-route mapping candidates,
- keeps all external claims retrieval-only unless and until local readback
  certification is added in this repository.

It does **not** import external source files into the owner theorem lane.
-/

namespace InfoGeometry.OperatorAlgebra

/-- Route status for external formalizer integration. -/
inductive ExternalRouteStatus where
  | retrievalOnly
  | conductiveOverlayCandidate
  | localReadbackCertified
  deriving DecidableEq, Repr

/-- Metadata for a pinned external Lean formalization source. -/
structure ExternalLeanProjectPin where
  repository : String
  commit : String
  localPath : String
  upstreamToolchain : String
  localToolchain : String
  rootModule : String
  deriving Repr

/-- Pinned source metadata for `kkytola/VirasoroProject`. -/
def virasoroProjectPin : ExternalLeanProjectPin where
  repository := "https://github.com/kkytola/VirasoroProject"
  commit := "555a9096c259b1608016b10d1d7b5e3bbc8d2477"
  localPath := "external_refs/VirasoroProject"
  upstreamToolchain := "leanprover/lean4:v4.27.0-rc1"
  localToolchain := "leanprover/lean4:v4.28.0"
  rootModule := "VirasoroProject"

/-- Candidate conductive-route map entry (non-authoritative metadata). -/
structure ConductiveRouteMapEntry where
  externalModule : String
  internalSocket : String
  status : ExternalRouteStatus
  deriving Repr

/--
Initial non-authoritative route map for Virasoro/Sugawara surfaces.

All entries remain overlay candidates until local readback certification exists.
-/
def virasoroConductiveRouteMap : List ConductiveRouteMapEntry :=
  [ { externalModule := "VirasoroProject.VirasoroAlgebra"
      internalSocket := "InfoGeometry.OperatorAlgebra.AffineVirasoroBridge"
      status := ExternalRouteStatus.conductiveOverlayCandidate }
  , { externalModule := "VirasoroProject.Sugawara"
      internalSocket := "InfoGeometry.OperatorAlgebra.AffineVirasoroBridge"
      status := ExternalRouteStatus.conductiveOverlayCandidate }
  , { externalModule := "VirasoroProject.WittAlgebra"
      internalSocket := "InfoGeometry.OperatorAlgebra.TKKConformalClosure"
      status := ExternalRouteStatus.conductiveOverlayCandidate }
  ]

/-- Non-empty route-map sanity check. -/
theorem virasoroConductiveRouteMap_nonempty : virasoroConductiveRouteMap ≠ [] := by
  decide

/--
Integration gate for this external source:

- pin metadata is populated,
- local checkout path is recorded,
- routes are present but not automatically promoted to owner authority.
-/
def VirasoroProjectConductiveRouteTarget : Prop :=
  virasoroProjectPin.commit ≠ "" ∧
  virasoroProjectPin.localPath = "external_refs/VirasoroProject" ∧
  virasoroConductiveRouteMap ≠ []

/-- Certified local fact that the integration gate data is populated. -/
theorem virasoroProjectConductiveRouteTarget_holds :
    VirasoroProjectConductiveRouteTarget := by
  refine ⟨?_, rfl, virasoroConductiveRouteMap_nonempty⟩
  decide

/-!
## Integration status: WITNESS BRIDGE ONLY

As of the current state of this repository, the Virasoro integration has NOT
passed the conductivity standard required for Lean proof authority.

Reasons:

1. The external project `kkytola/VirasoroProject` (pinned above) is NOT
   imported into any lean file in this repository. The `localPath` field is
   a metadata string, not a Lean import.

2. A toolchain mismatch exists:
   - upstream uses `leanprover/lean4:v4.27.0-rc1`
   - this repo uses `leanprover/lean4:v4.28.0`
   A porting pass is required before direct import is possible.

3. The local Virasoro files (`AffineVirasoroBridge.lean`,
   `ExceptionalVirasoroBridge.lean`, `SuperVirasoroExtension.lean`,
   `AffineVirasoroExceptionalBridge.lean`) define their own `VirasoroDatum`
   and `VirasoroAlgebraDatum` structures with proof-carrying hypothesis fields.
   No concrete Mathlib-rooted instance of these structures is constructed.
   All readback theorems are tautological projections of those hypothesis fields.

4. Mathlib has `Mathlib.Algebra.Lie.Loop` (Carnahan 2026) which provides
   `LieAlgebra.loopAlgebra` and `twoCocycleOfBilinear` -- the correct donors
   for the affine/Kac-Moody layer. None of the local files use these.

All route map entries remain at `conductiveOverlayCandidate`.
No entry has reached `localReadbackCertified`.

To promote to `localReadbackCertified`:
- port `kkytola/VirasoroProject` to v4.28.0, OR
- construct a concrete `VirasoroAlgebraDatum` from `LieAlgebra.loopAlgebra`
  + `twoCocycleOfBilinear` with rfl/norm_num structural fields,
- then add a readback theorem that reads a Mathlib-observable quantity from
  that concrete instance.
-/

/-- Machine-readable certification status for Virasoro integration. -/
def virasoroIntegrationStatus : ExternalRouteStatus :=
  ExternalRouteStatus.conductiveOverlayCandidate

/-- The integration has not reached local readback certification. -/
theorem virasoroIntegration_not_certified :
    virasoroIntegrationStatus ≠ ExternalRouteStatus.localReadbackCertified := by
  decide

/-- Legacy lower-camel compatibility alias. -/
theorem virasoroProjectConductiveRouteTarget :
    VirasoroProjectConductiveRouteTarget :=
  virasoroProjectConductiveRouteTarget_holds

end InfoGeometry.OperatorAlgebra
