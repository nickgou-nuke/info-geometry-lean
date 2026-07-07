import Mathlib
import InfoGeometry.External.Virasoro.VirasoroAlgebra

/-!
# InfoGeometry.OperatorAlgebra.VirasoroProjectPin

Integration socket for the external Lean project `kkytola/VirasoroProject`.

This file is metadata + routing only:
- records the pinned external checkout,
- records conductive-route mapping candidates,
- records that the upstream source has been vendored and ported to the local
  Lean toolchain,
- exposes a tiny local readback certificate against the imported Virasoro
  implementation.

The proof authority remains in `InfoGeometry.External.Virasoro`, which is the
ported in-repository copy of `kkytola/VirasoroProject`.
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
  localPath := "lean/InfoGeometry/External/Virasoro"
  upstreamToolchain := "leanprover/lean4:v4.27.0-rc1"
  localToolchain := "leanprover/lean4:v4.28.0"
  rootModule := "InfoGeometry.External.Virasoro"

/-- Candidate conductive-route map entry (non-authoritative metadata). -/
structure ConductiveRouteMapEntry where
  externalModule : String
  internalSocket : String
  status : ExternalRouteStatus
  deriving Repr

/--
Route map for the vendored Virasoro/Sugawara surfaces.
-/
def virasoroConductiveRouteMap : List ConductiveRouteMapEntry :=
  [ { externalModule := "VirasoroProject.VirasoroAlgebra"
      internalSocket := "InfoGeometry.OperatorAlgebra.AffineVirasoroBridge"
      status := ExternalRouteStatus.localReadbackCertified }
  , { externalModule := "VirasoroProject.Sugawara"
      internalSocket := "InfoGeometry.OperatorAlgebra.AffineVirasoroBridge"
      status := ExternalRouteStatus.localReadbackCertified }
  , { externalModule := "VirasoroProject.WittAlgebra"
      internalSocket := "InfoGeometry.OperatorAlgebra.TKKConformalClosure"
      status := ExternalRouteStatus.localReadbackCertified }
  ]

/-- Non-empty route-map sanity check. -/
theorem virasoroConductiveRouteMap_nonempty : virasoroConductiveRouteMap ≠ [] := by
  decide

/-!
## Integration status: LOCAL READBACK CERTIFIED

The external project `kkytola/VirasoroProject` is vendored under
`InfoGeometry.External.Virasoro` and builds on the repository toolchain
`leanprover/lean4:v4.28.0`.

This status is deliberately narrow: it certifies that the VirasoroProject
implementation is imported and usable natively from this repository. It does
not turn every downstream affine/Sugawara socket into an analytic theorem.
-/

/-- Machine-readable certification status for Virasoro integration. -/
def virasoroIntegrationStatus : ExternalRouteStatus :=
  ExternalRouteStatus.localReadbackCertified

/--
Integration gate for this external source:

- pin metadata is populated,
- local checkout path is recorded,
- the root module is imported locally,
- routes have local readback certification.
-/
def VirasoroProjectConductiveRouteTarget : Prop :=
  virasoroProjectPin.commit ≠ "" ∧
  virasoroProjectPin.localPath = "lean/InfoGeometry/External/Virasoro" ∧
  virasoroProjectPin.rootModule = "InfoGeometry.External.Virasoro" ∧
  virasoroIntegrationStatus = ExternalRouteStatus.localReadbackCertified ∧
  virasoroConductiveRouteMap ≠ []

/-- Certified local fact that the integration gate data is populated. -/
theorem virasoroProjectConductiveRouteTarget_holds :
    VirasoroProjectConductiveRouteTarget := by
  refine ⟨?_, rfl, rfl, rfl, virasoroConductiveRouteMap_nonempty⟩
  decide

/-- The vendored VirasoroProject integration has reached local readback certification. -/
theorem virasoroIntegration_is_certified :
    virasoroIntegrationStatus = ExternalRouteStatus.localReadbackCertified := by
  rfl

/-- Minimal local readback for the Virasoro bracket on basis generators. -/
theorem virasoroProject_lgen_readback (K : Type*) [Field K] [CharZero K] (n m : ℤ) :
    basisBracket K (VirasoroBasis.L n) (VirasoroBasis.L m) =
      (Finsupp.single (VirasoroBasis.L (n + m)) ((n - m : ℤ) : K) +
        if n + m = 0 then
          Finsupp.single VirasoroBasis.c (((n ^ 3 - n : ℤ) : K) / (12 : K))
        else 0) := by
  rfl

/-- Minimal local readback for the Virasoro central generator. -/
theorem virasoroProject_cgen_readback (K : Type*) [Field K] [CharZero K] :
    basisBracket K VirasoroBasis.c VirasoroBasis.c = 0 := by
  rfl

/-- Legacy lower-camel compatibility alias. -/
theorem virasoroProjectConductiveRouteTarget :
    VirasoroProjectConductiveRouteTarget :=
  virasoroProjectConductiveRouteTarget_holds

end InfoGeometry.OperatorAlgebra
