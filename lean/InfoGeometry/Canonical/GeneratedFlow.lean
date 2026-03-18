import InfoGeometry.Canonical.LogGenerator

namespace InfoGeometry.Canonical

/-!
# Generated Flow

High-level naming layer for the latter stages of the canonical relative-geometry
spine.

This file introduces the abstract stages

`LogGenerator -> GeneratedFlow -> GeometricResponse`.
-/

/-- Flow/transport generated from an additive logarithmic generator. -/
structure GeneratedFlow (G F : Type*) where
  flowOf : G → F

namespace GeneratedFlow

variable {W G F : Type*}

/-- Push a log-generator through a generated flow. -/
def along (Φ : GeneratedFlow G F) (L : LogGenerator W G) : W → F :=
  fun w => Φ.flowOf (L.logGen w)

end GeneratedFlow

/-- Exact exponential-style realization of a generated flow. -/
structure ExponentialGeneratedFlow (G F : Type*) where
  toGeneratedFlow : GeneratedFlow G F

namespace ExponentialGeneratedFlow

variable {G F : Type*}

/-- Forget the exponential branch to the common generated-flow interface. -/
def flowOf (Φ : ExponentialGeneratedFlow G F) : G → F :=
  Φ.toGeneratedFlow.flowOf

end ExponentialGeneratedFlow

/-- Abstract cocycle/transport family, separated from exponential generation. -/
structure CocycleGeneratedFlow (T F : Type*) where
  transport : T → F

/-- Geometric response extracted from a generated flow. -/
structure GeometricResponse (F R : Type*) where
  responseOf : F → R

namespace GeometricResponse

variable {W G F R : Type*}

/-- Read geometric response from a generated flow. -/
def along (resp : GeometricResponse F R) (Φ : GeneratedFlow G F) : G → R :=
  fun g => resp.responseOf (Φ.flowOf g)

/-- Full relative-geometry pipeline from log-generator to geometric response. -/
def fromLogGenerator (resp : GeometricResponse F R) (Φ : GeneratedFlow G F)
    (L : LogGenerator W G) : W → R :=
  fun w => resp.responseOf (Φ.flowOf (L.logGen w))

end GeometricResponse

namespace LogGenerator

variable {W G F R : Type*}

/-- Generate a flow from a logarithmic generator. -/
def generate (L : LogGenerator W G) (Φ : GeneratedFlow G F) : W → F :=
  GeneratedFlow.along Φ L

/-- Read geometric response from a logarithmic generator through a flow. -/
def respond (L : LogGenerator W G) (Φ : GeneratedFlow G F)
    (resp : GeometricResponse F R) : W → R :=
  GeometricResponse.fromLogGenerator resp Φ L

end LogGenerator

end InfoGeometry.Canonical
