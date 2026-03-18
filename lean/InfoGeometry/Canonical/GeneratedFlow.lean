import InfoGeometry.Canonical.LogGenerator
import InfoGeometry.Canonical.SpineAttributes

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

attribute [spine_object] GeneratedFlow

namespace GeneratedFlow

variable {W G F : Type*}

/-- Push a log-generator through a generated flow. -/
def along (Φ : GeneratedFlow G F) (L : LogGenerator W G) : W → F :=
  fun w => Φ.flowOf (L.logGen w)

/-- Pointwise expansion of `GeneratedFlow.along`. -/
@[simp] theorem along_apply (Φ : GeneratedFlow G F) (L : LogGenerator W G) (w : W) :
    Φ.along L w = Φ.flowOf (L.logGen w) := by
  rfl

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

attribute [spine_object] GeometricResponse

namespace GeometricResponse

variable {W G F R : Type*}

/-- Read geometric response from a generated flow. -/
def along (resp : GeometricResponse F R) (Φ : GeneratedFlow G F) : G → R :=
  fun g => resp.responseOf (Φ.flowOf g)

/-- Pointwise expansion of `GeometricResponse.along`. -/
@[simp] theorem along_apply (resp : GeometricResponse F R) (Φ : GeneratedFlow G F) (g : G) :
    resp.along Φ g = resp.responseOf (Φ.flowOf g) := by
  rfl

/-- Full relative-geometry pipeline from log-generator to geometric response. -/
def fromLogGenerator (resp : GeometricResponse F R) (Φ : GeneratedFlow G F)
    (L : LogGenerator W G) : W → R :=
  fun w => resp.responseOf (Φ.flowOf (L.logGen w))

/-- Pointwise expansion of `fromLogGenerator`. -/
@[simp] theorem fromLogGenerator_apply
    (resp : GeometricResponse F R) (Φ : GeneratedFlow G F) (L : LogGenerator W G) (w : W) :
    resp.fromLogGenerator Φ L w = resp.responseOf (Φ.flowOf (L.logGen w)) := by
  rfl

/-- `fromLogGenerator` factors through `along` after applying the log-generator. -/
@[simp] theorem fromLogGenerator_eq_along_comp
    (resp : GeometricResponse F R) (Φ : GeneratedFlow G F) (L : LogGenerator W G) :
    resp.fromLogGenerator Φ L = resp.along Φ ∘ L.logGen := by
  funext w
  rfl

attribute [spine_functor, spine_functor_lift] GeneratedFlow.along
attribute [spine_functor, spine_functor_responder] GeometricResponse.along
attribute [spine_functor, spine_functor_responder] GeometricResponse.fromLogGenerator

end GeometricResponse

namespace LogGenerator

variable {W G F R : Type*}

/-- Generate a flow from a logarithmic generator. -/
def generate (L : LogGenerator W G) (Φ : GeneratedFlow G F) : W → F :=
  GeneratedFlow.along Φ L

/-- `generate` is the canonical alias for `GeneratedFlow.along`. -/
@[simp] theorem generate_eq_along (L : LogGenerator W G) (Φ : GeneratedFlow G F) :
    L.generate Φ = Φ.along L := by
  rfl

/-- Pointwise expansion of `generate`. -/
@[simp] theorem generate_apply (L : LogGenerator W G) (Φ : GeneratedFlow G F) (w : W) :
    L.generate Φ w = Φ.flowOf (L.logGen w) := by
  rfl

/-- Read geometric response from a logarithmic generator through a flow. -/
def respond (L : LogGenerator W G) (Φ : GeneratedFlow G F)
    (resp : GeometricResponse F R) : W → R :=
  GeometricResponse.fromLogGenerator resp Φ L

/-- `respond` is the direct alias-expansion of `fromLogGenerator`. -/
@[simp] theorem respond_eq_fromLogGenerator
    (L : LogGenerator W G) (Φ : GeneratedFlow G F) (resp : GeometricResponse F R) :
    L.respond Φ resp = resp.fromLogGenerator Φ L := by
  rfl

/-- Reading response after generation factors through the generated transport. -/
theorem respond_eq_responseOf_comp_generate
    (L : LogGenerator W G) (Φ : GeneratedFlow G F) (resp : GeometricResponse F R) :
    L.respond Φ resp = resp.responseOf ∘ L.generate Φ := by
  funext w
  rfl

/-- Pointwise form of `respond_eq_responseOf_comp_generate`. -/
theorem respond_apply
    (L : LogGenerator W G) (Φ : GeneratedFlow G F) (resp : GeometricResponse F R) (w : W) :
    L.respond Φ resp w = resp.responseOf (L.generate Φ w) := by
  rfl

attribute [spine_functor, spine_functor_lift] LogGenerator.generate
attribute [spine_functor, spine_functor_responder] LogGenerator.respond

end LogGenerator

end InfoGeometry.Canonical
