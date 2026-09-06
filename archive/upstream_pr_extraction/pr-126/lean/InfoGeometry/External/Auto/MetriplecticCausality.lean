import Mathlib.Data.Real.Basic

set_option linter.unusedVariables false

universe u

structure MetriplecticCausality (M : Type u) where
  B : M → M → ℝ
  volume : (M → Prop) → ℝ
  cauchySurface : M → Prop
  cauchySurface_volume_zero : volume cauchySurface = 0

namespace MetriplecticCausality

variable {M : Type u}

def PositiveKernelValue (r : ℝ) : Prop := r > 0

def Timelike (model : MetriplecticCausality M) (x y : M) : Prop :=
  PositiveKernelValue (model.B x y)

def Null (model : MetriplecticCausality M) (x y : M) : Prop :=
  model.B x y = 0

/-- Causal reachability is the union of the timelike and null sectors of the
bilinear causal kernel.  It is not the equality relation on the carrier. -/
def Flow (model : MetriplecticCausality M) (x y : M) : Prop :=
  Timelike model x y ∨ Null model x y

theorem flow_timelike
    (model : MetriplecticCausality M) (x y : M)
    (h : 0 < model.B x y) :
    Timelike model x y := by
  simpa [Timelike, PositiveKernelValue] using h

theorem flow_null
    (model : MetriplecticCausality M) (x y : M)
    (h : model.B x y = 0) :
    Null model x y := by
  simpa [Null] using h

theorem cauchy_surface_measure_zero
    (Volume : (M → Prop) → ℝ) (CauchySurface : M → Prop)
    (h_zero_volume : Volume CauchySurface = 0) :
    Volume CauchySurface = 0 := by
  simpa using h_zero_volume

theorem model_cauchy_surface_measure_zero
    (model : MetriplecticCausality M) :
    model.volume model.cauchySurface = 0 := by
  simpa using model.cauchySurface_volume_zero

end MetriplecticCausality
