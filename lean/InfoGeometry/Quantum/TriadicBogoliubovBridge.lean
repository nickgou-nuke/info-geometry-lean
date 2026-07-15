import InfoGeometry.Canonical.BogoliubovTransport
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace TriadicBogoliubovBridge

open BogoliubovTransport
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Krein dyadic block operator `u ⊗ₖ v`, built from the actual doubled-space Krein functional. -/
noncomputable def dyadicKrein (u v : H₂) : EndH :=
  ContinuousLinearMap.smulRight
    (((innerSL ℝ ((KreinSpace.J (H := H₂)) v)) : H₂ →L[ℝ] ℝ)) u

/-- Exact application formula for the Krein dyadic block. -/
@[simp] theorem dyadicKrein_apply (u v x : H₂) :
    dyadicKrein (E := E) u v x = (KreinSpace.kreinInner (H := H₂) v x) • u := by
  simp [dyadicKrein, KreinSpace.kreinInner_def]

/-- Triadic generator synthesized as a finite weighted sum of Krein dyadic blocks. -/
noncomputable def triadicGenerator {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (q a : ι → H₂) : EndH :=
  ∑ i, w i • dyadicKrein (E := E) (q i) (a i)

end TriadicBogoliubovBridge
