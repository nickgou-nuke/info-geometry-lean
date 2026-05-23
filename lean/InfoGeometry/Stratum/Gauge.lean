import Mathlib.Data.Real.Basic

import Mathlib.Algebra.Group.Action.Defs

/-!
# InfoGeometry.Stratum.Gauge

Layer 0 of the Functorial Hierarchy: The Scalar Parameter Layer.

This module isolates the strictly positive real gauge group $\mathbb{R}_{>0}$.
This gauge group provides the foundational symmetry for projectivization
across all layers of the theory (Classical, Finite NC, Infinite NC).
-/

namespace InfoGeometry.Stratum

noncomputable section

/-- The gauge group of strictly positive reals (Layer 0). -/
def PosGauge := { c : ℝ // 0 < c }

instance : Mul PosGauge := ⟨fun a b => ⟨a.val * b.val, mul_pos a.property b.property⟩⟩
instance : One PosGauge := ⟨⟨1, zero_lt_one⟩⟩
instance : Inv PosGauge := ⟨fun a => ⟨a.val⁻¹, inv_pos.mpr a.property⟩⟩

instance : Group PosGauge where
  mul_assoc a b c := Subtype.ext (mul_assoc _ _ _)
  one_mul a := Subtype.ext (one_mul _)
  mul_one a := Subtype.ext (mul_one _)
  inv_mul_cancel a := Subtype.ext (inv_mul_cancel₀ a.property.ne')

end

end InfoGeometry.Stratum
