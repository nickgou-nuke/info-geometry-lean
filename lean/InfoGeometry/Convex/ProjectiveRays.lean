import InfoGeometry.Clifford.Cl11
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Projective Rays (Doubled Space)

Mathlib-native projectivization of doubled states:
physical states are rays in `DoubledSpace E`, i.e. `ℙ ℝ (DoubledSpace E)`.
-/

namespace InfoGeometry.Convex

open scoped LinearAlgebra.Projectivization

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NoZeroSMulDivisors ℝ (DoubledSpace E)]

/-- “Physical states” as rays in the doubled space (excluding `0` by construction). -/
abbrev ProjectiveState : Type _ := ℙ ℝ (DoubledSpace E)

/-- Canonical projection from a nonzero doubled state to its projective ray. -/
noncomputable def projectivize (v : DoubledSpace E) (hv : v ≠ 0) : ProjectiveState (E := E) :=
  Projectivization.mk ℝ v hv

end InfoGeometry.Convex
