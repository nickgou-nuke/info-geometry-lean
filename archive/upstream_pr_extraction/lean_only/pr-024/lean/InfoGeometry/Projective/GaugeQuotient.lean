import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# InfoGeometry.Projective.GaugeQuotient

Gauge-quotient helpers for rays in projectivized linear spaces.
-/

namespace InfoGeometry.Projective

open scoped LinearAlgebra.Projectivization

variable {K : Type*} {V : Type*}
  [DivisionRing K] [AddCommGroup V] [Module K V]
  [NoZeroSMulDivisors K V]

/-- Unnormalized states: nonzero vectors. -/
abbrev Unnormalized : Type _ :=
  { v : V // v ≠ (0 : V) }

/-- The ray/projection map `V \ {0} → ℙ K V`. -/
def ray (v : Unnormalized (V := V)) : ℙ K V :=
  Projectivization.mk K v.1 v.2

/-- Gauge invariance: scaling by a unit does not change the ray. -/
@[simp]
theorem ray_smul (a : Kˣ) (v : Unnormalized (V := V)) :
    ray (K := K) (V := V)
        ⟨a • v.1, smul_ne_zero (Units.ne_zero a) v.2⟩
      =
    ray (K := K) (V := V) v := by
  apply (Projectivization.mk_eq_mk_iff K (a • v.1) v.1
      (smul_ne_zero (Units.ne_zero a) v.2) v.2).2
  refine ⟨a, ?_⟩
  simp

/-- Equivalent gauge invariance statement for an arbitrary nonzero scalar. -/
@[simp]
theorem ray_smul₀ (a : K) (ha : a ≠ 0) (v : Unnormalized (V := V)) :
    ray (K := K) (V := V)
        ⟨a • v.1, smul_ne_zero ha v.2⟩
      =
    ray (K := K) (V := V) v := by
  simpa using (ray_smul (K := K) (V := V) (Units.mk0 a ha) v)

end InfoGeometry.Projective
