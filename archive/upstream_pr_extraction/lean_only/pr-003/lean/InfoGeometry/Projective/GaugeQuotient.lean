import Mathlib.LinearAlgebra.Projectivization.Basic

namespace InfoGeometry.Projective

open scoped Classical
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
theorem ray_smul (a : Kˣ) (v : Unnormalized (V := V)) :
    ray (K := K) (V := V)
        ⟨a • v.1, smul_ne_zero (Units.ne_zero a) v.2⟩
      =
    ray (K := K) (V := V) v := by
  apply (Projectivization.mk_eq_mk_iff K (a • v.1) v.1
      (smul_ne_zero (Units.ne_zero a) v.2) v.2).2
  refine ⟨a, ?_⟩
  simp

end InfoGeometry.Projective
