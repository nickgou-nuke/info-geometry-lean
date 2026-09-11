import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Projective.KuzminCuntzPath

/-!
# Kuzmin q-CCR Inductive-Limit Bridge

Conservative stage-to-limit bridge for the Kuzmin q-CCR corridor.

Closed here:

* finite `q = 0`, `q = -1`, and `q = 1` readouts from `KuzminCuntzPath`;
* transport of those readouts through an explicit map into an abstract limit
  carrier.

Not closed here:

* the analytic C*-isomorphism to a genuine infinite-generator `KO_∞`;
* construction of the limit map itself from the finite q-CCR owners;
* any claim that the finite q-CCR algebra is already the colimit.

The bridge is assumption-gated: the infinite carrier map is an explicit field.
-/

namespace InfoGeometry.Projective.KuzminInductiveLimitBridge

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Projective.KuzminCuntzPath

variable {R : Type*} [CommRing R] [StarRing R]
variable {AInf : Type*} [CommRing AInf]

/--
Conservative limit data for the Kuzmin corridor.

The finite q-CCR seed is transported to an abstract limit carrier through an
explicit ring homomorphism. No analytic limit theorem is claimed.
-/
structure KuzminInductiveLimitData where
  seed : QCCRSeed R
  toCuntzToeplitz : R ≃⋆+* CuntzToeplitzAlg 2
  toLimit : CuntzToeplitzAlg 2 →+* AInf

/-- The `q = 0` Toeplitz readout survives transport to the limit carrier. -/
theorem q_zero_infinite_toeplitz_readout
    (H : KuzminInductiveLimitData (R := R) (AInf := AInf))
    (hq0 : H.seed.q = (0 : R))
    (i j : Fin 2) :
    H.toLimit (H.toCuntzToeplitz (H.seed.creation i)) *
        H.toLimit (H.toCuntzToeplitz (H.seed.annihilation j)) =
      (if i = j then 1 else 0) := by
  have hfinite :
      H.seed.creation i * H.seed.annihilation j = (if i = j then 1 else 0) :=
    seed_toeplitz_limit (H := H.seed) hq0 i j
  have hmap := congrArg H.toLimit (congrArg H.toCuntzToeplitz hfinite)
  simpa [map_mul] using hmap

/-- The `q = -1` CAR readout survives transport to the limit carrier. -/
theorem q_neg_one_infinite_car_readout
    (H : KuzminInductiveLimitData (R := R) (AInf := AInf))
    (hqneg1 : H.seed.q = (-1 : R))
    (i j : Fin 2) :
    H.toLimit (H.toCuntzToeplitz (H.seed.creation i)) *
        H.toLimit (H.toCuntzToeplitz (H.seed.annihilation j)) +
      H.toLimit (H.toCuntzToeplitz (H.seed.annihilation j)) *
        H.toLimit (H.toCuntzToeplitz (H.seed.creation i)) =
      (if i = j then 1 else 0) := by
  have hfinite :
      H.seed.creation i * H.seed.annihilation j +
        H.seed.annihilation j * H.seed.creation i = (if i = j then 1 else 0) :=
    seed_car_from_minus_one (H := H.seed) hqneg1 i j
  have hmap := congrArg H.toLimit (congrArg H.toCuntzToeplitz hfinite)
  simpa [map_add, map_mul] using hmap

/-- The `q = 1` CCR readout survives transport to the limit carrier. -/
theorem q_pos_one_infinite_ccr_readout
    (H : KuzminInductiveLimitData (R := R) (AInf := AInf))
    (hqpos1 : H.seed.q = (1 : R))
    (i j : Fin 2) :
    H.toLimit (H.toCuntzToeplitz (H.seed.creation i)) *
        H.toLimit (H.toCuntzToeplitz (H.seed.annihilation j)) -
      H.toLimit (H.toCuntzToeplitz (H.seed.annihilation j)) *
        H.toLimit (H.toCuntzToeplitz (H.seed.creation i)) =
      (if i = j then 1 else 0) := by
  have hfinite :
      H.seed.creation i * H.seed.annihilation j -
        H.seed.annihilation j * H.seed.creation i = (if i = j then 1 else 0) :=
    seed_ccr_from_plus_one (H := H.seed) hqpos1 i j
  have hmap := congrArg H.toLimit (congrArg H.toCuntzToeplitz hfinite)
  simpa [map_sub, map_mul] using hmap

/-- A q=0 stage can be packaged as explicit limit data. -/
def q_zero_limit_data
    (seed : QCCRSeed R)
    (toCuntzToeplitz : R ≃⋆+* CuntzToeplitzAlg 2)
    (toLimit : CuntzToeplitzAlg 2 →+* AInf) :
    KuzminInductiveLimitData (R := R) (AInf := AInf) where
  seed := seed
  toCuntzToeplitz := toCuntzToeplitz
  toLimit := toLimit

end InfoGeometry.Projective.KuzminInductiveLimitBridge
