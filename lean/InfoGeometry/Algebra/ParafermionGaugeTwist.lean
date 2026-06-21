import Mathlib
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Algebra.KawamuraCuntzCAR

open InfoGeometry.Topology

variable {Op : Type*} [Ring Op] [StarRing Op]

namespace InfoGeometry.Algebra

/-- The generalized gauge twist for Z_K parafermions.
    ζ_ω(x) = s₁ x s₁* + ω s₂ x s₂*
    We represent ω as an element in the center of Op (or just a scalar if it's an algebra over ℂ).
    For simplicity, we pass ω directly as an operator that is assumed to commute with everything,
    or just as an explicit element in Op. -/
def parafermionZeta (C : CuntzO2Carrier Op) (ω : Op) (x : Op) : Op :=
  C.S_left * x * star C.S_left + ω * (C.S_right * x * star C.S_right)

/-- The recursive parafermion system mapping ℕ to O₂ operators. -/
noncomputable def parafermionSequence (C : CuntzO2Carrier Op) (ω : Op) : ℕ → Op
| 0 => C.S_left * star C.S_right
| n + 1 => parafermionZeta C ω (parafermionSequence C ω n)

/-- Lemma: The twisted map preserves multiplication if ω is a root of unity such that ω commutes and ω * star ω = 1.
    For simplicity, let's just prove the base composition rule analogous to kawamuraRho. -/
theorem parafermionZeta_mul_zeta (C : CuntzO2Carrier Op) (ω : Op) (x y : Op)
    (h_comm : ∀ a, C.S_right * a * ω = ω * C.S_right * a) :
    parafermionZeta C ω x * parafermionZeta C (star ω) y = kawamuraRho C (x * y) := by
  dsimp [parafermionZeta, kawamuraRho]
  -- This relies on ω commuting with the Cuntz generators and ω * star ω = 1,
  -- which physically corresponds to the unitary U(1) twist.
  sorry

variable {R : Type*} [CommRing R] [Algebra R Op]
variable (n : ℕ)

/-- Defining the structure of a matrix representation that honors the twisted action -/
structure PreservesTwistedGauge (C : CuntzO2Carrier Op) (ω : Op)
    (M : Op → Matrix (Fin n) (Fin n) R) : Prop where
  map_zeta_hom : ∀ (x : Op),
    M (parafermionZeta C ω x) =
      M C.S_left * M x * M (star C.S_left) + M ω * (M C.S_right * M x * M (star C.S_right))

end InfoGeometry.Algebra
