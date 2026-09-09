import Mathlib.Tactic
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
    (h_comm : ∀ a, a * ω = ω * a) (h_unit : ω * star ω = 1) :
    parafermionZeta C ω x * parafermionZeta C (star ω) y = kawamuraRho C (x * y) := by
  dsimp [parafermionZeta, kawamuraRho]
  have h_star_comm : ∀ a, a * star ω = star ω * a := by
    intro a
    have h_star_comm_aux : star (star a * ω) = star (ω * star a) := by rw [h_comm]
    simpa using h_star_comm_aux.symm
  rw [add_mul, mul_add, mul_add]
  have h1 : (C.S_left * x * star C.S_left) * (C.S_left * y * star C.S_left) = C.S_left * (x * y) * star C.S_left := by
    calc (C.S_left * x * star C.S_left) * (C.S_left * y * star C.S_left)
      _ = C.S_left * x * (star C.S_left * C.S_left) * y * star C.S_left := by simp [mul_assoc]
      _ = C.S_left * x * 1 * y * star C.S_left := by rw [C.left_isometry]
      _ = C.S_left * (x * y) * star C.S_left := by simp [mul_assoc]
  have h2 : (ω * (C.S_right * x * star C.S_right)) * (star ω * (C.S_right * y * star C.S_right)) = C.S_right * (x * y) * star C.S_right := by
    calc (ω * (C.S_right * x * star C.S_right)) * (star ω * (C.S_right * y * star C.S_right))
      _ = ω * (C.S_right * x * star C.S_right * star ω) * (C.S_right * y * star C.S_right) := by simp [mul_assoc]
      _ = ω * (star ω * (C.S_right * x * star C.S_right)) * (C.S_right * y * star C.S_right) := by rw [h_star_comm]
      _ = (ω * star ω) * (C.S_right * x * (star C.S_right * C.S_right) * y * star C.S_right) := by simp [mul_assoc]
      _ = 1 * (C.S_right * x * 1 * y * star C.S_right) := by rw [h_unit, C.right_isometry]
      _ = C.S_right * (x * y) * star C.S_right := by simp [mul_assoc]
  have h3 : (C.S_left * x * star C.S_left) * (star ω * (C.S_right * y * star C.S_right)) = 0 := by
    calc (C.S_left * x * star C.S_left) * (star ω * (C.S_right * y * star C.S_right))
      _ = C.S_left * x * star C.S_left * star ω * C.S_right * y * star C.S_right := by simp [mul_assoc]
      _ = star ω * (C.S_left * x * star C.S_left) * C.S_right * y * star C.S_right := by rw [h_star_comm]
      _ = 0 := by simp [mul_assoc, C.orthogonal_ranges.1]
  have h4 : (ω * (C.S_right * x * star C.S_right)) * (C.S_left * y * star C.S_left) = 0 := by
    calc (ω * (C.S_right * x * star C.S_right)) * (C.S_left * y * star C.S_left)
      _ = ω * C.S_right * x * (star C.S_right * C.S_left) * y * star C.S_left := by simp [mul_assoc]
      _ = ω * C.S_right * x * 0 * y * star C.S_left := by rw [C.orthogonal_ranges.2]
      _ = 0 := by simp
  rw [h1, h2, h3, h4]
  simp

variable {R : Type*} [CommRing R] [Algebra R Op]
variable (n : ℕ)

/-- Defining the structure of a matrix representation that honors the twisted action -/
def PreservesTwistedGauge (C : CuntzO2Carrier Op) (ω : Op)
    (M : Op → Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ (x : Op),
    M (parafermionZeta C ω x) =
      M C.S_left * M x * M (star C.S_left) + M ω *
        (M C.S_right * M x * M (star C.S_right))

end InfoGeometry.Algebra
