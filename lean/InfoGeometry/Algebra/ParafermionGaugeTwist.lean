import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Algebra

open InfoGeometry.Topology

variable {Op : Type*} [Ring Op] [StarRing Op]

namespace InfoGeometry.Algebra

/-- The generalized gauge twist for Z_K parafermions.
    ζ_ω(x) = s₁ x s₁* + ω s₂ x s₂*
    We represent ω as an element in the center of Op (or just a scalar if it's an algebra over ℂ).
    For simplicity, we pass ω directly as an operator that is assumed to commute with everything,
    or just as an explicit element in Op. -/
def parafermionZeta (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (ω : Op) (x : Op) : Op :=
  CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C) + ω * (CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C))

/-- The recursive parafermion system mapping ℕ to O₂ operators. -/
noncomputable def parafermionSequence (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (ω : Op) : ℕ → Op
| 0 => CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)
| n + 1 => parafermionZeta C ω (parafermionSequence C ω n)

/-- Lemma: The twisted map preserves multiplication if ω is a root of unity such that ω commutes and ω * star ω = 1.
    For simplicity, let's just prove the base composition rule analogous to kawamuraRho. -/
theorem parafermionZeta_mul_zeta (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (ω : Op) (x y : Op)
    (h_comm : ∀ a, a * ω = ω * a) (h_unit : ω * star ω = 1) :
    parafermionZeta C ω x * parafermionZeta C (star ω) y = kawamuraRho C (x * y) := by
  dsimp [parafermionZeta, kawamuraRho]
  have h_star_comm : ∀ a, a * star ω = star ω * a := by
    intro a
    have h_star_comm_aux : star (star a * ω) = star (ω * star a) := by rw [h_comm]
    simpa using h_star_comm_aux.symm
  rw [add_mul, mul_add, mul_add]
  have h1 : (CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C)) * (CuntzO2Carrier.S_left C * y * star (CuntzO2Carrier.S_left C)) = CuntzO2Carrier.S_left C * (x * y) * star (CuntzO2Carrier.S_left C) := by
    calc (CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C)) * (CuntzO2Carrier.S_left C * y * star (CuntzO2Carrier.S_left C))
      _ = CuntzO2Carrier.S_left C * x * (star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_left C) * y * star (CuntzO2Carrier.S_left C) := by simp [mul_assoc]
      _ = CuntzO2Carrier.S_left C * x * 1 * y * star (CuntzO2Carrier.S_left C) := by rw [CuntzO2Carrier.left_isometry C]
      _ = CuntzO2Carrier.S_left C * (x * y) * star (CuntzO2Carrier.S_left C) := by simp [mul_assoc]
  have h2 : (ω * (CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C))) * (star ω * (CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C))) = CuntzO2Carrier.S_right C * (x * y) * star (CuntzO2Carrier.S_right C) := by
    calc (ω * (CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C))) * (star ω * (CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C)))
      _ = ω * (CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C) * star ω) * (CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C)) := by simp [mul_assoc]
      _ = ω * (star ω * (CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C))) * (CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C)) := by rw [h_star_comm]
      _ = (ω * star ω) * (CuntzO2Carrier.S_right C * x * (star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_right C) * y * star (CuntzO2Carrier.S_right C)) := by simp [mul_assoc]
      _ = 1 * (CuntzO2Carrier.S_right C * x * 1 * y * star (CuntzO2Carrier.S_right C)) := by rw [h_unit, CuntzO2Carrier.right_isometry C]
      _ = CuntzO2Carrier.S_right C * (x * y) * star (CuntzO2Carrier.S_right C) := by simp [mul_assoc]
  have h3 : (CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C)) * (star ω * (CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C))) = 0 := by
    calc (CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C)) * (star ω * (CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C)))
      _ = CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C) * star ω * CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C) := by simp [mul_assoc]
      _ = star ω * (CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C)) * CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C) := by rw [h_star_comm]
      _ = 0 := by simp [mul_assoc, (CuntzO2Carrier.orthogonal_ranges C).1]
  have h4 : (ω * (CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C))) * (CuntzO2Carrier.S_left C * y * star (CuntzO2Carrier.S_left C)) = 0 := by
    calc (ω * (CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C))) * (CuntzO2Carrier.S_left C * y * star (CuntzO2Carrier.S_left C))
      _ = ω * CuntzO2Carrier.S_right C * x * (star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_left C) * y * star (CuntzO2Carrier.S_left C) := by simp [mul_assoc]
      _ = ω * CuntzO2Carrier.S_right C * x * 0 * y * star (CuntzO2Carrier.S_left C) := by rw [(CuntzO2Carrier.orthogonal_ranges C).2]
      _ = 0 := by simp
  rw [h1, h2, h3, h4]
  simp

variable {R : Type*} [CommRing R] [Algebra R Op]
variable (n : ℕ)

/-- Defining the structure of a matrix representation that honors the twisted action -/
def PreservesTwistedGauge (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (ω : Op)
    (M : Op → Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ (x : Op),
    M (parafermionZeta C ω x) =
      M (CuntzO2Carrier.S_left C) * M x * M (star (CuntzO2Carrier.S_left C)) + M ω *
        (M (CuntzO2Carrier.S_right C) * M x * M (star (CuntzO2Carrier.S_right C)))

end InfoGeometry.Algebra
