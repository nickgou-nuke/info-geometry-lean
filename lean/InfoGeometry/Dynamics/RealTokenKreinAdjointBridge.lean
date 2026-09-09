import InfoGeometry.Krein.KreinSpace

/-!
# Krein adjoints for a total chiral generator

This file deliberately lives on the analytic Krein carrier, not on the
algebraic doubled token witness.  A Krein adjoint requires a complete real
inner-product space and a fundamental symmetry; the algebraic witness alone
does not provide those instances.
-/

namespace InfoGeometry.Dynamics

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [KreinSpace H]

local notation "EndH" => H →L[ℝ] H

/-- The total generator with a real dissipative coefficient. -/
def totalKreinGenerator (γ : ℝ) (D R : EndH) : EndH := γ • D + R

/-- A Krein-self-adjoint dissipative part and a Krein-skew-adjoint rotational
part have the expected adjoint decomposition. -/
theorem kreinAdjoint_totalKreinGenerator (γ : ℝ) (D R : EndH)
    (hD : IsKreinSelfAdjoint D) (hR : IsKreinSkewAdjoint R) :
    kreinAdjoint (totalKreinGenerator γ D R) = γ • D - R := by
  unfold IsKreinSelfAdjoint at hD
  unfold IsKreinSkewAdjoint at hR
  simp [totalKreinGenerator, hD, hR, sub_eq_add_neg]

/-- The Krein-symmetric part of the total generator is exactly the
dissipative sector. -/
theorem totalKreinGenerator_add_kreinAdjoint
    (γ : ℝ) (D R : EndH) (hD : IsKreinSelfAdjoint D)
    (hR : IsKreinSkewAdjoint R) :
    totalKreinGenerator γ D R +
        kreinAdjoint (totalKreinGenerator γ D R) = 2 * γ • D := by
  rw [kreinAdjoint_totalKreinGenerator γ D R hD hR]
  simp [totalKreinGenerator, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm]
  rw [two_mul]
  simp [smul_add]

/- The Krein-antisymmetric part of the same total generator is the
   rotational sector.  No linear independence of the two sectors is used. -/
theorem totalKreinGenerator_sub_kreinAdjoint
    (γ : ℝ) (D R : EndH) (hD : IsKreinSelfAdjoint D)
    (hR : IsKreinSkewAdjoint R) :
    totalKreinGenerator γ D R -
        kreinAdjoint (totalKreinGenerator γ D R) = 2 • R := by
  rw [kreinAdjoint_totalKreinGenerator γ D R hD hR]
  simp [totalKreinGenerator, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm]
  rw [two_mul]

/-- With the rotational sector absent, the total generator has the Krein
    adjoint symmetry of the dissipative sector. -/
theorem totalKreinGenerator_kreinSelfAdjoint_of_zero_rotation
    (γ : ℝ) (D : EndH) (hD : IsKreinSelfAdjoint D) :
    IsKreinSelfAdjoint (totalKreinGenerator γ D 0) := by
  unfold IsKreinSelfAdjoint at hD ⊢
  have hR : IsKreinSkewAdjoint (0 : EndH) := by
    simp [IsKreinSkewAdjoint]
  rw [kreinAdjoint_totalKreinGenerator γ D 0 hD hR]
  simp [totalKreinGenerator]

/-- The total generator is Krein-skew-adjoint exactly when its dissipative
coefficient vanishes, provided the two sectors are already typed by their
Krein adjoint symmetries and no cancellation is assumed.  The forward
direction is intentionally exposed as an explicit hypothesis: sector
separation is not inferred from names alone. -/
theorem totalKreinGenerator_kreinSkew_of_zero_dissipation
    (D R : EndH) (hR : IsKreinSkewAdjoint R) :
    IsKreinSkewAdjoint (totalKreinGenerator 0 D R) := by
  unfold IsKreinSkewAdjoint at hR ⊢
  rw [totalKreinGenerator, zero_smul, zero_add, hR]

end InfoGeometry.Dynamics
