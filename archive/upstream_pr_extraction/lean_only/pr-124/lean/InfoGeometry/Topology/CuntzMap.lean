import InfoGeometry.Topology.CuntzCantorSpectralTriple
import Mathlib.Tactic

/-!
# Cuntz Map — Algebraic Two-Branch Transfer

The Cuntz map Φ(X) = S_L·X·S*_L + S_R·X·S*_R is the canonical
two-branch transfer map associated to an abstract `O₂` carrier.

## Algebraic Properties
This file proves only the algebraic facts visible from the Cuntz relations:

  Φ(1) = 1        (probability conservation)
  Φ(X*) = Φ(X)*    (reality preservation)

KMS fixed-point and modular-flow statements are formulated with explicit
branch-scaling or pointwise equality witnesses.  This file does not prove
uniqueness, contractive convergence, complete positivity, or equality with a
continuous modular flow.
-/

namespace InfoGeometry.Topology.CuntzMap

open InfoGeometry.Topology.CuntzCantorSpectralTriple

variable (Op : Type*) [Ring Op] [StarRing Op]

/--
The Cuntz map / canonical two-branch transfer map of the Cuntz O₂ algebra.

  Φ(X) = S_left·X·S*_left + S_right·X·S*_right

This is the Markov transfer operator. It is not asserted to be
multiplicative: the Cuntz range projections create a sum of two conjugation
terms rather than an algebra homomorphism.
-/
def map (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (X : Op) : Op :=
  CuntzO2Carrier.S_left C * X * star (CuntzO2Carrier.S_left C) +
    CuntzO2Carrier.S_right C * X * star (CuntzO2Carrier.S_right C)

/--
**Unitality:** Φ(1) = 1. The Cuntz map preserves the identity,
encoding probability conservation — the total probability mass
redistributes across the two branches and sums to 1.
-/
theorem map_unital (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    map Op C 1 = 1 := by
  simpa [map] using C.range_sum

theorem map_additive
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (X Y : Op) :
    map Op C (X + Y) = map Op C X + map Op C Y := by
  simp [map, add_mul, mul_add, add_assoc, add_left_comm]

theorem map_mul
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (X Y : Op) :
    map Op C (X * Y) = map Op C X * map Op C Y := by
  let L := CuntzO2Carrier.S_left C
  let R := CuntzO2Carrier.S_right C
  have hLL : L * X * star L * L * Y * star L = L * X * Y * star L := by
    rw [mul_assoc (L * X) (star L) L,
      CuntzO2Carrier.left_isometry C]
    simp [mul_assoc]
  have hLR : L * X * star L * R * Y * star R = 0 := by
    rw [mul_assoc (L * X) (star L) R,
      (CuntzO2Carrier.orthogonal_ranges C).1]
    simp
  have hRL : R * X * star R * L * Y * star L = 0 := by
    rw [mul_assoc (R * X) (star R) L,
      (CuntzO2Carrier.orthogonal_ranges C).2]
    simp
  have hRR : R * X * star R * R * Y * star R = R * X * Y * star R := by
    rw [mul_assoc (R * X) (star R) R,
      CuntzO2Carrier.right_isometry C]
    simp [mul_assoc]
  unfold map
  simp only [add_mul, mul_add]
  simp only [← mul_assoc]
  rw [hLL, hRL, hLR, hRR]
  simp [L, R]

theorem map_zero
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    map Op C 0 = 0 := by
  simp [map]

/--
**Star-preserving:** Φ(X*) = Φ(X)*. The Cuntz map respects the
*-involution, preserving the reality/observable structure of the
algebra. Complete positivity is not asserted at this algebraic layer.
-/
theorem map_star (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (X : Op) :
    map Op C (star X) = star (map Op C X) := by
  unfold map
  simp [star_add, star_mul, mul_assoc]

/-- Additive real readout fixed by equal half-branch Cuntz scaling. -/
theorem map_real_fixed_point_of_half_branch_scaling
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (φ : Op →+ ℝ)
    (X : Op)
    (hleft : φ (CuntzO2Carrier.S_left C * X * star (CuntzO2Carrier.S_left C)) =
      (1 / 2 : ℝ) * φ X)
    (hright : φ (CuntzO2Carrier.S_right C * X * star (CuntzO2Carrier.S_right C)) =
      (1 / 2 : ℝ) * φ X) :
    φ (map Op C X) = φ X := by
  rw [map, map_add, hleft, hright]
  ring

/-- A half-branch real readout is fixed by a witnessed Cuntz modular step. -/
theorem discrete_modular_flow_real_fixed_point_of_half_branch_scaling
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (sigma : Op → Op)
    (hσ : ∀ X, sigma X = map Op C X)
    (φ : Op →+ ℝ)
    (X : Op)
    (hleft : φ (CuntzO2Carrier.S_left C * X * star (CuntzO2Carrier.S_left C)) =
      (1 / 2 : ℝ) * φ X)
    (hright : φ (CuntzO2Carrier.S_right C * X * star (CuntzO2Carrier.S_right C)) =
      (1 / 2 : ℝ) * φ X) :
    φ (sigma X) = φ X := by
  rw [hσ X]
  exact map_real_fixed_point_of_half_branch_scaling Op C φ X hleft hright

end InfoGeometry.Topology.CuntzMap
