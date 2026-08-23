import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Cyclotomic/Fibonacci identities on native commutative-ring filtered colimits

This owner is the commutative companion to
`HestenesKreinBilingualColimitBridge`.

It keeps cyclotomic and Fibonacci phase identities entirely inside Mathlib's
native `CommRingCat` filtered colimit.  In particular, the colimit carrier is
only an algebraic commutative ring: no topology, norm completion, analytic
limit, Hilbert-space structure, or "infinite-volume" interpretation is
asserted here.

The two theorem surfaces are:

* carrier identities are transported by the canonical colimit ring homs;
* invertible phase data are transported functorially by `Units.map`.
-/

namespace InfoGeometry.Physics.CyclotomicFibonacciCommRingColimitBridge

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type u} [Category.{u} J] [IsFiltered J]
variable (F : J ⥤ CommRingCat.{u}) [HasColimit F]

noncomputable section

/-- The native filtered colimit carrier in `CommRingCat`. -/
abbrev ColimitCarrier := (colimit F : CommRingCat.{u})

/-- The canonical stage-to-colimit ring hom. -/
abbrev stageMap (j : J) : F.obj j →+* ColimitCarrier F :=
  (colimit.ι F j).hom

/-- The induced homomorphism on units. -/
def stageUnitMap (j : J) : (F.obj j)ˣ →* (ColimitCarrier F)ˣ :=
  Units.map (stageMap F j)

@[simp] theorem stageMap_zero (j : J) :
    stageMap F j 0 = 0 := by
  exact map_zero (stageMap F j)

@[simp] theorem stageMap_one (j : J) :
    stageMap F j 1 = 1 := by
  exact map_one (stageMap F j)

@[simp] theorem stageMap_neg (j : J) (x : F.obj j) :
    stageMap F j (-x) = -(stageMap F j x) := by
  exact map_neg (stageMap F j) x

@[simp] theorem stageMap_pow (j : J) (x : F.obj j) (n : ℕ) :
    stageMap F j (x ^ n) = (stageMap F j x) ^ n := by
  exact map_pow (stageMap F j) x n

/-- The order-ten/Fibonacci root relation `q^5 = -1` is preserved by the
canonical filtered-colimit injection. -/
theorem stageMap_pow_five_eq_neg_one
    (j : J) (q : F.obj j) (hq : q ^ 5 = -1) :
    (stageMap F j q) ^ 5 = -1 := by
  have h := congrArg (stageMap F j) hq
  simpa using h

/-- Consequently `q^10 = 1` is preserved as well. -/
theorem stageMap_pow_ten_eq_one
    (j : J) (q : F.obj j) (hq : q ^ 5 = -1) :
    (stageMap F j q) ^ 10 = 1 := by
  calc
    (stageMap F j q) ^ 10 = ((stageMap F j q) ^ 5) ^ 2 := by ring
    _ = (-1) ^ 2 := by rw [stageMap_pow_five_eq_neg_one F j q hq]
    _ = 1 := by ring

/-- The tenth-cyclotomic polynomial relation is transported stagewise. -/
theorem stageMap_cyclotomic_ten_relation
    (j : J) (q : F.obj j)
    (hq : q ^ 4 - q ^ 3 + q ^ 2 - q + 1 = 0) :
    (stageMap F j q) ^ 4 - (stageMap F j q) ^ 3 +
        (stageMap F j q) ^ 2 - stageMap F j q + 1 = 0 := by
  have h := congrArg (stageMap F j) hq
  simpa using h

/-- Any polynomial identity of the specific Fibonacci form
`τ² + τ = 1` is preserved by the filtered-colimit injection. -/
theorem stageMap_fibonacci_quadratic
    (j : J) (τ : F.obj j) (hτ : τ ^ 2 + τ = 1) :
    (stageMap F j τ) ^ 2 + stageMap F j τ = 1 := by
  have h := congrArg (stageMap F j) hτ
  simpa using h

@[simp] theorem stageUnitMap_val
    (j : J) (q : (F.obj j)ˣ) :
    ((stageUnitMap F j q : (ColimitCarrier F)ˣ) : ColimitCarrier F) =
      stageMap F j (q : F.obj j) :=
  rfl

@[simp] theorem stageUnitMap_mul
    (j : J) (q r : (F.obj j)ˣ) :
    stageUnitMap F j (q * r) = stageUnitMap F j q * stageUnitMap F j r := by
  exact map_mul (stageUnitMap F j) q r

@[simp] theorem stageUnitMap_pow
    (j : J) (q : (F.obj j)ˣ) (n : ℕ) :
    stageUnitMap F j (q ^ n) = (stageUnitMap F j q) ^ n := by
  exact map_pow (stageUnitMap F j) q n

@[simp] theorem stageUnitMap_inv
    (j : J) (q : (F.obj j)ˣ) :
    stageUnitMap F j q⁻¹ = (stageUnitMap F j q)⁻¹ := by
  exact map_inv (stageUnitMap F j) q

/-- A unit-level fifth-power identity is preserved without forgetting
invertibility. -/
theorem stageUnitMap_pow_five_eq_neg_one
    (j : J) (q : (F.obj j)ˣ) (hq : q ^ 5 = -1) :
    (stageUnitMap F j q) ^ 5 = -1 := by
  have h := congrArg (stageUnitMap F j) hq
  simpa using h

/-- A unit identity involving inversion, such as the Fibonacci phase relation
`q⁻⁴ = -q`, is transported unchanged to the filtered colimit. -/
theorem stageUnitMap_zpow_neg_four_eq_neg
    (j : J) (q : (F.obj j)ˣ)
    (hq : q ^ (-4 : ℤ) = -q) :
    (stageUnitMap F j q) ^ (-4 : ℤ) = -(stageUnitMap F j q) := by
  have h := congrArg (stageUnitMap F j) hq
  simpa using h

/-- Compact theorem packet for the algebraic Fibonacci phase identities most
commonly consumed by the finite braid owners. -/
theorem colimit_fibonacci_phase_packet
    (j : J) (q : (F.obj j)ˣ)
    (hq5 : q ^ 5 = -1)
    (hqneg4 : q ^ (-4 : ℤ) = -q) :
    (stageUnitMap F j q) ^ 5 = -1 ∧
      (stageUnitMap F j q) ^ (-4 : ℤ) = -(stageUnitMap F j q) := by
  exact ⟨stageUnitMap_pow_five_eq_neg_one F j q hq5,
    stageUnitMap_zpow_neg_four_eq_neg F j q hqneg4⟩

end
end InfoGeometry.Physics.CyclotomicFibonacciCommRingColimitBridge
