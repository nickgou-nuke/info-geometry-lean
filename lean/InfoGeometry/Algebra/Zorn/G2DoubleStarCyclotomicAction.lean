import InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Simultaneous action on the two cyclotomic root hexagons

The Boolean coordinate separates the two six-element sectors.  The concrete
simple-reflection permutations act on the cyclic coordinate and preserve that
sector coordinate, so they braid the two hexagons in parallel.
-/

namespace InfoGeometry.Algebra.Zorn.G2DoubleStarCyclotomicAction

open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.OperatorAlgebra

theorem simple_reflection_one_preserves_sector (r : Root) :
    sector (cyclotomicS1Perm r) = sector r := by
  rcases r with ⟨b, k⟩
  cases b <;> rfl

theorem simple_reflection_two_preserves_sector (r : Root) :
    sector (cyclotomicS2Perm r) = sector r := by
  rcases r with ⟨b, k⟩
  cases b <;> rfl

theorem coxeter_preserves_sector (r : Root) :
    sector (cyclotomicCoxeterPerm r) = sector r := by
  rcases r with ⟨b, k⟩
  cases b <;> rfl

/-! The concrete cyclotomic permutations now expose the same carrier-
independent grade-action interface as the abstract dihedral action.  The
sector label is the grade; the cyclic root coordinate is deliberately left
inside the concrete permutation owner. -/

theorem simple_reflection_one_mapsTo_sector_family :
    MapsToGrade
      (fun b : Bool => {r : Root | sector r = b})
      (fun _ : Unit => fun r => cyclotomicS1Perm r)
      (fun _ b => b) := by
  intro _ b r hr
  change sector (cyclotomicS1Perm r) = b
  rw [simple_reflection_one_preserves_sector r]
  exact hr

theorem simple_reflection_two_mapsTo_sector_family :
    MapsToGrade
      (fun b : Bool => {r : Root | sector r = b})
      (fun _ : Unit => fun r => cyclotomicS2Perm r)
      (fun _ b => b) := by
  intro _ b r hr
  change sector (cyclotomicS2Perm r) = b
  rw [simple_reflection_two_preserves_sector r]
  exact hr

theorem coxeter_mapsTo_sector_family :
    MapsToGrade
      (fun b : Bool => {r : Root | sector r = b})
      (fun _ : Unit => fun r => cyclotomicCoxeterPerm r)
      (fun _ b => b) := by
  intro _ b r hr
  change sector (cyclotomicCoxeterPerm r) = b
  rw [coxeter_preserves_sector r]
  exact hr

theorem simple_reflection_one_preserves_short_and_long (r : Root) :
    r.1 = false → (cyclotomicS1Perm r).1 = false := by
  intro h
  rw [← h]
  simpa [sector] using simple_reflection_one_preserves_sector r

theorem simple_reflection_two_preserves_short_and_long (r : Root) :
    r.1 = true → (cyclotomicS2Perm r).1 = true := by
  intro h
  rw [← h]
  simpa [sector] using simple_reflection_two_preserves_sector r

theorem cyclotomicS1_permMatrix_sq :
    (cyclotomicS1Perm.permMatrix ℂ) ^ 2 = 1 := by
  rw [pow_two, ← Matrix.permMatrix_mul, ← pow_two, cyclotomicS1Perm_sq,
    Matrix.permMatrix_one]

theorem cyclotomicS2_permMatrix_sq :
    (cyclotomicS2Perm.permMatrix ℂ) ^ 2 = 1 := by
  rw [pow_two, ← Matrix.permMatrix_mul, ← pow_two, cyclotomicS2Perm_sq,
    Matrix.permMatrix_one]

theorem sq_eq_of_involution_compat
    (P Λ : Matrix Root Root ℂ) (q : ℂ)
    (hcompat : P * Λ * P * Λ = q • (1 : Matrix Root Root ℂ)) :
    (P * Λ) ^ 2 = q • (1 : Matrix Root Root ℂ) := by
  simpa [pow_two, Matrix.mul_assoc] using hcompat

theorem pow_twelve_eq_one_of_pow_six_eq_neg_one
    (C : Matrix Root Root ℂ)
    (hC : C ^ 6 = -(1 : Matrix Root Root ℂ)) :
    C ^ 12 = 1 := by
  calc
    C ^ 12 = C ^ 6 * C ^ 6 := by rw [← pow_add]
    _ = (-(1 : Matrix Root Root ℂ)) * (-(1 : Matrix Root Root ℂ)) := by rw [hC]
    _ = 1 := by simp

end InfoGeometry.Algebra.Zorn.G2DoubleStarCyclotomicAction
