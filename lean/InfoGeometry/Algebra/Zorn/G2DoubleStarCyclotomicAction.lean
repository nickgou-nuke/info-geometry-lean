import InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge

/-!
# Simultaneous action on the two cyclotomic root hexagons

The Boolean coordinate separates the two six-element sectors.  The concrete
simple-reflection permutations act on the cyclic coordinate and preserve that
sector coordinate, so they braid the two hexagons in parallel.
-/

namespace InfoGeometry.Algebra.Zorn.G2DoubleStarCyclotomicAction

open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl

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

theorem cyclotomic_artin_I2_six_relation :
    cyclotomicS1Perm * cyclotomicS2Perm * cyclotomicS1Perm *
        cyclotomicS2Perm * cyclotomicS1Perm * cyclotomicS2Perm =
      cyclotomicS2Perm * cyclotomicS1Perm * cyclotomicS2Perm *
        cyclotomicS1Perm * cyclotomicS2Perm * cyclotomicS1Perm := by
  apply Equiv.ext
  intro r
  rcases r with ⟨b, k⟩
  cases b <;>
    simp [cyclotomicS1Perm, cyclotomicS2Perm, cyclotomicS1Fun,
      cyclotomicS2Fun, Equiv.Perm.mul_def,
      show (3 : ZMod 6) = -3 by decide]

end InfoGeometry.Algebra.Zorn.G2DoubleStarCyclotomicAction
