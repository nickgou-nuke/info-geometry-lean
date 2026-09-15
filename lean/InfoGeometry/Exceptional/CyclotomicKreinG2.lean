import InfoGeometry.Exceptional.CyclotomicIntegerClock
import InfoGeometry.Exceptional.CyclotomicNeutralBoundary
import InfoGeometry.Exceptional.CyclotomicKreinG2Dependency
import InfoGeometry.Exceptional.CyclotomicRotation
import InfoGeometry.Canonical.TwelveFoldCyclotomicNative
import Mathlib.LinearAlgebra.RootSystem.Finite.G2

namespace InfoGeometry.Exceptional.CyclotomicKreinG2

open InfoGeometry.Canonical.TwelveFoldCyclotomicNative

theorem nonidentity_galois_automorphism_order
    (automorphism : Gal(CyclotomicField 12 ℚ / ℚ))
    (nonidentity : automorphism ≠ 1) : orderOf automorphism = 2 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · simpa [cyclotomic12_gal_exponent] using Monoid.pow_exponent_eq_one automorphism
  · intro prime prime_is_prime divides
    rcases (Nat.dvd_prime Nat.prime_two).mp divides with impossible | rfl
    · exact (prime_is_prime.ne_one impossible).elim
    · simpa using nonidentity

section RootPairing

variable {Root Weight Coweight : Type*} [Finite Root]
    [AddCommGroup Weight] [Module ℝ Weight]
    [AddCommGroup Coweight] [Module ℝ Coweight]
    (pairing : RootPairing Root ℝ Weight Coweight) [pairing.IsG2]

include pairing in
theorem g2_rank_and_root_count :
    Module.finrank ℝ Weight = 2 ∧ Nat.card Root = 12 := by
  letI : pairing.EmbeddedG2 := RootPairing.IsG2.toEmbeddedG2 pairing
  constructor
  · simpa using Module.finrank_eq_card_basis (RootPairing.EmbeddedG2.basis pairing)
  · exact RootPairing.EmbeddedG2.card_index_eq_twelve pairing

include pairing in
theorem galois_automorphisms_not_equivalent_to_g2_roots :
    IsEmpty (Gal(CyclotomicField 12 ℚ / ℚ) ≃ Root) := by
  refine ⟨fun equivalence => ?_⟩
  have cardinalities := Nat.card_congr equivalence
  rw [cyclotomic12_gal_card, (g2_rank_and_root_count pairing).2] at cardinalities
  norm_num at cardinalities

open scoped Classical in
omit [pairing.IsG2] in
theorem g2_six_short_and_six_long [pairing.EmbeddedG2]
    (invariant : pairing.InvariantForm)
    (short_unit : invariant.form (RootPairing.EmbeddedG2.shortRoot pairing)
      (RootPairing.EmbeddedG2.shortRoot pairing) = 1) :
    ((RootPairing.EmbeddedG2.allRoots pairing).filter
      (fun root => decide (invariant.form root root = 1))).length = 6 ∧
    ((RootPairing.EmbeddedG2.allRoots pairing).filter
      (fun root => decide (invariant.form root root = 3))).length = 6 := by
  have long_squared : invariant.form (RootPairing.EmbeddedG2.longRoot pairing)
      (RootPairing.EmbeddedG2.longRoot pairing) = 3 := by
    rw [RootPairing.EmbeddedG2.long_eq_three_mul_short invariant, short_unit]
    norm_num
  constructor <;>
    simp [RootPairing.EmbeddedG2.allRoots, long_squared, short_unit]

end RootPairing

end InfoGeometry.Exceptional.CyclotomicKreinG2
