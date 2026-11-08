import InfoGeometry.Singular.MoorePenroseChiralDefects

/-!
# Symmetric support overlap without additive torsion

Contract: retain an arbitrary noncommutative star ring and its native
Moore–Penrose inverse equations. With torsion-free addition, zero symmetric
support overlap is equivalent to square-zero. No commutation of the operator
with its inverse, or of the supports, is imposed.
Dependency order: characteristic-free overlap criterion → cancellation of
doubling → square-zero; the converse uses the two orthogonal support products.
-/
namespace InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse

variable {R : Type*} [Ring R] [StarRing R] [IsAddTorsionFree R] {a m : R}

theorem symmetric_support_overlap_zero_iff_square_zero
    (h : IsMoorePenroseInverse a m) :
    (a * m) * (m * a) + (m * a) * (a * m) = 0 ↔ a * a = 0 := by
  constructor
  · intro hz
    have ht := (h.symmetric_support_overlap_zero_iff).mp hz
    apply IsAddTorsionFree.nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
    simpa only [two_nsmul, smul_zero] using ht.2
  · intro ha
    rw [h.range_mul_domain_eq_zero ha, domain_mul_range_eq_zero ha, add_zero]

end InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
