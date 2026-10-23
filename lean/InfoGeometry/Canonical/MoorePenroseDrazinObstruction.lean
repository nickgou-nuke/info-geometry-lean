import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.MoorePenrose

/-!
# A general Moore--Penrose/Drazin obstruction

The Moore--Penrose equations do not imply the index-one Drazin power law.
The obstruction is structural: a nonzero square-zero element cannot have its
Moore--Penrose inverse as an index-one Drazin inverse.  This is stated over an
arbitrary unital ring (with the star-ring structure needed only for the
Moore--Penrose predicate), so it does not depend on coordinates or a
commutative model.
-/

namespace InfoGeometry.Canonical.MoorePenroseDrazinObstruction

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose

variable {R : Type*} [Ring R]

/-- The index-one Drazin power law forces a square-zero element to vanish. -/
theorem square_zero_eq_zero_of_drazin_index_one
    {a b : R} (hD : IsDrazinInverse a b 1) (ha : a * a = 0) : a = 0 := by
  have hpow := hD.power
  exact (by simpa [pow_two, pow_one, ha] using hpow.symm)

variable [StarRing R]

/-- A nonzero square-zero Moore--Penrose operator cannot be Drazin index one
    with the same inverse.  Thus an EP/commutation hypothesis is genuinely
    necessary in the usual Moore--Penrose-to-Drazin implication. -/
theorem square_zero_moore_penrose_not_drazin_index_one
    {a b : R} (hMP : IsMoorePenroseInverse a b)
    (ha : a * a = 0) (ha0 : a ≠ 0) :
    ¬ IsDrazinInverse a b 1 := by
  rcases hMP with ⟨hinner, houter, hleft, hright⟩
  intro hD
  exact ha0 (square_zero_eq_zero_of_drazin_index_one hD ha)

end InfoGeometry.Canonical.MoorePenroseDrazinObstruction
