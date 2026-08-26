import InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics
import InfoGeometry.Arithmetic.HestenesKreinChiralProjectors

/-!
# InfoGeometry.Krein.SplitComplex

Krein-side adapter for the canonical split-complex seed.

This file does not reprove the split-complex arithmetic from scratch.  It
re-exports the concrete split-sign laws under the Krein namespace so that the
metric firewall can reference the same algebraic seed as the thermal/chiral
layers:

* `eps^2 = 1`;
* `1 ± eps` are nonzero zero divisors;
* the half-projectors are orthogonal idempotents;
* the split norm is multiplicative.
-/

noncomputable section

namespace InfoGeometry.Krein.SplitComplex

open InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics
open InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex
open InfoGeometry.Arithmetic.HestenesKreinChiralProjectors

/-- The split generator `eps`, aliased to the canonical `j`. -/
abbrev eps : InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex := j

/-- The positive null idempotent `p₊ = (1 + eps)/2`. -/
abbrev pPlus : InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex := ePlus

/-- The negative null idempotent `p₋ = (1 - eps)/2`. -/
abbrev pMinus : InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex := eMinus

@[simp] theorem eps_sq :
    SplitComplex.mul eps eps = SplitComplex.one := by
  simpa [eps] using j_mul_j

/-- The split sign gives explicit nonzero zero divisors. -/
theorem krein_split_sign_has_nonzero_zero_divisors :
    ∃ u v : InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex, u ≠ zero ∧ v ≠ zero ∧ SplitComplex.mul u v = zero := by
  simpa [eps] using split_sign_has_nonzero_zero_divisors

/-- The factors `1 + eps` and `1 - eps` multiply to zero. -/
theorem one_add_eps_mul_one_sub_eps_zero :
    SplitComplex.mul (SplitComplex.add one eps) (SplitComplex.add one (SplitComplex.neg eps)) = zero := by
  simpa [eps] using one_add_j_mul_one_sub_j_zero

/-- The opposite order also multiplies to zero. -/
theorem one_sub_eps_mul_one_add_eps_zero :
    SplitComplex.mul (SplitComplex.add one (SplitComplex.neg eps)) (SplitComplex.add one eps) = zero := by
  ext <;> simp [eps, SplitComplex.j, SplitComplex.add, SplitComplex.mul,
    SplitComplex.neg, SplitComplex.one, SplitComplex.zero]

/-- The positive half-projector is idempotent. -/
@[simp] theorem pPlus_idempotent :
    SplitComplex.mul pPlus pPlus = pPlus := by
  simpa [pPlus] using
    (InfoGeometry.Arithmetic.HestenesKreinChiralProjectors.ePlus_idempotent)

/-- The negative half-projector is idempotent. -/
@[simp] theorem pMinus_idempotent :
    SplitComplex.mul pMinus pMinus = pMinus := by
  simpa [pMinus] using
    (InfoGeometry.Arithmetic.HestenesKreinChiralProjectors.eMinus_idempotent)

/-- The projectors are orthogonal. -/
@[simp] theorem pPlus_mul_pMinus :
    SplitComplex.mul pPlus pMinus = zero := by
  simpa [pPlus, pMinus] using
    (InfoGeometry.Arithmetic.HestenesKreinChiralProjectors.ePlus_mul_eMinus)

/-- The projectors are orthogonal in the opposite order as well. -/
@[simp] theorem pMinus_mul_pPlus :
    SplitComplex.mul pMinus pPlus = zero := by
  simpa [pPlus, pMinus] using
    (InfoGeometry.Arithmetic.HestenesKreinChiralProjectors.eMinus_mul_ePlus)

/-- The split norm is multiplicative. -/
theorem norm_mul (x y : InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex) :
    SplitComplex.norm (SplitComplex.mul x y) = SplitComplex.norm x * SplitComplex.norm y := by
  cases x <;> cases y <;> simp [SplitComplex.norm, SplitComplex.leftPart,
    SplitComplex.rightPart, SplitComplex.mul] <;> ring

/-- Left multiplication by a norm-one split-complex unit preserves the split norm. -/
theorem norm_mul_left_of_norm_one (x y : InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex) (hx : SplitComplex.norm x = 1) :
    SplitComplex.norm (SplitComplex.mul x y) = SplitComplex.norm y := by
  rw [norm_mul, hx, one_mul]

/-- Right multiplication by a norm-one split-complex unit preserves the split norm. -/
theorem norm_mul_right_of_norm_one (x y : InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex) (hx : SplitComplex.norm x = 1) :
    SplitComplex.norm (SplitComplex.mul y x) = SplitComplex.norm y := by
  rw [norm_mul, hx, mul_one]

end InfoGeometry.Krein.SplitComplex
