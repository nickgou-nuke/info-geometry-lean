import Mathlib.Tactic
import InfoGeometry.Canonical.ConnesRadonNikodymCocycle
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Arithmetic.MoebiusSignature

open InfoGeometry.Canonical.FormalPrimeRootSystem
open ConnesCocycle

/-!
# Prime Connes Radon-Nikodym Cocycle Coefficients

The explicit Connes Radon-Nikodym cocycle [Dω₂ : Dω₁]_t between two prime
state profiles, computed as product of Weyl denominator factors.

#### BUCKET 1: CLOSED FINITE THEOREMS

- `cocycleCoefficient_empty` — the coefficient over the empty prime set is 1.
- `cocycleCoefficient_singleton` — the coefficient over a single prime p
  equals (1 - x_p), the Weyl denominator factor at p.

#### BUCKET 2: CONDITIONAL THEOREMS

- `cocycleCoefficient_eq_weylDenominatorProduct` — equals the product-form
  Weyl denominator from FormalPrimeRootSystem.

#### BUCKET 3: OPEN CLOSURE DEBT

- Full prime state profile integration with occupancy difference.
- Exponentiation to the modular time evolution u(t).
-/

namespace PrimeCocycleCoefficients

/--
The cocycle coefficient for a finite prime set P with thermal variable x
is the product of Weyl denominator factors:

  coeff_P(x) = ∏_{p ∈ P} (1 - x_p)

This is exactly the FormalPrimeRootSystem.weylDenominatorProduct.
-/
noncomputable def cocycleCoefficient (P : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  ∏ p ∈ P, (1 - x p)

/--
Over the empty prime set, the coefficient is 1.
-/
theorem cocycleCoefficient_empty (x : ℕ → ℝ) : cocycleCoefficient ∅ x = 1 := by
  simp [cocycleCoefficient]

/--
Over a singleton {p}, the coefficient equals the Weyl denominator factor
(1 - x_p).
-/
theorem cocycleCoefficient_singleton (p : ℕ) (x : ℕ → ℝ) :
    cocycleCoefficient {p} x = 1 - x p := by
  simp [cocycleCoefficient]

/--
The cocycle coefficient equals the formal prime Weyl denominator product.
-/
theorem cocycleCoefficient_eq_weylDenominatorProduct
    (L : FormalPrimeRootLattice) (x : ℕ → ℝ) :
    cocycleCoefficient L.primes x = weylDenominatorProduct L x := by
  unfold cocycleCoefficient weylDenominatorProduct
  rfl

end PrimeCocycleCoefficients
