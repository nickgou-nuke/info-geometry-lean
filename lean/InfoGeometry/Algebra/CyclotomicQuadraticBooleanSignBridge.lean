/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.ZMod.Units
import InfoGeometry.Algebra.BostConnesClassFieldTheoryBridge
import InfoGeometry.Canonical.FormalPrimeRootSystem

/-!
# InfoGeometry.Algebra.CyclotomicQuadraticBooleanSignBridge

Characteristic-0 Galois extension bridge connecting
`BostConnesClassFieldTheory.GaloisGroupAction` on `(ℤ/N)^×` to the Boolean Weyl
sign group of `FormalPrimeRootSystem`:

For a finite set of odd primes `L : FormalPrimeRootLattice` with squarefree
modulus `N = squarefreeCode L.primes = ∏_{p ∈ L.primes} p`:

1. `cyclotomicGaloisAction N : GaloisGroupAction (ZMod N)ˣ (ZMod N)` constructs
   the concrete finite-level cyclotomic Galois action of `(ℤ/N)^×` on `ℤ/N`.
2. Each odd prime `p ∈ L.primes` yields a group homomorphism
   `primeQuadCharHom p : (ZMod p)ˣ →* ℤˣ` via Mathlib's `quadraticChar (ZMod p)`.
3. Composing with the reduction `(ZMod N)ˣ →* (ZMod p)ˣ` yields the product
   quadratic-character homomorphism
   `cyclotomicToBooleanSign L : (ZMod (squarefreeCode L.primes))ˣ →* ({p // p ∈ L.primes} → ℤˣ)`.
4. Mapping each `u ∈ (ZMod N)ˣ` to its quadratic-nonresidue support
   `nonResidueWeyl L u : BooleanWeylGroup L` proves the exact identity:

     `∏ p : {p // p ∈ L.primes}, ((cyclotomicToBooleanSign L u p : ℤ) : ℝ) = weylSign (nonResidueWeyl L u)`.
-/

namespace InfoGeometry.Algebra.CyclotomicQuadraticBooleanSignBridge

open scoped BigOperators
open InfoGeometry.Algebra.BostConnesClassFieldTheory
open InfoGeometry.Canonical.FormalPrimeRootSystem

/-! ## 1. Concrete finite-level cyclotomic `GaloisGroupAction` on `ℤ/N` -/

/-- Concrete finite-level cyclotomic Galois action: `(ZMod N)ˣ` acts on `ZMod N`
by multiplication, commuting with positive-integer scaling. -/
def cyclotomicGaloisAction (N : ℕ) : GaloisGroupAction (ZMod N)ˣ (ZMod N) where
  act g :=
    { toFun := fun γ => (g : ZMod N) * γ
      map_zero' := mul_zero _
      map_add' := fun x y => mul_add _ x y }
  act_one := fun γ => by simp
  act_mul := fun g₁ g₂ γ => by
    change ((g₁ * g₂ : (ZMod N)ˣ) : ZMod N) * γ = (g₁ : ZMod N) * ((g₂ : ZMod N) * γ)
    rw [Units.val_mul, mul_assoc]
  act_smul_comm := fun g n γ => by
    change (g : ZMod N) * ((n : ℕ) • γ) = (n : ℕ) • ((g : ZMod N) * γ)
    simp [nsmul_eq_mul, mul_left_comm]

/-! ## 2. Quadratic character `(ZMod p)ˣ →* ℤˣ` for an odd prime `p` -/

/-- For a prime `p`, the quadratic character on `(ZMod p)ˣ` takes values in `ℤˣ = {±1}`. -/
noncomputable def primeQuadCharHom (p : ℕ) [Fact (Nat.Prime p)] : (ZMod p)ˣ →* ℤˣ where
  toFun u :=
    { val := quadraticChar (ZMod p) (u : ZMod p)
      inv := quadraticChar (ZMod p) (u⁻¹ : (ZMod p)ˣ)
      val_inv := by
        rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
      inv_val := by
        rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one] }
  map_one' := by
    ext
    exact map_one (quadraticChar (ZMod p))
  map_mul' u v := by
    ext
    exact map_mul (quadraticChar (ZMod p)) (u : ZMod p) (v : ZMod p)

/-- For an odd prime `p`, `primeQuadCharHom p : (ZMod p)ˣ →* ℤˣ` is surjective. -/
theorem primeQuadCharHom_surjective (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Function.Surjective (primeQuadCharHom p) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  intro s
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨1, map_one _⟩
  · obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) hchar
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, MulChar.map_zero] at ha
      norm_num at ha
    refine ⟨Units.mk0 a ha0, ?_⟩
    ext
    exact ha

/-! ## 3. Product quadratic-character homomorphism `(ZMod N)ˣ →* ({p // p ∈ L.primes} → ℤˣ)` -/

/-- Reduction of `(ZMod (squarefreeCode L.primes))ˣ` to `(ZMod p)ˣ` for `p ∈ L.primes`. -/
def reduceUnitAtPrime (L : FormalPrimeRootLattice) (p : {p // p ∈ L.primes}) :
    (ZMod (squarefreeCode L.primes))ˣ →* (ZMod p.1)ˣ :=
  ZMod.unitsMap (Finset.dvd_prod_of_mem id p.2)

/-- Product quadratic-character homomorphism mapping `(ZMod N)ˣ` into the
Boolean sign group `{p // p ∈ L.primes} → ℤˣ`. -/
noncomputable def cyclotomicToBooleanSign (L : FormalPrimeRootLattice) :
    (ZMod (squarefreeCode L.primes))ˣ →* ({p // p ∈ L.primes} → ℤˣ) :=
  MonoidHom.pi fun p =>
    letI : Fact (Nat.Prime p.1) := ⟨L.prime_mem p.1 p.2⟩
    (primeQuadCharHom p.1).comp (reduceUnitAtPrime L p)

/-- The quadratic-nonresidue prime support of `u ∈ (ZMod N)ˣ` as a
`BooleanWeylGroup L` element. -/
noncomputable def nonResidueWeyl (L : FormalPrimeRootLattice)
    (u : (ZMod (squarefreeCode L.primes))ˣ) : BooleanWeylGroup L where
  support :=
    by
      classical
      exact L.primes.filter fun p =>
        ∃ hp : p ∈ L.primes, cyclotomicToBooleanSign L u ⟨p, hp⟩ = -1
  support_subset := by
    classical
    exact Finset.filter_subset _ _

/-- **Boolean-sign / quadratic-character product identity**:
the product of the Legendre/quadratic signs of `u ∈ (ℤ/N)^×` over all primes
`p ∈ L.primes` equals `weylSign (nonResidueWeyl L u) = (-1)^{|nonResidueSupport|}`. -/
theorem prod_cyclotomicToBooleanSign_eq_weylSign
    (L : FormalPrimeRootLattice)
    (u : (ZMod (squarefreeCode L.primes))ˣ) :
    (∏ p : {p // p ∈ L.primes}, ((cyclotomicToBooleanSign L u p : ℤ) : ℝ)) =
      weylSign (nonResidueWeyl L u) := by
  classical
  have h1 :
      (∏ p : {p // p ∈ L.primes}, ((cyclotomicToBooleanSign L u p : ℤ) : ℝ)) =
        ∏ p ∈ L.primes.attach, ((cyclotomicToBooleanSign L u p : ℤ) : ℝ) := rfl
  rw [h1]
  have hterm :
      ∀ p ∈ L.primes.attach,
        ((cyclotomicToBooleanSign L u p : ℤ) : ℝ) =
          if cyclotomicToBooleanSign L u p = -1 then (-1 : ℝ) else 1 := by
    intro p _
    rcases Int.units_eq_one_or (cyclotomicToBooleanSign L u p) with hpos | hneg
    · rw [hpos]
      simp
    · rw [hneg]
      simp
  rw [Finset.prod_congr rfl hterm, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]
  unfold weylSign nonResidueWeyl
  congr 1
  symm
  refine Finset.card_bij
    (fun (p : ℕ) (hp : p ∈ L.primes.filter fun q =>
      ∃ hq : q ∈ L.primes, cyclotomicToBooleanSign L u ⟨q, hq⟩ = -1) =>
      (⟨p, (Finset.mem_filter.mp hp).1⟩ : {q // q ∈ L.primes}))
    ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpL, ⟨hpL', hneg⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hneg⟩
  · intro p₁ _ p₂ _ hEq
    exact congrArg Subtype.val hEq
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hneg⟩
    exact ⟨p.1, Finset.mem_filter.mpr ⟨p.2, ⟨p.2, hneg⟩⟩, Subtype.ext rfl⟩

end InfoGeometry.Algebra.CyclotomicQuadraticBooleanSignBridge
