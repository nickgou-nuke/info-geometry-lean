import Mathlib
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.MobiusDirichletInverseBridge

/-!
# InfoGeometry.Arithmetic.PrimeSuperalgebra

Finite prime superalgebra / primon-gas readouts.

This file separates the theorem-safe finite readouts:

* bosonic all-natural-number trace: finite reciprocal product;
* fermionic square-free ordinary trace: finite positive square-free product;
* signed fermionic exterior supertrace: finite Weyl/Euler denominator;
* full boson-fermion SUSY product: finite cancellation, gated by nonzero local
  factors.

The square-free exterior/Fock sector is different from the full natural-number
monoid algebra: occupied exterior states are finite prime subsets, parity is
`(-1)^ω`, and nonsquare-free states are absent.  Möbius is therefore exterior
parity with square-free projection, not raw parity on all integer states.

This module proves finite product identities such as:

```text
sum_{S subset P} (-1)^|S| prod_{p in S} exp(-beta log p)
  = prod_{p in P} (1 - exp(-beta log p)).
```

No analytic continuation, no zeta-zero statement, and no claim that an
arithmetic derivative is a differential are made here.
-/

noncomputable section

open scoped BigOperators

namespace PrimeSuperalgebra

open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-! ## 1. Finite exterior prime algebra -/

/-- A finite prime cutoff is a certified finite register of primes. -/
abbrev PrimeCutoff :=
  PrimeRegister

/-- A finite exterior/Fock state is a subset of the prime cutoff. -/
abbrev ExteriorState (P : PrimeCutoff) :=
  {S : Finset ℕ // S ⊆ P.primes}

/-- Fermion parity of a finite exterior state. -/
def parity {P : PrimeCutoff} (S : ExteriorState P) : ℤ :=
  (-1 : ℤ) ^ S.1.card

/-- Prime energy `log p`. -/
def primeEnergy (p : ℕ) : ℝ :=
  Real.log (p : ℝ)

/-- Local Boltzmann weight `exp(-β log p)`. -/
def primeWeight (β : ℝ) (p : ℕ) : ℝ :=
  Real.exp (-(β * primeEnergy p))

/-- Energy of a finite exterior/Fock state: sum of occupied prime energies. -/
def stateEnergy {P : PrimeCutoff} (S : ExteriorState P) : ℝ :=
  ∑ p ∈ S.1, primeEnergy p

/-- Boltzmann weight of a finite exterior/Fock state: product of occupied local weights. -/
def stateWeight {P : PrimeCutoff} (β : ℝ) (S : ExteriorState P) : ℝ :=
  ∏ p ∈ S.1, primeWeight β p

/-- Finite fermionic prime supertrace: the finite square-free/Möbius readout. -/
def finitePrimeSupertrace (P : PrimeCutoff) (β : ℝ) : ℝ :=
  ∑ S ∈ P.primes.powerset,
    (((-1 : ℤ) ^ S.card : ℤ) : ℝ) * (∏ p ∈ S, primeWeight β p)

/-- Finite Euler/Weyl denominator over the prime cutoff. -/
def finitePrimeDenominator (P : PrimeCutoff) (β : ℝ) : ℝ :=
  ∏ p ∈ P.primes, (1 - primeWeight β p)

lemma finitePrimeDenominator_ne_zero
    (P : PrimeCutoff) (β : ℝ)
    (h : ∀ p ∈ P.primes, (1 - primeWeight β p) ≠ 0) :
    finitePrimeDenominator P β ≠ 0 := by
  unfold finitePrimeDenominator
  exact Finset.prod_ne_zero_iff.mpr h

/--
Unsigned finite fermionic square-free partition:

```text
sum_{S subset P} prod_{p in S} w_p = prod_{p in P} (1 + w_p).
```

This is the finite precursor of the `ζ(s) / ζ(2s)` square-free channel, not the
inverse-zeta supertrace.
-/
def finiteFermionicSquarefreePartition (P : PrimeCutoff) (β : ℝ) : ℝ :=
  ∑ S ∈ P.primes.powerset, ∏ p ∈ S, primeWeight β p

/-- Finite unsigned fermionic square-free product. -/
def finiteSquarefreeProduct (P : PrimeCutoff) (β : ℝ) : ℝ :=
  ∏ p ∈ P.primes, (1 + primeWeight β p)

/--
Finite bosonic prime-gas partition function.

This is the finite reciprocal product precursor of the bosonic zeta channel.
-/
def finiteBosonicPrimePartition (P : PrimeCutoff) (β : ℝ) : ℝ :=
  (finitePrimeDenominator P β)⁻¹

/-- Finite signed-supertrace partition inverse. -/
def finiteSignedPrimePartition (P : PrimeCutoff) (β : ℝ) : ℝ :=
  (finitePrimeDenominator P β)⁻¹

lemma finiteBosonicPrimePartition_ne_zero
    (P : PrimeCutoff) (β : ℝ)
    (h : finitePrimeDenominator P β ≠ 0) :
    finiteBosonicPrimePartition P β ≠ 0 := by
  unfold finiteBosonicPrimePartition
  exact inv_ne_zero h

/--
Finite full SUSY product readout.

This models the finite boson-fermion cancellation product.  The equality to `1`
requires the local nonzero gate `1 - w_p ≠ 0`.
-/
def finiteFullSUSYProduct (P : PrimeCutoff) (β : ℝ) : ℝ :=
  finiteBosonicPrimePartition P β * finitePrimeDenominator P β

/--
The finite exterior prime supertrace equals the finite Euler/Weyl denominator.

Mathematically:

```text
sum_{S subset P} (-1)^|S| prod_{p in S} w_p = prod_{p in P} (1 - w_p).
```
-/
theorem finitePrimeSupertrace_eq_denominator
    (P : PrimeCutoff) (β : ℝ) :
    finitePrimeSupertrace P β = finitePrimeDenominator P β := by
  classical
  unfold finitePrimeSupertrace finitePrimeDenominator
  calc
    (∑ S ∈ P.primes.powerset,
      (((-1 : ℤ) ^ S.card : ℤ) : ℝ) * (∏ p ∈ S, primeWeight β p))
        =
      ∑ S ∈ P.primes.powerset,
        (-1 : ℝ) ^ S.card * (∏ p ∈ S, primeWeight β p) := by
        refine Finset.sum_congr rfl ?_
        intro S _hS
        simp
    _ =
      ∑ S ∈ P.primes.powerset,
        (-1 : ℝ) ^ S.card * (∏ p ∈ P.primes \ S, (1 : ℝ)) *
          (∏ p ∈ S, primeWeight β p) := by
        refine Finset.sum_congr rfl ?_
        intro S _hS
        simp
    _ = ∏ p ∈ P.primes, (1 - primeWeight β p) := by
        exact (Finset.prod_sub (fun _ : ℕ => (1 : ℝ)) (primeWeight β) P.primes).symm

/--
The finite ordinary fermionic square-free partition equals the finite positive
square-free product.

Mathematically:

```text
sum_{S subset P} prod_{p in S} w_p = prod_{p in P} (1 + w_p).
```
-/
theorem finiteFermionicSquarefreePartition_eq_product
    (P : PrimeCutoff) (β : ℝ) :
    finiteFermionicSquarefreePartition P β =
      finiteSquarefreeProduct P β := by
  classical
  unfold finiteFermionicSquarefreePartition finiteSquarefreeProduct
  calc
    (∑ S ∈ P.primes.powerset, ∏ p ∈ S, primeWeight β p)
        =
      ∑ S ∈ P.primes.powerset,
        (∏ p ∈ S, primeWeight β p) * (∏ p ∈ P.primes \ S, (1 : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro S _hS
        simp
    _ = ∏ p ∈ P.primes, (1 + primeWeight β p) := by
        rw [show (∏ p ∈ P.primes, (1 + primeWeight β p))
            = ∏ p ∈ P.primes, (primeWeight β p + 1) by
              refine Finset.prod_congr rfl ?_
              intro p _hp
              ring]
        exact (Finset.prod_add (primeWeight β) (fun _ : ℕ => (1 : ℝ)) P.primes).symm

/--
The finite full SUSY product cancels to `1` when the local denominator factors
are nonzero.
-/
theorem finiteFullSUSYProduct_eq_one
    (P : PrimeCutoff) (β : ℝ)
    (hdenom : finitePrimeDenominator P β ≠ 0) :
    finiteFullSUSYProduct P β = 1 := by
  unfold finiteFullSUSYProduct finiteBosonicPrimePartition
  exact inv_mul_cancel₀ hdenom

/-! ## 3. Möbius interpretation and differential guardrails -/

/-! ## 2. Complex finite-volume zeta bridge -/

/-- Complex one-prime Boltzmann/Mellin weight `p^{-s}`. -/
def complexPrimeWeight
    (s : ℂ)
    (p : Nat.Primes) : ℂ :=
  ((p : ℕ) : ℂ) ^ (-s)

/--
Finite-volume bosonic primon partition over a finite prime cutoff.

This is the finite reciprocal Euler product, not the fermionic exterior sector.
-/
def finiteComplexBosonPartition
    (S : Finset Nat.Primes)
    (s : ℂ) : ℂ :=
  ∏ p ∈ S, (1 - complexPrimeWeight s p)⁻¹

/--
Finite-volume fermionic exterior supertrace over a finite prime cutoff.

A basis vector is a subset `T ⊆ S`, and the parity insertion contributes the
local signed factor `-p^{-s}` for every occupied prime.
-/
def finiteComplexFermionSupertrace
    (S : Finset Nat.Primes)
    (s : ℂ) : ℂ :=
  ∑ T ∈ S.powerset, ∏ p ∈ T, (-complexPrimeWeight s p)

@[simp]
theorem finiteComplexFermionSupertrace_empty
    (s : ℂ) :
    finiteComplexFermionSupertrace (∅ : Finset Nat.Primes) s = 1 := by
  simp [finiteComplexFermionSupertrace]

@[simp]
theorem finiteComplexBosonPartition_empty
    (s : ℂ) :
    finiteComplexBosonPartition (∅ : Finset Nat.Primes) s = 1 := by
  simp [finiteComplexBosonPartition]

lemma finiteComplexBosonPartition_ne_zero
    (S : Finset Nat.Primes) (s : ℂ)
    (h : ∀ p ∈ S, (1 - complexPrimeWeight s p) ≠ 0) :
    finiteComplexBosonPartition S s ≠ 0 := by
  unfold finiteComplexBosonPartition
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => inv_ne_zero (h p hp))

/--
Finite fermionic Euler product identity:

`STr_F(e^{-sH}) = ∏_{p∈S} (1 - p^{-s})`.
-/
theorem finiteComplexFermionSupertrace_eq_eulerProduct
    (S : Finset Nat.Primes)
    (s : ℂ) :
    finiteComplexFermionSupertrace S s =
      ∏ p ∈ S, (1 - complexPrimeWeight s p) := by
  unfold finiteComplexFermionSupertrace
  simpa [sub_eq_add_neg, complexPrimeWeight] using
    (Finset.prod_one_add (s := S) (f := fun p : Nat.Primes => -complexPrimeWeight s p)).symm

/-- The infinite bosonic Euler product used by Mathlib's zeta theorem. -/
def infiniteComplexBosonicEulerProduct
    (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, (1 - complexPrimeWeight s p)⁻¹

/--
Mathlib bridge: in the convergence half-plane, the infinite bosonic primon
partition function is the Riemann zeta function.
-/
theorem infiniteComplexBosonicEulerProduct_eq_riemannZeta
    {s : ℂ}
    (hs : 1 < s.re) :
    infiniteComplexBosonicEulerProduct s = riemannZeta s := by
  simpa [infiniteComplexBosonicEulerProduct, complexPrimeWeight] using
    riemannZeta_eulerProduct_tprod hs

/--
Infinite positive-fermion ratio readout built from two bosonic Euler products.

This is the honest infinite ratio lane for the square-free/positive fermion
factor.  It is not a separate proof that `∏ₚ (1 + p^{-s})` converges; instead it
uses the already-owned bosonic Euler products at `s` and `2s`.
-/
def infiniteComplexPositiveFermionZetaRatio (s : ℂ) : ℂ :=
  infiniteComplexBosonicEulerProduct s *
    (infiniteComplexBosonicEulerProduct ((2 : ℂ) * s))⁻¹

/--
Infinite order-`κ` parafermion ratio readout built from bosonic Euler products.

This is the zeta-ratio owner surface for the expected parafermion identity;
the direct infinite product and finite-to-infinite limit are deliberately not
asserted here.
-/
def infiniteComplexParafermionZetaRatio (κ : ℕ) (s : ℂ) : ℂ :=
  infiniteComplexBosonicEulerProduct s *
    (infiniteComplexBosonicEulerProduct ((κ : ℂ) * s))⁻¹

/--
Positive-fermion infinite ratio readout equals `ζ(s) / ζ(2s)` on the convergence domain.
-/
theorem infiniteComplexPositiveFermionZetaRatio_eq_zeta_div_zeta_two
    {s : ℂ}
    (hs : 1 < s.re)
    (hs2 : 1 < (((2 : ℂ) * s).re)) :
    infiniteComplexPositiveFermionZetaRatio s =
      riemannZeta s / riemannZeta ((2 : ℂ) * s) := by
  unfold infiniteComplexPositiveFermionZetaRatio
  rw [infiniteComplexBosonicEulerProduct_eq_riemannZeta hs,
    infiniteComplexBosonicEulerProduct_eq_riemannZeta hs2]
  rfl

/--
Order-`κ` parafermion infinite ratio readout equals `ζ(s) / ζ(κs)` on the convergence domain.
-/
theorem infiniteComplexParafermionZetaRatio_eq_zeta_div_zeta_mul
    (κ : ℕ) {s : ℂ}
    (hs : 1 < s.re)
    (hκs : 1 < (((κ : ℂ) * s).re)) :
    infiniteComplexParafermionZetaRatio κ s =
      riemannZeta s / riemannZeta ((κ : ℂ) * s) := by
  unfold infiniteComplexParafermionZetaRatio
  rw [infiniteComplexBosonicEulerProduct_eq_riemannZeta hs,
    infiniteComplexBosonicEulerProduct_eq_riemannZeta hκs]
  rfl

/-- The order-two parafermion ratio readout is the positive-fermion ratio readout. -/
theorem infiniteComplexParafermionZetaRatio_two_eq_positiveFermion
    (s : ℂ) :
    infiniteComplexParafermionZetaRatio 2 s = infiniteComplexPositiveFermionZetaRatio s := by
  rfl

/--
Reciprocal-zeta readout, stated as the inverse of the bosonic Euler product.

This avoids pretending that the non-inverted infinite fermionic product is
already installed as a separate theorem owner.
-/
theorem inverse_infiniteComplexBosonicEulerProduct_eq_inverse_riemannZeta
    {s : ℂ}
    (hs : 1 < s.re) :
    (infiniteComplexBosonicEulerProduct s)⁻¹ = (riemannZeta s)⁻¹ := by
  exact congrArg (fun z : ℂ => z⁻¹)
    (infiniteComplexBosonicEulerProduct_eq_riemannZeta hs)

end PrimeSuperalgebra
