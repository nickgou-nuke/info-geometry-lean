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

namespace InfoGeometry.Arithmetic.PrimeSuperalgebra

open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-! ## 1. Sector split -/

/--
Arithmetic sign/zeta channel.

These channels must not be collapsed:

* `bosonicZeta`: full bosonic primon trace, zeta channel;
* `squareFreeMobiusInverseZeta`: exterior square-free supertrace, Möbius/inverse-zeta channel;
* `liouvilleZetaRatio`: full integer sector with `(-1)^Ω(n)`, zeta-ratio channel;
* `distinctPrimeParity`: `(-1)^ω(n)` as a distinct-prime sign, not the Möbius function unless
  restricted to square-free states and zeroed off that sector.
-/
inductive PrimeSignChannel where
  | bosonicZeta
  | squareFreeMobiusInverseZeta
  | liouvilleZetaRatio
  | distinctPrimeParity
  deriving DecidableEq, Repr

/--
Generic prime superalgebra channel packet.

`degreeOmega` is total prime multiplicity `Ω`; `degreeOmegaDistinct` is distinct
prime count `ω`.  The `channel` field declares which arithmetic sign convention
is being used.
-/
structure PrimeSuperalgebraChannel where
  /-- State carrier. -/
  State : Type*
  /-- Total prime multiplicity, with repeated factors counted. -/
  degreeOmega : State → ℕ
  /-- Distinct prime count. -/
  degreeOmegaDistinct : State → ℕ
  /-- Arithmetic code/readout of a state. -/
  arithmeticCode : State → ℕ
  /-- Energy readout. -/
  energy : State → ℝ
  /-- Channel-dependent parity/sign. -/
  paritySign : State → ℤ
  /-- Declared arithmetic sign/zeta channel. -/
  channel : PrimeSignChannel
  /-- Partition or supertrace function. -/
  partitionFunction : ℂ → ℂ
  /-- Trace/supertrace law for this channel. -/
  traceLaw : Prop
  /-- Certificate of the trace/supertrace law. -/
  traceLawCertificate : traceLaw

/-- Any prime-superalgebra channel exports only its declared trace law. -/
theorem primeSuperalgebraChannel_traceLaw
    (C : PrimeSuperalgebraChannel) :
    C.traceLaw :=
  C.traceLawCertificate

/--
Bosonic full-integer sector descriptor.

This is the full multiplicative monoid sector.  If graded by total prime
multiplicity, its parity readout is Liouville-type, not the Möbius denominator.
-/
structure PrimeBosonAlgebra where
  /-- Integer-state carrier, usually a basis `|n⟩`. -/
  IntegerState : Type*
  /-- Multiplication of integer states. -/
  multiply : IntegerState → IntegerState → IntegerState
  /-- Total-prime-multiplicity grading witness, i.e. `Ω(n)`. -/
  totalMultiplicityGradingWitness : Type*
  /-- Guardrail: this sector does not produce the square-free Möbius denominator. -/
  liouville_not_mobius_guard : Type*

/--
Mixed boson/fermion sector descriptor.

The partition depends on which species are included.  It is not automatically
`ζ`, `1/ζ`, or `ζ(2s)/ζ(s)`.
-/
structure PrimeMixedSuperAlgebra where
  /-- Bosonic species carrier. -/
  BosonMode : Type*
  /-- Fermionic species carrier. -/
  FermionMode : Type*
  /-- Species-choice/weighting witness. -/
  speciesWitness : Type*
  /-- Guardrail: no automatic zeta-channel identification. -/
  noAutomaticZetaChannelGuard : Type*

/-! ## 2. Finite exterior prime algebra -/

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

/-! ## 3. Complex finite-volume zeta bridge -/

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

/--
Finite exterior prime algebra packet.

The square-free/Möbius interpretation is imported from `PrimeBitWittenIndex`,
which proves that the Möbius value of a square-free prime product is the
fermion parity.
-/
structure PrimeFermionExteriorAlgebra where
  /-- Finite prime cutoff. -/
  cutoff : PrimeCutoff
  /-- Exterior state carrier. -/
  State : Type*
  /-- Map from exterior states to occupied prime subsets. -/
  occupiedPrimes : State → Finset ℕ
  /-- Occupied primes lie in the cutoff. -/
  occupied_subset :
    ∀ ψ : State, occupiedPrimes ψ ⊆ cutoff.primes
  /-- Square-free/Möbius parity witness. -/
  mobiusParityWitness : Type*
  /-- Pauli exclusion guard: nonsquare-free states are not exterior states. -/
  squarefreeOnlyGuard : Type*

/--
Square-free fermionic prime channel.

The Möbius sign is `(-1)^ω` only on square-free/exterior states.  Non-square-free
integer states are not represented in this exterior state carrier; globally, the
Möbius function is zero on them.
-/
structure SquareFreeFermionicPrimeChannel where
  /-- State carrier for exterior/square-free states. -/
  State : Type*
  /-- Arithmetic integer code. -/
  code : State → ℕ
  /-- Square-free admissibility predicate. -/
  squareFree : State → Prop
  /-- Möbius/supertrace weight. -/
  mobiusWeight : State → ℤ
  /-- Energy readout. -/
  energy : State → ℝ
  /-- Supertrace readout. -/
  supertrace : ℂ → ℂ
  /-- Inverse-zeta or finite inverse-Euler-product law, supplied by the correct analytic/finite owner. -/
  inverseZetaLaw : Prop
  /-- Certificate of the inverse-zeta/finite-denominator law. -/
  inverseZetaCertificate : inverseZetaLaw

/-- Square-free fermionic supertrace exports only its supplied inverse-zeta law. -/
theorem squarefree_fermionic_supertrace_inverse_zeta
    (C : SquareFreeFermionicPrimeChannel) :
    C.inverseZetaLaw :=
  C.inverseZetaCertificate

/--
Koszul differential packet for the exterior prime algebra.

Arithmetic derivative and von Mangoldt readouts are not automatically odd
differentials.  A DG-superalgebra needs an explicit odd derivation and a proof
of `d² = 0`.
-/
structure PrimeKoszulDifferentialPacket
    (A Weight : Type*) where
  /-- Odd differential. -/
  d : A → A
  /-- Weight/readout assigned to prime generators, e.g. `log p`. -/
  weight : Weight
  /-- Odd Leibniz rule witness. -/
  oddLeibnizWitness : Type*
  /-- Nilpotence witness `d² = 0`. -/
  d_squared_zero_witness : Type*
  /-- Guardrail separating this differential from the arithmetic derivative. -/
  notArithmeticDerivativeGuard : Type*

end InfoGeometry.Arithmetic.PrimeSuperalgebra
