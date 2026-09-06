import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Arithmetic.PrimeSuperalgebra

/-!
# Prime-gas partition functions

Finite traces are explicit products.  Infinite traces are actual complex
functions tied to Mathlib's Riemann-zeta Euler product; no arbitrary values or
equality fields are stored in witness structures.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeGasPartitions

open scoped BigOperators
open FormalPrimeRootSystem
open InfoGeometry.Arithmetic.PrimeSuperalgebra

/-! ## Finite prime traces -/

/-- Finite bosonic prime trace `∏ (1-xₚ)⁻¹`. -/
@[rep_depth thermo]
def finiteBosonTrace
    (L : FormalPrimeRootLattice)
    (x : ℕ → ℝ) : ℝ :=
  ∏ p ∈ L.primes, (1 - x p)⁻¹

/-- Finite positive fermion trace `∏ (1+xₚ)`. -/
@[rep_depth thermo]
def finiteFermionTrace
    (L : FormalPrimeRootLattice)
    (x : ℕ → ℝ) : ℝ :=
  ∏ p ∈ L.primes, (1 + x p)

/-- Finite parity supertrace `∏ (1-xₚ)`. -/
@[rep_depth thermo]
def finiteParityTrace
    (L : FormalPrimeRootLattice)
    (x : ℕ → ℝ) : ℝ :=
  ∏ p ∈ L.primes, (1 - x p)

/-- The finite boson and parity traces cancel when no denominator vanishes. -/
@[rep_depth thermo]
theorem finiteBosonTrace_mul_finiteParityTrace
    (L : FormalPrimeRootLattice)
    (x : ℕ → ℝ)
    (hx : ∀ p ∈ L.primes, 1 - x p ≠ 0) :
    finiteBosonTrace L x * finiteParityTrace L x = 1 := by
  classical
  unfold finiteBosonTrace finiteParityTrace
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p hp
  simp [hx p hp]

/--
Positive fermion times parity equals the product with squared prime weights.
-/
@[rep_depth thermo]
theorem finiteFermionTrace_mul_finiteParityTrace
    (L : FormalPrimeRootLattice)
    (x : ℕ → ℝ) :
    finiteFermionTrace L x * finiteParityTrace L x =
      ∏ p ∈ L.primes, (1 - (x p) ^ 2) := by
  classical
  unfold finiteFermionTrace finiteParityTrace
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  ring

/-! ## Infinite complex traces -/

/-- Infinite bosonic prime trace. -/
def infiniteBosonTrace (s : ℂ) : ℂ :=
  infiniteComplexBosonicEulerProduct s

/-- Infinite positive-fermion zeta-ratio channel. -/
def infiniteFermionTrace (s : ℂ) : ℂ :=
  infiniteComplexPositiveFermionZetaRatio s

/-- Infinite parity channel, defined as the reciprocal bosonic product. -/
def infiniteParityTrace (s : ℂ) : ℂ :=
  (infiniteBosonTrace s)⁻¹

/--
Proof-carrying half-plane context for the genuine infinite Euler products.
-/
@[rep_depth thermo]
structure InfiniteEulerProductConvergenceWitness where
  s : ℂ
  halfPlane_Re_gt_one : 1 < s.re

namespace InfiniteEulerProductConvergenceWitness

def zeta (W : InfiniteEulerProductConvergenceWitness) : ℂ :=
  riemannZeta W.s

def zeta_two_beta (W : InfiniteEulerProductConvergenceWitness) : ℂ :=
  riemannZeta ((2 : ℂ) * W.s)

def inverseZeta (W : InfiniteEulerProductConvergenceWitness) : ℂ :=
  (riemannZeta W.s)⁻¹

def bosonTrace (W : InfiniteEulerProductConvergenceWitness) : ℂ :=
  infiniteBosonTrace W.s

def fermionTrace (W : InfiniteEulerProductConvergenceWitness) : ℂ :=
  infiniteFermionTrace W.s

def parityTrace (W : InfiniteEulerProductConvergenceWitness) : ℂ :=
  infiniteParityTrace W.s

end InfiniteEulerProductConvergenceWitness

/-- The bosonic trace is Riemann zeta on `Re(s)>1`. -/
@[rep_depth thermo]
theorem infiniteBosonTrace_eq_riemannZeta
    {s : ℂ}
    (hs : 1 < s.re) :
    infiniteBosonTrace s = riemannZeta s :=
  infiniteComplexBosonicEulerProduct_eq_riemannZeta hs

/-- The parity trace is inverse Riemann zeta on `Re(s)>1`. -/
@[rep_depth thermo]
theorem infiniteParityTrace_eq_inverse_riemannZeta
    {s : ℂ}
    (hs : 1 < s.re) :
    infiniteParityTrace s = (riemannZeta s)⁻¹ := by
  unfold infiniteParityTrace infiniteBosonTrace
  exact inverse_infiniteComplexBosonicEulerProduct_eq_inverse_riemannZeta hs

/-- The positive fermion trace is `ζ(s)/ζ(2s)` on `Re(s)>1`. -/
@[rep_depth thermo]
theorem infiniteFermionTrace_eq_zeta_div_zeta_two
    {s : ℂ}
    (hs : 1 < s.re) :
    infiniteFermionTrace s =
      riemannZeta s / riemannZeta ((2 : ℂ) * s) := by
  unfold infiniteFermionTrace
  apply infiniteComplexPositiveFermionZetaRatio_eq_zeta_div_zeta_two hs
  have htwo : (((2 : ℂ) * s).re) = 2 * s.re := by
    norm_num [Complex.mul_re]
  rw [htwo]
  linarith

@[rep_depth thermo]
theorem bosonTrace_eq_zeta (W : InfiniteEulerProductConvergenceWitness) :
    W.bosonTrace = W.zeta :=
  infiniteBosonTrace_eq_riemannZeta W.halfPlane_Re_gt_one

@[rep_depth thermo]
theorem fermionTrace_eq_zeta_div_zeta_two_beta
    (W : InfiniteEulerProductConvergenceWitness) :
    W.fermionTrace = W.zeta / W.zeta_two_beta :=
  infiniteFermionTrace_eq_zeta_div_zeta_two W.halfPlane_Re_gt_one

@[rep_depth thermo]
theorem parityTrace_eq_inverse_zeta
    (W : InfiniteEulerProductConvergenceWitness) :
    W.parityTrace = W.inverseZeta :=
  infiniteParityTrace_eq_inverse_riemannZeta W.halfPlane_Re_gt_one

/-! The native equality relation identifying parity and supertrace readouts.

The certified prime cutoff underlying a formal Boolean prime-root lattice.

This is the concrete carrier conversion needed to compare the Weyl parity
product with the exterior-prime-algebra supertrace.  Both owners retain their
own semantic types; only their common finite prime register is identified.
-/
def primeCutoffOfRootLattice (L : FormalPrimeRootLattice) : PrimeCutoff where
  val := L.primes
  property := L.prime_mem

/--
The finite parity product is the genuine exterior-prime-algebra supertrace.

This replaces the former equality-witness packet by a theorem between the
actual owners: the Boolean prime-root lattice on the left and the finite
exterior prime superalgebra on the right.
-/
@[rep_depth thermo]
theorem finiteParityTrace_eq_finitePrimeSupertrace
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finiteParityTrace L (primeWeight β) =
      finitePrimeSupertrace (primeCutoffOfRootLattice L) β := by
  rw [finitePrimeSupertrace_eq_denominator]
  simp [finiteParityTrace, finitePrimeDenominator, primeCutoffOfRootLattice]

/--
Compatibility spelling for the recovered split parity/supertrace theorem.

Unlike the historical record field, this statement has no freely supplied
readouts: both sides are computed from the same certified prime modes.
-/
@[rep_depth thermo]
theorem parityTrace_eq_supertrace
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finiteParityTrace L (primeWeight β) =
      finitePrimeSupertrace (primeCutoffOfRootLattice L) β :=
  finiteParityTrace_eq_finitePrimeSupertrace L β

end InfoGeometry.Canonical.PrimeGasPartitions
