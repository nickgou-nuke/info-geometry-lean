import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import InfoGeometry.Meta.Architecture
import InfoGeometry.Arithmetic.MobiusDirichletInverseBridge

/-!
# Finite inverse-zeta cutoffs and their filtered limit

This module uses the actual finite Möbius Dirichlet polynomial and fermionic
Euler product.  It contains no equality field and no reflexive limit witness.
The infinite statement is represented by Mathlib's `Filter.Tendsto`.
-/

noncomputable section

namespace InfoGeometry.Canonical.AnalyticLimit

open Filter
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.MobiusDirichletInverseBridge

/-- Prime weight `p^{-β}` in the complex Euler product. -/
@[rep_depth thermo]
def primeWeight (β : ℝ) (p : ℕ) : ℂ :=
  (p : ℂ) ^ (-(β : ℂ))

/-- The genuine finite inverse-zeta Euler cutoff. -/
@[rep_depth thermo]
def finiteInverseZeta (P : PrimeRegister) (β : ℝ) : ℂ :=
  finiteFermionicEulerProduct P (primeWeight β)

/-- The genuine finite Möbius Dirichlet cutoff. -/
@[rep_depth thermo]
def finiteMobiusInverseZeta (P : PrimeRegister) (β : ℝ) : ℂ :=
  finiteMobiusDirichletPolynomial P (primeWeight β)

/-- Finite Möbius inversion is exactly the finite fermionic Euler product. -/
@[rep_depth thermo]
theorem finiteMobiusInverseZeta_eq_finiteInverseZeta
    (P : PrimeRegister)
    (β : ℝ) :
    finiteMobiusInverseZeta P β = finiteInverseZeta P β :=
  finiteMobiusDirichletPolynomial_eq_finiteFermionicEulerProduct
    P (primeWeight β)

/-- Native product of a genuine prime register and its inverse temperature. -/
@[rep_depth thermo]
abbrev FinitePrimeCutoffDirichletData :=
  PrimeRegister × ℝ

namespace FinitePrimeCutoffDirichletData

/-- Prime-register projection from the native product owner. -/
abbrev primes (D : FinitePrimeCutoffDirichletData) : PrimeRegister :=
  D.1

/-- Inverse-temperature projection from the native product owner. -/
abbrev beta (D : FinitePrimeCutoffDirichletData) : ℝ :=
  D.2

/-- Genuine finite Euler-product readout of the cutoff packet. -/
def finiteEulerProduct (D : FinitePrimeCutoffDirichletData) : ℂ :=
  finiteInverseZeta D.primes D.beta

/-- Genuine finite Möbius-Dirichlet readout of the cutoff packet. -/
def finiteDirichletPolynomial
    (D : FinitePrimeCutoffDirichletData) : ℂ :=
  finiteMobiusInverseZeta D.primes D.beta

/-- The packet's two finite readouts agree by the native Möbius theorem. -/
theorem finiteEuler_eq_dirichlet
    (D : FinitePrimeCutoffDirichletData) :
    D.finiteEulerProduct = D.finiteDirichletPolynomial := by
  symm
  exact finiteMobiusInverseZeta_eq_finiteInverseZeta D.primes D.beta

end FinitePrimeCutoffDirichletData

/-- Restored finite-packet readout without shadowing the native owner. -/
@[rep_depth thermo]
def finiteInverseZetaData
    (D : FinitePrimeCutoffDirichletData) : ℂ :=
  finiteInverseZeta D.primes D.beta

/-- Finite packet readout is exactly its genuine Euler product. -/
@[rep_depth thermo]
theorem finiteInverseZeta_eq_finiteEulerProduct
    (D : FinitePrimeCutoffDirichletData) :
    finiteInverseZetaData D = D.finiteEulerProduct :=
  rfl

/-! ## Native infinite owner -/

/--
The full bosonic prime Euler product at inverse temperature `β`.

Unlike the historical `limitingInverseZeta` field, this is an actual Mathlib
infinite product over `Nat.Primes`.
-/
@[rep_depth thermo]
def infinitePrimeEulerProduct (β : ℝ) : ℂ :=
  ∏' p : Nat.Primes,
    (1 - (p : ℂ) ^ (-(β : ℂ)))⁻¹

/-- The genuine infinite inverse-zeta readout. -/
@[rep_depth thermo]
def infiniteInverseZeta (β : ℝ) : ℂ :=
  (infinitePrimeEulerProduct β)⁻¹

/--
Mathlib's Euler-product theorem identifies the full prime product with the
Riemann zeta function on the absolute-convergence half-plane.
-/
@[rep_depth thermo]
theorem infinitePrimeEulerProduct_eq_riemannZeta
    {β : ℝ}
    (hβ : 1 < β) :
    infinitePrimeEulerProduct β = riemannZeta (β : ℂ) := by
  have hs : 1 < ((β : ℂ).re) := by
    simpa using hβ
  simpa [infinitePrimeEulerProduct] using
    (riemannZeta_eulerProduct_tprod (s := (β : ℂ)) hs)

/--
The infinite inverse Euler product is genuinely inverse zeta.

This recovers the mathematical target of the deleted
`limitingInverseZeta`/`inverseZeta_eq_limit` fields without storing either
side or their equality as evidence.
-/
@[rep_depth thermo]
theorem infiniteInverseZeta_eq_inverse_riemannZeta
    {β : ℝ}
    (hβ : 1 < β) :
    infiniteInverseZeta β = (riemannZeta (β : ℂ))⁻¹ := by
  unfold infiniteInverseZeta
  rw [infinitePrimeEulerProduct_eq_riemannZeta hβ]

/-- A directed sequence of finite prime registers. -/
abbrev PrimeCutoffSystem :=
  ℕ → PrimeRegister

/-- Finite Euler cutoffs along a directed prime-register system. -/
@[rep_depth thermo]
def finiteInverseZetaAlong
    (P : PrimeCutoffSystem)
    (β : ℝ) :
    ℕ → ℂ :=
  fun n => finiteInverseZeta (P n) β

/-- Finite Möbius cutoffs along the same directed system. -/
@[rep_depth thermo]
def finiteMobiusInverseZetaAlong
    (P : PrimeCutoffSystem)
    (β : ℝ) :
    ℕ → ℂ :=
  fun n => finiteMobiusInverseZeta (P n) β

/--
The honest inverse-zeta convergence proposition for a specified cutoff
system.  No convergence is asserted merely by constructing data.
-/
@[rep_depth thermo]
def ConvergesToInverseZeta
    (P : PrimeCutoffSystem)
    (β : ℝ) : Prop :=
  Tendsto
    (finiteInverseZetaAlong P β)
    atTop
    (nhds (riemannZeta (β : ℂ))⁻¹)

/--
Direct inverse-zeta convergence theorem.

The former `AnalyticLimitWitness` merely repackaged these hypotheses and then
projected the supplied `Tendsto` field.  The actual analytic owner is the
Mathlib `Filter.Tendsto` proposition itself.
-/
@[rep_depth thermo]
theorem inverseZeta_eq_tendsto_finiteInverseZeta
    (P : PrimeCutoffSystem)
    (β : ℝ)
    (_hβ : 1 < β)
    (hconv : ConvergesToInverseZeta P β) :
    Tendsto
      (finiteInverseZetaAlong P β)
      atTop
      (nhds (riemannZeta (β : ℂ))⁻¹) :=
  hconv

/--
Equivalent formulation with the proved infinite Euler-product owner as the
limit target.
-/
@[rep_depth thermo]
theorem convergesToInverseZeta_iff_tendsto_infiniteInverseZeta
    (P : PrimeCutoffSystem)
    {β : ℝ}
    (hβ : 1 < β) :
    ConvergesToInverseZeta P β ↔
      Tendsto
        (finiteInverseZetaAlong P β)
        atTop
        (nhds (infiniteInverseZeta β)) := by
  rw [infiniteInverseZeta_eq_inverse_riemannZeta hβ]
  rfl

/-- Möbius and Euler cutoff sequences are pointwise identical. -/
@[rep_depth thermo]
theorem finiteMobiusInverseZetaAlong_eq_finiteInverseZetaAlong
    (P : PrimeCutoffSystem)
    (β : ℝ) :
    finiteMobiusInverseZetaAlong P β =
      finiteInverseZetaAlong P β := by
  funext n
  exact finiteMobiusInverseZeta_eq_finiteInverseZeta (P n) β

/--
Convergence of the Möbius cutoffs is equivalent to convergence of the Euler
cutoffs, because the finite-stage functions are definitionally connected by
the proved finite product theorem.
-/
@[rep_depth thermo]
theorem tendsto_finiteMobiusInverseZeta_iff
    (P : PrimeCutoffSystem)
    (β : ℝ) :
    Tendsto
        (finiteMobiusInverseZetaAlong P β)
        atTop
        (nhds (riemannZeta (β : ℂ))⁻¹) ↔
      ConvergesToInverseZeta P β := by
  rw [finiteMobiusInverseZetaAlong_eq_finiteInverseZetaAlong]
  rfl

end InfoGeometry.Canonical.AnalyticLimit
