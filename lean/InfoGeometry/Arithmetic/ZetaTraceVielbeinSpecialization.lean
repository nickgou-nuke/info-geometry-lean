/- 
InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean

Prime-indexed zeta-trace specialization of the vielbein readout.

The primes are treated as discrete local frame indices.  The formal interface
is deliberately modest:

* local Jacobian factor `1 - p^(-s)`
* trace-log effective action `∑' -log(1 - p^(-s))`
* exponentiated supervolume `exp(action)`
* Euler-product supervolume `∏' (1 - p^(-s))⁻¹`

The only convergence gate used here is the standard `1 < s.re` half-plane.
No Clifford/Berezinian operator realization is asserted at this layer.
-/

import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic

/-! ### 1. Local prime frame data -/

/-- Local diagonal Jacobian factor attached to a prime. -/
def primeLocalJacobian (p : Nat.Primes) (s : ℂ) : ℂ :=
  1 - ((p : ℕ) : ℂ) ^ (-s)

/-- Local reciprocal volume factor attached to a prime. -/
def primeLocalVolumeFactor (p : Nat.Primes) (s : ℂ) : ℂ :=
  (primeLocalJacobian p s)⁻¹

lemma primeLocalVolumeFactor_ne_zero {p : Nat.Primes} {s : ℂ}
    (h : primeLocalJacobian p s ≠ 0) :
    primeLocalVolumeFactor p s ≠ 0 := by
  unfold primeLocalVolumeFactor
  exact inv_ne_zero h

/-- Local trace-log contribution to the effective action. -/
def primeLocalEffectiveAction (p : Nat.Primes) (s : ℂ) : ℂ :=
  -Complex.log (primeLocalJacobian p s)

/-! ### 2. Global zeta-trace readouts -/

/-- Trace-log effective action. -/
def zetaTraceEffectiveAction (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, primeLocalEffectiveAction p s

/-- Exponentiated trace-log supervolume. -/
def zetaTraceSupervolume (s : ℂ) : ℂ :=
  Complex.exp (zetaTraceEffectiveAction s)

lemma zetaTraceSupervolume_ne_zero (s : ℂ) :
    zetaTraceSupervolume s ≠ 0 := by
  unfold zetaTraceSupervolume
  exact Complex.exp_ne_zero _

/-- Direct Euler-product supervolume. -/
def zetaTraceEulerSupervolume (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, primeLocalVolumeFactor p s

@[simp]
theorem primeLocalJacobian_def (p : Nat.Primes) (s : ℂ) :
    primeLocalJacobian p s = 1 - ((p : ℕ) : ℂ) ^ (-s) :=
  rfl

@[simp]
theorem primeLocalVolumeFactor_def (p : Nat.Primes) (s : ℂ) :
    primeLocalVolumeFactor p s = (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ :=
  rfl

@[simp]
theorem primeLocalEffectiveAction_def (p : Nat.Primes) (s : ℂ) :
    primeLocalEffectiveAction p s = -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) :=
  rfl

/-- Euler-product readout equals `riemannZeta` on the standard half-plane. -/
theorem zetaTraceEulerSupervolume_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    zetaTraceEulerSupervolume s = riemannZeta s := by
  simpa [zetaTraceEulerSupervolume, primeLocalVolumeFactor, primeLocalJacobian]
    using (riemannZeta_eulerProduct_tprod hs)

/--
Trace-log supervolume readout equals `riemannZeta` on the standard half-plane.

This is the exponentiated trace-log form of the Euler product.
-/
theorem zetaTraceSupervolume_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    zetaTraceSupervolume s = riemannZeta s := by
  simpa [zetaTraceSupervolume, zetaTraceEffectiveAction, primeLocalEffectiveAction,
    primeLocalJacobian]
    using (riemannZeta_eulerProduct_exp_log hs)

/-- The trace-log and Euler-product supervolumes agree on the standard half-plane. -/
theorem zetaTraceSupervolume_eq_eulerSupervolume
    {s : ℂ} (hs : 1 < s.re) :
    zetaTraceSupervolume s = zetaTraceEulerSupervolume s := by
  calc
    zetaTraceSupervolume s = riemannZeta s := zetaTraceSupervolume_eq_riemannZeta hs
    _ = zetaTraceEulerSupervolume s := (zetaTraceEulerSupervolume_eq_riemannZeta hs).symm

/-! ### 3. Carrier packaging -/

/--
Prime-gas vielbein carrier.

This packages the local Jacobians, global trace-log action, and both
supervolume readouts as a single interface.
-/
structure PrimeVielbeinCarrier where
  convergenceDomain : ℂ → Prop
  localJacobian : Nat.Primes → ℂ → ℂ
  localVolumeFactor : Nat.Primes → ℂ → ℂ
  localEffectiveAction : Nat.Primes → ℂ → ℂ
  effectiveAction : ℂ → ℂ
  traceLogSupervolume : ℂ → ℂ
  eulerSupervolume : ℂ → ℂ

/-- Canonical zeta-trace prime-vielbein carrier. -/
def canonicalPrimeVielbein : PrimeVielbeinCarrier where
  convergenceDomain := fun s => 1 < s.re
  localJacobian := primeLocalJacobian
  localVolumeFactor := primeLocalVolumeFactor
  localEffectiveAction := primeLocalEffectiveAction
  effectiveAction := zetaTraceEffectiveAction
  traceLogSupervolume := zetaTraceSupervolume
  eulerSupervolume := zetaTraceEulerSupervolume

@[simp]
theorem canonicalPrimeVielbein_convergenceDomain
    (s : ℂ) :
    canonicalPrimeVielbein.convergenceDomain s ↔ 1 < s.re :=
  Iff.rfl

@[simp]
theorem canonicalPrimeVielbein_traceLogSupervolume
    (s : ℂ) :
    canonicalPrimeVielbein.traceLogSupervolume s = zetaTraceSupervolume s :=
  rfl

@[simp]
theorem canonicalPrimeVielbein_eulerSupervolume
    (s : ℂ) :
    canonicalPrimeVielbein.eulerSupervolume s = zetaTraceEulerSupervolume s :=
  rfl

/-- Canonical trace-log readout equals `riemannZeta` on the standard half-plane. -/
theorem canonicalPrimeVielbein_traceLogSupervolume_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    canonicalPrimeVielbein.traceLogSupervolume s = riemannZeta s := by
  simpa using zetaTraceSupervolume_eq_riemannZeta (s := s) hs

/-- Canonical Euler-product readout equals `riemannZeta` on the standard half-plane. -/
theorem canonicalPrimeVielbein_eulerSupervolume_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    canonicalPrimeVielbein.eulerSupervolume s = riemannZeta s := by
  simpa using zetaTraceEulerSupervolume_eq_riemannZeta (s := s) hs

/-- The two canonical supervolume readouts agree on the standard half-plane. -/
theorem canonicalPrimeVielbein_traceLog_eq_eulerSupervolume
    {s : ℂ} (hs : 1 < s.re) :
    canonicalPrimeVielbein.traceLogSupervolume s =
      canonicalPrimeVielbein.eulerSupervolume s := by
  simpa using zetaTraceSupervolume_eq_eulerSupervolume (s := s) hs

end InfoGeometry.Arithmetic
