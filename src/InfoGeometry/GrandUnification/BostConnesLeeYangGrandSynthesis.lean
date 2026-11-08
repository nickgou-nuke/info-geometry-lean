/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Analysis.JaynesRelativeStates
import InfoGeometry.Canonical.HodgeDiracLaplacianBridge
import InfoGeometry.Canonical.PrimeCl11ModularAtom
import InfoGeometry.Arithmetic.FiniteMobiusFermionSupertraceBridge
import InfoGeometry.Arithmetic.RiemannZetaPrimonSouriauCayleyCapstone
import InfoGeometry.Quantum.CantorCrystalSupergradedSuperalgebraCapstone

/-!
# Algebraic Bost–Connes / Cantor-Crystal Readout Synthesis

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Unifies the finite $\mathrm{Cl}(1,1)$ Möbius parity atom (`PrimeCl11ModularAtom`),
    Hodge–Dirac Laplacian commutation (`HodgeDiracLaplacianBridge`), finite fermionic supertrace
    Euler product (`FiniteMobiusFermionSupertraceBridge`), and critical-line Cayley unitarity.
- BUCKET 2 (Finite & Property-Gated Scope):
  * Composes finite and property-gated algebraic theorems on explicitly supplied carriers;
    makes no analytic Riemann hypothesis or infinite $C^*$-algebra claim.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `prime_mobius_parity_sq_eq_one`, `dirac_laplacian_commutes_with_mobius_parity`,
    `fermion_supertrace_is_inverse_euler_product`, `mobius_parity_equals_fermion_sign`,
    and `cayley_unitarity_of_critical_line`.
-/

noncomputable section

namespace InfoGeometry.GrandUnification.BostConnesLeeYang

open Complex Matrix
open InfoGeometry.Canonical.YangBaxterProof
open InfoGeometry.Analysis.JaynesRelativeStates
open InfoGeometry.Canonical.HodgeDiracLaplacianBridge
open InfoGeometry.Canonical.PrimeCl11ModularAtom
open InfoGeometry.Arithmetic.FiniteMobiusFermionSupertraceBridge
open InfoGeometry.Arithmetic.PrimonSouriauCayley
open InfoGeometry.Quantum.CantorCrystal

variable {A : Type*} [Ring A]
variable {O2 : Type*} [Ring O2] [StarRing O2]

/-! ## 1. Prime Cl(1,1) Möbius Parity & Dirac-Laplacian Commutation -/

/-- The local Möbius parity `γ = c · d` is an involution (`γ² = 1`). -/
theorem prime_mobius_parity_sq_eq_one (atom : Cl11Atom A) :
    (atom.mobiusParity) * (atom.mobiusParity) = 1 := by
  rw [atom.mobiusParity_sq_eq_one]

/-- The Dirac Laplacian `Δ = Q²` commutes with Möbius parity:
`{Q, γ} = 0 ⟹ [Q², γ] = 0`. -/
theorem dirac_laplacian_commutes_with_mobius_parity
    (atom : Cl11Atom A)
    (Q : A)
    (h_chiral : Q * (atom.mobiusParity) = -(atom.mobiusParity * Q)) :
    (Q * Q) * (atom.mobiusParity) = (atom.mobiusParity) * (Q * Q) := by
  apply dirac_sq_commutes_hodge (atom.mobiusParity) Q h_chiral

/-! ## 2. Super-KMS Trace & Möbius Inversion -/

/-- The fermionic supertrace `STr(q)` evaluates to the inverse Euler product `∏ (1 - q_p)`. -/
theorem fermion_supertrace_is_inverse_euler_product
    {ι M : Type*} [DecidableEq ι] [CommRing M]
    (modes : Finset ι) (q : ι → M) :
    finiteFermionSupertrace modes q = ∏ p ∈ modes, (1 - q p) := by
  rw [finiteFermionSupertrace_eq_eulerProduct]

/-- The fermion parity of a squarefree prime product is the Möbius function `μ(n)`. -/
theorem mobius_parity_equals_fermion_sign
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    ArithmeticFunction.moebius (∏ p ∈ S, p) = finiteArithmeticParity S := by
  apply mobius_subsetProduct_eq_finiteArithmeticParity S hprime

/-! ## 3. Critical-Line Cayley Transport -/

/-- Cayley transform centered at the critical line `Re(s) = 1/2`. -/
def cayley_critical (s : ℂ) : ℂ :=
  ((s - (1 / 2 : ℂ)) - 1) / ((s - (1 / 2 : ℂ)) + 1)

/-- The Critical Line `Re(s) = 1/2` maps to the unit circle under `cayley_critical`:
`|C_crit(s)|² = 1` for all `s` with `s.re = 1/2`. -/
theorem cayley_unitarity_of_critical_line (s : ℂ) (h_crit : s.re = 1 / 2) :
    Complex.normSq (cayley_critical s) = 1 := by
  unfold cayley_critical
  rw [Complex.normSq_div]
  have hre_half : ((1 / 2 : ℂ).re) = 1 / 2 := by norm_num
  have him_half : ((1 / 2 : ℂ).im) = 0 := by norm_num
  have hre_num : (((s - 1 / 2) - 1).re) = -1 := by
    calc
      (((s - 1 / 2) - 1).re) = (s.re - (1/2 : ℂ).re) - (1 : ℂ).re := by
        rw [sub_re, sub_re]
      _ = (1/2 - 1/2) - 1 := by rw [h_crit, hre_half, one_re]
      _ = -1 := by ring
  have him_num : (((s - 1 / 2) - 1).im) = s.im := by
    calc
      (((s - 1 / 2) - 1).im) = (s.im - (1/2 : ℂ).im) - (1 : ℂ).im := by
        rw [sub_im, sub_im]
      _ = (s.im - 0) - 0 := by rw [him_half, one_im]
      _ = s.im := by ring
  have hre_den : (((s - 1 / 2) + 1).re) = 1 := by
    calc
      (((s - 1 / 2) + 1).re) = (s.re - (1/2 : ℂ).re) + (1 : ℂ).re := by
        rw [add_re, sub_re]
      _ = (1/2 - 1/2) + 1 := by rw [h_crit, hre_half, one_re]
      _ = 1 := by ring
  have him_den : (((s - 1 / 2) + 1).im) = s.im := by
    calc
      (((s - 1 / 2) + 1).im) = (s.im - (1/2 : ℂ).im) + (1 : ℂ).im := by
        rw [add_im, sub_im]
      _ = (s.im - 0) + 0 := by rw [him_half, one_im]
      _ = s.im := by ring
  have hnorm_num : Complex.normSq ((s - 1 / 2) - 1) = 1 + s.im ^ 2 := by
    rw [Complex.normSq_apply, hre_num, him_num]
    ring
  have hnorm_den : Complex.normSq ((s - 1 / 2) + 1) = 1 + s.im ^ 2 := by
    rw [Complex.normSq_apply, hre_den, him_den]
    ring
  rw [hnorm_num, hnorm_den]
  have hpos : 1 + s.im ^ 2 ≠ 0 := by
    have hsq : 0 ≤ s.im ^ 2 := sq_nonneg s.im
    linarith
  exact div_self hpos

end InfoGeometry.GrandUnification.BostConnesLeeYang
