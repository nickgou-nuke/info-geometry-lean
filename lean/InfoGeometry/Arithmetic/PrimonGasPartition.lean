import Mathlib.Data.Nat.Factorization.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.PNat.Basic
import InfoGeometry.Arithmetic.BostConnesSystem

/-!
# Squarefree primon index packet

This file currently defines only squarefreeness for positive naturals and the
corresponding set.  It does not prove Euler-product formulas, zeta partition
functions, Cuntz-algebra representations, KMS states, phase transitions, or
boson/fermion cancellation theorems.
-/

namespace InfoGeometry.Arithmetic.PrimonGasPartition

open BostConnesSystem

/- ## The Counting Functions -/

/-- Test if n is squarefree (no prime factor appears more than once). -/
def IsSquarefree (n : ℕ+) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p^2 ∣ (n.val : ℕ) → False

/-- The set of squarefree positive integers. -/
def squarefreeSet : Set ℕ+ :=
  { n | IsSquarefree n }

/-
No bijection with an infinite Cantor boundary is constructed in this file.
-/

/- No partition functions or Euler products are defined or proved here.
-/

/- ## The Exact Cancellation — Bosonic × Möbius = 1 -/

/-
No arithmetic supersymmetry or zeta inverse theorem is proved here.
-/

/- ## Group-theoretic claims -/

/-
No idele-class, Cuntz-crossed-product, or KMS theorem is proved here.
-/

/- ## The Trifactor Geometry — Bosons × Fermions × Sign -/

/-
No trifactor, Hodge-decomposition, Pauli-exclusion, or Bost--Connes semigroup
identification is proved here.
-/

/-! ## Finite Euler-factor cancellation

The following theorem is the native finite mathlib core of the transferred
"bosonic × Möbius factor = 1" idea.  It is deliberately finite: no infinite
Euler product, zeta identity, Fock-space trace, or analytic continuation is
claimed here.
-/

open scoped BigOperators

section FiniteEulerProduct

variable {ι : Type*}

/-- Finite product of inverse local bosonic factors over an index set. -/
noncomputable def finiteBosonicEulerFactor (S : Finset ι) (w : ι → ℂ) : ℂ :=
  ∏ p ∈ S, (1 - w p)⁻¹

/-- Finite product of local Möbius-style complementary factors over an index set. -/
noncomputable def finiteMobiusEulerFactor (S : Finset ι) (w : ι → ℂ) : ℂ :=
  ∏ p ∈ S, (1 - w p)

/--
Finite cancellation of reciprocal Euler factors.

If every local factor `1 - w p` is nonzero on the finite set `S`, then the
finite bosonic inverse product times the finite Möbius-style product is `1`.
This is the theorem-safe finite algebraic core of the transferred partition
factor idea.
-/
theorem finiteBosonicEulerFactor_mul_finiteMobiusEulerFactor
    (S : Finset ι) (w : ι → ℂ)
    (hw : ∀ p ∈ S, 1 - w p ≠ 0) :
    finiteBosonicEulerFactor S w * finiteMobiusEulerFactor S w = 1 := by
  classical
  unfold finiteBosonicEulerFactor finiteMobiusEulerFactor
  rw [← Finset.prod_mul_distrib]
  trans ∏ p ∈ S, (1 : ℂ)
  · apply Finset.prod_congr rfl
    intro p hp
    exact inv_mul_cancel₀ (hw p hp)
  · simp

/-- Finite product of local squarefree/fermionic plus factors over an index set. -/
noncomputable def finiteFermionicEulerFactor (S : Finset ι) (w : ι → ℂ) : ℂ :=
  ∏ p ∈ S, (1 + w p)

/-- Finite product of inverse local Liouville-style plus factors over an index set. -/
noncomputable def finiteLiouvilleComplementFactor (S : Finset ι) (w : ι → ℂ) : ℂ :=
  ∏ p ∈ S, (1 + w p)⁻¹

/--
Finite cancellation of squarefree/fermionic plus factors with their reciprocal
Liouville-style complements.

This is a second finite theorem-safe product identity from the transferred
trifactor partition-language: it is only a finite product calculation.
-/
theorem finiteFermionicEulerFactor_mul_finiteLiouvilleComplementFactor
    (S : Finset ι) (w : ι → ℂ)
    (hw : ∀ p ∈ S, 1 + w p ≠ 0) :
    finiteFermionicEulerFactor S w * finiteLiouvilleComplementFactor S w = 1 := by
  classical
  unfold finiteFermionicEulerFactor finiteLiouvilleComplementFactor
  rw [← Finset.prod_mul_distrib]
  trans ∏ p ∈ S, (1 : ℂ)
  · apply Finset.prod_congr rfl
    intro p hp
    exact mul_inv_cancel₀ (hw p hp)
  · simp

/-- Empty finite bosonic/Möbius product readout. -/
theorem finiteBosonicMobiusEulerFactor_empty (w : ι → ℂ) :
    finiteBosonicEulerFactor (∅ : Finset ι) w = 1 ∧
      finiteMobiusEulerFactor (∅ : Finset ι) w = 1 := by
  simp [finiteBosonicEulerFactor, finiteMobiusEulerFactor]

/-- Empty finite fermionic/Liouville-complement product readout. -/
theorem finiteFermionicLiouvilleEulerFactor_empty (w : ι → ℂ) :
    finiteFermionicEulerFactor (∅ : Finset ι) w = 1 ∧
      finiteLiouvilleComplementFactor (∅ : Finset ι) w = 1 := by
  simp [finiteFermionicEulerFactor, finiteLiouvilleComplementFactor]

end FiniteEulerProduct

end InfoGeometry.Arithmetic.PrimonGasPartition
