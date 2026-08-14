import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Arithmetic.PrimonGasPartition
import InfoGeometry.Analysis.BregmanAnalyticBound
import DAG.HarmonicKMS

/-!
# U_res finite readouts

This module records finite arithmetic and operator-style readouts using
restricted-unitary notation.  It does not construct an infinite-dimensional
restricted-unitary representation, Fredholm determinant, Pfaffian, Euler
product, or analytic partition function.  Such interpretations enter only
through explicit fields or hypotheses.
-/

open Complex

namespace InfoGeometry.Arithmetic.UResRepresentations

open BostConnesSystem
open PrimonGasPartition

/- ## The 1-Particle Hilbert Space and the Diagonal Hamiltonian -/

/-
The 1-particle Hilbert space ℓ²(ℕ^+) with orthonormal basis |p⟩ indexed
by primes. The Hamiltonian H|p⟩ = log(p)·|p⟩ is diagonal and unbounded.

For e^{-βH}: the operator is trace-class for β > 1, with eigenvalues p^{-β}.
-/

/-- The 1-particle energy of prime mode p: ε_p = log(p). -/
noncomputable def primeEnergy (p : ℕ+) : ℝ := Real.log (p.val : ℝ)

lemma primeEnergy_nonneg (p : ℕ+) :
    0 ≤ primeEnergy p := by
  unfold primeEnergy
  exact Real.log_nonneg (by exact_mod_cast p.pos)

/-
The Boltzmann weight at inverse temperature β for prime p:
    e^{-β H}|p⟩ = p^{-β}|p⟩
-/
noncomputable def boltzmannWeight (β : ℝ) (p : ℕ+) : ℝ :=
  (p.val : ℝ) ^ (-β)

lemma boltzmannWeight_pos (β : ℝ) (p : ℕ+) :
    0 < boltzmannWeight β p := by
  unfold boltzmannWeight
  exact Real.rpow_pos_of_pos (by exact_mod_cast p.pos) _

lemma boltzmannWeight_ne_zero (β : ℝ) (p : ℕ+) :
    boltzmannWeight β p ≠ 0 :=
  (boltzmannWeight_pos β p).ne'

/-- Finite local weight readout for a positive prime mode. -/
def liouvilleWeightVector (p : ℕ+) (_hp : Nat.Prime (p.val)) : ℂ :=
  -1

/- ## Optional KMS comparison socket

The analytic KMS and phase-transition statements associated with this
notation are not constructed by the finite declarations in this module.
They must be supplied by an explicit operator-algebra owner or hypothesis.
-/

/- ## Deferred analytic comparison targets

The finite declarations above do not prove Fredholm determinant identities,
Dikin bounds for zeta, analytic continuation, monodromy, or a universal-cover
construction.  Those statements remain explicit downstream targets and must
be supplied by their respective owners.
-/

end InfoGeometry.Arithmetic.UResRepresentations
