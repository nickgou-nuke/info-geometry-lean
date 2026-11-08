import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Primon Zeta and Möbius Fermion Parity

Concrete arithmetic-function layer for the boson/fermion Primon dictionary.

* `ζ` is the bosonic divisor-sum kernel.
* `μ` is the fermionic parity kernel.
* nonsquarefree states are killed by `μ`;
* squarefree states carry parity `(-1) ^ cardFactors n`;
* `ζ * μ = 1`, so the bosonic and fermionic kernels cancel to the vacuum
  for Dirichlet convolution.
-/

noncomputable section

open ArithmeticFunction
open scoped zeta
open scoped ArithmeticFunction.Moebius

def ZBosonKernel : ArithmeticFunction ℤ :=
  ζ

def FermionParityKernel : ArithmeticFunction ℤ :=
  μ

def PrimonVacuumKernel : ArithmeticFunction ℤ :=
  1

def fermionParity (n : ℕ) : ℤ :=
  μ n

theorem fermion_parity_of_not_squarefree {n : ℕ} (h : ¬Squarefree n) :
    fermionParity n = 0 := by
  simpa [fermionParity] using moebius_eq_zero_of_not_squarefree h

theorem fermion_parity_of_squarefree {n : ℕ} (h : Squarefree n) :
    fermionParity n = (-1) ^ cardFactors n := by
  simpa [fermionParity] using moebius_apply_of_squarefree h

theorem fermion_parity_prime {p : ℕ} (hp : p.Prime) :
    fermionParity p = -1 := by
  simpa [fermionParity] using moebius_apply_prime hp

theorem zeta_mobius_vacuum_cancellation :
    ZBosonKernel * FermionParityKernel = PrimonVacuumKernel := by
  simp [ZBosonKernel, FermionParityKernel, PrimonVacuumKernel]

theorem mobius_zeta_vacuum_cancellation :
    FermionParityKernel * ZBosonKernel = PrimonVacuumKernel := by
  simp [ZBosonKernel, FermionParityKernel, PrimonVacuumKernel]

theorem zeta_mobius_cancels_observable (f : ArithmeticFunction ℤ) :
    (f * ZBosonKernel) * FermionParityKernel = f := by
  unfold ZBosonKernel FermionParityKernel
  rw [mul_assoc, coe_zeta_mul_moebius, mul_one]

/-- Consolidated Primon zeta/Möbius package with genuine arithmetic facts. -/
theorem primon_zeta_mobius_synthesis :
    ZBosonKernel * FermionParityKernel = PrimonVacuumKernel ∧
    FermionParityKernel * ZBosonKernel = PrimonVacuumKernel ∧
    (∀ f : ArithmeticFunction ℤ, (f * ZBosonKernel) * FermionParityKernel = f) ∧
    (∀ p : ℕ, p.Prime → fermionParity p = -1) := by
  exact ⟨zeta_mobius_vacuum_cancellation, mobius_zeta_vacuum_cancellation,
    zeta_mobius_cancels_observable, fun p hp => fermion_parity_prime hp⟩

end noncomputable section
