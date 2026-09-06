import Mathlib.Tactic
import InfoGeometry.Categorical.PrimeThermodynamicLimitCapstone
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
import InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock
import InfoGeometry.Arithmetic.ChiralPrimonGas

noncomputable section

namespace InfoGeometry.Categorical.PrimeThermodynamicReadoutCones

open InfoGeometry.Arithmetic.ChiralPrimonGas
open InfoGeometry.Arithmetic.PrimeOccupationAlgebra
open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
open InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock
open InfoGeometry.Categorical.PrimeThermodynamicDirectLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

def toNatPrimes {n : ℕ} (p : primesUpto n) : Nat.Primes :=
  ⟨p.1, (mem_primesUpto_iff.mp p.2).2⟩

@[rep_depth thermo]
def stageActivityEval (z s : ℂ) (n : ℕ) : PrimeStage n →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval (fun p => grandComplexPrimeWeight z s (toNatPrimes p))

@[simp]
theorem stageActivityEval_comp_bond (z s : ℂ) (n : ℕ) (x : PrimeStage n) :
    stageActivityEval z s (n + 1) (primeBondAlg n x) = stageActivityEval z s n x := by
  unfold stageActivityEval primeBondAlg
  rw [MvPolynomial.aeval_rename]
  rfl

def universalActivityEval (z s : ℂ) : PrimonAlgebra →+* ℂ :=
  directLimitLift primeBond (fun n => (stageActivityEval z s n).toRingHom) (by
    intro n x
    exact stageActivityEval_comp_bond z s n x)

@[simp]
theorem universalActivityEval_stage (z s : ℂ) (n : ℕ) (x : PrimeStage n) :
    universalActivityEval z s (stageLimitOf n x) = stageActivityEval z s n x := by
  exact directLimitLift_of primeBond (fun n => (stageActivityEval z s n).toRingHom) _ n x

def stageGeneratorProduct (n : ℕ) (S : Finset (primesUpto n)) : PrimeStage n :=
  ∏ p ∈ S, MvPolynomial.X p

theorem stageActivityEval_generatorProduct
    (z s : ℂ) (n : ℕ) (S : Finset (primesUpto n)) :
    stageActivityEval z s n (stageGeneratorProduct n S) =
      ∏ p ∈ S, grandComplexPrimeWeight z s (toNatPrimes p) := by
  unfold stageGeneratorProduct
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p _hp
  simp [stageActivityEval]

theorem universalActivityEval_generatorProduct
    (z s : ℂ) (n : ℕ) (S : Finset (primesUpto n)) :
    universalActivityEval z s (stageLimitOf n (stageGeneratorProduct n S)) =
      ∏ p ∈ S, grandComplexPrimeWeight z s (toNatPrimes p) := by
  rw [universalActivityEval_stage, stageActivityEval_generatorProduct]

theorem universalActivityEval_unique
    (z s : ℂ) (g : PrimonAlgebra →+* ℂ)
    (hg : ∀ n (x : PrimeStage n),
      g (stageLimitOf n x) = stageActivityEval z s n x) :
    g = universalActivityEval z s := by
  apply directLimitLift_unique primeBond
    (fun n => (stageActivityEval z s n).toRingHom)
    (by
      intro n x
      exact stageActivityEval_comp_bond z s n x)
    g
  intro n
  apply RingHom.ext
  intro x
  exact hg n x

end InfoGeometry.Categorical.PrimeThermodynamicReadoutCones
