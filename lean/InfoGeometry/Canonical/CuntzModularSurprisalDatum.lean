import InfoGeometry.Canonical.LogScaleModularSurprisalBridge
import InfoGeometry.Algebra.CuntzModularTreeFlowBridge

/-!
# Cuntz modular surprisal flow datum

The existing Cuntz gauge flow supplies the one-parameter-group part of the
algebraic `ModularSurprisalDatum` interface.  Its infinitesimal generator is
kept as explicit supplied data: the repository does not identify the bounded
gauge flow with an exponential of an unbounded modular generator.  The
verified content is the one-parameter group law and its logarithmic arithmetic
sampling.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzModularSurprisalDatum

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzModularAutomorphism
open InfoGeometry.Canonical.LogScaleModularSurprisalBridge

variable {n : ℕ} (primes : Fin n → ℕ)

def datum (K : CuntzAlg n →ₗ[ℂ] CuntzAlg n) : ModularSurprisalDatum (CuntzAlg n) where
  K := K
  U := fun t => (sigma n primes t).toLinearMap
  flow_zero := by
    ext x
    simpa using congrArg (fun F : CuntzAlg n →ₐ[ℂ] CuntzAlg n => F x)
      (sigma_zero n primes)
  flow_add := by
    intro s t
    ext x
    simpa using congrArg (fun F : CuntzAlg n →ₐ[ℂ] CuntzAlg n => F x)
      (sigma_add n primes s t)

@[simp] theorem datum_U (K : CuntzAlg n →ₗ[ℂ] CuntzAlg n) (t : ℝ) :
    (datum primes K).U t = (sigma n primes t).toLinearMap := rfl

theorem dirichletModularSample_eq_sigma
    (K : CuntzAlg n →ₗ[ℂ] CuntzAlg n) (p : ℕ) :
    dirichletModularSample (datum primes K) p =
      (sigma n primes (Real.log p)).toLinearMap := rfl

theorem prime_modular_sample_eq_sigma
    (K : CuntzAlg n →ₗ[ℂ] CuntzAlg n) (p : ℕ) (_hp : Nat.Prime p) :
    dirichletModularSample (datum primes K) p =
      (sigma n primes (Real.log p)).toLinearMap :=
  dirichletModularSample_eq_sigma primes K p

theorem nat_power_sample_eq_iterate
    (K : CuntzAlg n →ₗ[ℂ] CuntzAlg n) (p k : ℕ) :
    dirichletModularSample (datum primes K) (p ^ k) =
      ((sigma n primes (Real.log p)).toLinearMap) ^ k := by
  simpa [datum_U] using
    (dirichletModularSample_prime_power (datum primes K) p k)

theorem prime_power_sample_eq_iterate
    (K : CuntzAlg n →ₗ[ℂ] CuntzAlg n) (p k : ℕ) (_hp : Nat.Prime p) :
    dirichletModularSample (datum primes K) (p ^ k) =
      ((sigma n primes (Real.log p)).toLinearMap) ^ k :=
  nat_power_sample_eq_iterate primes K p k


end InfoGeometry.Canonical.CuntzModularSurprisalDatum
