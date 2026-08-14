import InfoGeometry.Canonical.LogScaleModularSurprisalBridge
import InfoGeometry.Algebra.CuntzModularTreeFlowBridge

/-!
# Concrete Cuntz modular surprisal datum

The existing Cuntz gauge flow supplies a concrete inhabitant of the algebraic
`ModularSurprisalDatum` interface.  The generator field is deliberately the
zero operator: no exponential or unbounded-generator identification is
claimed here.  The verified content is the one-parameter group law and its
logarithmic arithmetic sampling.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzModularSurprisalDatum

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzModularAutomorphism
open InfoGeometry.Canonical.LogScaleModularSurprisalBridge

variable {n : ℕ} (primes : Fin n → ℕ)

def datum : ModularSurprisalDatum (CuntzAlg n) where
  K := 0
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

@[simp] theorem datum_U (t : ℝ) :
    (datum primes).U t = (sigma n primes t).toLinearMap := rfl

theorem dirichletModularSample_eq_sigma (p : ℕ) :
    dirichletModularSample (datum primes) p =
      (sigma n primes (Real.log p)).toLinearMap := rfl

theorem prime_modular_sample_eq_sigma (p : ℕ) (_hp : Nat.Prime p) :
    dirichletModularSample (datum primes) p =
      (sigma n primes (Real.log p)).toLinearMap :=
  dirichletModularSample_eq_sigma primes p

theorem nat_power_sample_eq_iterate (p k : ℕ) :
    dirichletModularSample (datum primes) (p ^ k) =
      ((sigma n primes (Real.log p)).toLinearMap) ^ k := by
  simpa [datum_U] using
    (dirichletModularSample_prime_power (datum primes) p k)

theorem prime_power_sample_eq_iterate (p k : ℕ) (_hp : Nat.Prime p) :
    dirichletModularSample (datum primes) (p ^ k) =
      ((sigma n primes (Real.log p)).toLinearMap) ^ k :=
  nat_power_sample_eq_iterate primes p k

end InfoGeometry.Canonical.CuntzModularSurprisalDatum

end
