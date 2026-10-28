/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorOneParticleSector
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A faithful real Euclidean realization of the polynomial sector

The finite carrier is embedded into the actual polynomial module. The Fock
pairing and every number-conserving matrix operator are transported exactly;
the finite representation is thus a proved restriction of the operators.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealPolynomialCCR

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def euclideanEmbedding : EuclideanSpace ℝ ι →ₗ[ℝ] WavePolynomial ι :=
  linearFormMap.comp (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap

omit [DecidableEq ι] in
@[simp] theorem euclideanEmbedding_apply (x : EuclideanSpace ℝ ι) :
    euclideanEmbedding x = linearForm (WithLp.ofLp x) := rfl

theorem euclideanEmbedding_injective : Function.Injective (euclideanEmbedding (ι := ι)) := by
  intro x y h
  apply WithLp.ofLp_injective
  exact linearForm_injective h

theorem euclideanEmbedding_pairing (x y : EuclideanSpace ℝ ι) :
    fockPairing (euclideanEmbedding x) (euclideanEmbedding y) = inner ℝ x y := by
  rw [euclideanEmbedding_apply, euclideanEmbedding_apply, fockPairing_linearForm,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [contraction, dotProduct, mul_comm]

omit [DecidableEq ι] in
theorem euclideanEmbedding_mem_sector (x : EuclideanSpace ℝ ι) :
    euclideanEmbedding x ∈ oneParticleSector :=
  ⟨WithLp.ofLp x, rfl⟩

theorem euler_euclideanEmbedding (x : EuclideanSpace ℝ ι) :
    euler (euclideanEmbedding x) = euclideanEmbedding x :=
  euler_linearForm _

/-- Every finite matrix action is the restriction of its genuine differential operator. -/
theorem oneBody_euclideanEmbedding (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    oneBody A (euclideanEmbedding x) = euclideanEmbedding (A.toEuclideanLin x) :=
  oneBody_linearForm A (WithLp.ofLp x)

end InfoGeometry.Twistor.RealPolynomialCCR
