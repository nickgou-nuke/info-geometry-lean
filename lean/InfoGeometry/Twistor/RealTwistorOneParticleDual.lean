/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorOneParticleRealization
import InfoGeometry.Twistor.RealDualTwistorPositiveSector

/-!
# The genuine dual of the polynomial one-excitation sector

The finite Euclidean carrier embeds into the actual polynomial module and
admits the degree-one coefficient retraction. Contravariant dualization then
embeds both primal and dual legs, preserving their neutral and symplectic
pairings. The ambient covectors are actual algebraic functionals; no
surjectivity of the infinite-dimensional Fock-to-dual map is asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealPolynomialCCR

open InfoGeometry.Twistor.RealDualTwistor
open InfoGeometry.Twistor.RealDualTwistorPositiveSector
open InfoGeometry.Twistor.RealDualTwistorKreinBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extract degree-one coefficients into the native real Euclidean carrier. -/
def euclideanRetraction : WavePolynomial ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap.comp oneParticleCoeff

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem euclideanRetraction_ofLp (p : WavePolynomial ι) :
    WithLp.ofLp (euclideanRetraction p) = oneParticleCoeff p := rfl

@[simp] theorem euclideanRetraction_euclideanEmbedding (x : EuclideanSpace ℝ ι) :
    euclideanRetraction (euclideanEmbedding x) = x := by
  apply WithLp.ofLp_injective
  exact oneParticleCoeff_linearForm (WithLp.ofLp x)

omit [DecidableEq ι] in
@[simp] theorem euclideanEmbedding_euclideanRetraction (p : WavePolynomial ι) :
    euclideanEmbedding (euclideanRetraction p) = oneParticleProjector p := rfl

theorem euclideanRetraction_comp_embedding :
    (euclideanRetraction (ι := ι)).comp euclideanEmbedding = LinearMap.id := by
  apply LinearMap.ext
  exact euclideanRetraction_euclideanEmbedding

omit [DecidableEq ι] in
theorem euclideanEmbedding_comp_retraction :
    (euclideanEmbedding (ι := ι)).comp euclideanRetraction = oneParticleProjector := rfl

/-- Extend a finite covector by the coefficient retraction, not by an assumed duality. -/
def sectorDualEmbedding :
    Carrier (EuclideanSpace ℝ ι) →ₗ[ℝ] Carrier (WavePolynomial ι) :=
  euclideanEmbedding.prodMap euclideanRetraction.dualMap

/-- Restrict an ambient covector to the actual polynomial sector. -/
def sectorDualRetraction :
    Carrier (WavePolynomial ι) →ₗ[ℝ] Carrier (EuclideanSpace ℝ ι) :=
  euclideanRetraction.prodMap euclideanEmbedding.dualMap

omit [DecidableEq ι] in
@[simp] theorem sectorDualEmbedding_apply (p : Carrier (EuclideanSpace ℝ ι)) :
    sectorDualEmbedding p = (euclideanEmbedding p.1, p.2.comp euclideanRetraction) := rfl

omit [DecidableEq ι] in
@[simp] theorem sectorDualRetraction_apply (p : Carrier (WavePolynomial ι)) :
    sectorDualRetraction p = (euclideanRetraction p.1, p.2.comp euclideanEmbedding) := rfl

@[simp] theorem sectorDualRetraction_embedding (p : Carrier (EuclideanSpace ℝ ι)) :
    sectorDualRetraction (sectorDualEmbedding p) = p := by
  apply Prod.ext
  · exact euclideanRetraction_euclideanEmbedding p.1
  · ext x
    change p.2 (euclideanRetraction (euclideanEmbedding x)) = p.2 x
    rw [euclideanRetraction_euclideanEmbedding]

omit [DecidableEq ι] in
theorem sectorDualEmbedding_retraction (p : Carrier (WavePolynomial ι)) :
    sectorDualEmbedding (sectorDualRetraction p) = dualLift oneParticleProjector p := by
  apply Prod.ext
  · exact euclideanEmbedding_euclideanRetraction p.1
  · apply LinearMap.ext
    intro q
    change p.2 (euclideanEmbedding (euclideanRetraction q)) = p.2 (oneParticleProjector q)
    rw [euclideanEmbedding_euclideanRetraction]

theorem sectorDualEmbedding_injective :
    Function.Injective (sectorDualEmbedding (ι := ι)) := by
  intro p q h
  have hr := congrArg (sectorDualRetraction (ι := ι)) h
  simpa only [sectorDualRetraction_embedding] using hr

/-- The finite dual is represented without changing its neutral pairing. -/
theorem sectorDualEmbedding_neutral (p q : Carrier (EuclideanSpace ℝ ι)) :
    neutralForm (sectorDualEmbedding p) (sectorDualEmbedding q) = neutralForm p q := by
  change p.2 (euclideanRetraction (euclideanEmbedding q.1)) +
      q.2 (euclideanRetraction (euclideanEmbedding p.1)) = p.2 q.1 + q.2 p.1
  rw [euclideanRetraction_euclideanEmbedding, euclideanRetraction_euclideanEmbedding]

/-- The same map preserves the independent alternating evaluation form. -/
theorem sectorDualEmbedding_symplectic (p q : Carrier (EuclideanSpace ℝ ι)) :
    symplecticForm (sectorDualEmbedding p) (sectorDualEmbedding q) =
      symplecticForm p q := by
  change q.2 (euclideanRetraction (euclideanEmbedding p.1)) -
      p.2 (euclideanRetraction (euclideanEmbedding q.1)) = q.2 p.1 - p.2 q.1
  rw [euclideanRetraction_euclideanEmbedding, euclideanRetraction_euclideanEmbedding]

theorem sectorDualEmbedding_fixed (p : Carrier (EuclideanSpace ℝ ι)) :
    dualLift oneParticleProjector (sectorDualEmbedding p) = sectorDualEmbedding p := by
  rw [← sectorDualEmbedding_retraction, sectorDualRetraction_embedding]

theorem mem_sectorDualEmbedding_range_iff (p : Carrier (WavePolynomial ι)) :
    p ∈ LinearMap.range sectorDualEmbedding ↔ dualLift oneParticleProjector p = p := by
  constructor
  · rintro ⟨q, rfl⟩
    exact sectorDualEmbedding_fixed q
  · intro hp
    exact ⟨sectorDualRetraction p, (sectorDualEmbedding_retraction p).trans hp⟩

theorem euclideanRetraction_oneBody (A : Matrix ι ι ℝ) (p : WavePolynomial ι) :
    euclideanRetraction (oneBody A p) = A.toEuclideanLin (euclideanRetraction p) := by
  apply WithLp.ofLp_injective
  exact oneParticleCoeff_oneBody A p

/-- Both dual legs intertwine, including the contravariant covector action. -/
theorem sectorDualEmbedding_oneBody (A : Matrix ι ι ℝ)
    (p : Carrier (EuclideanSpace ℝ ι)) :
    dualLift (oneBody A) (sectorDualEmbedding p) =
      sectorDualEmbedding (dualLift A.toEuclideanLin p) := by
  apply Prod.ext
  · exact oneBody_euclideanEmbedding A p.1
  · apply LinearMap.ext
    intro q
    change p.2 (euclideanRetraction (oneBody A q)) =
      p.2 (A.toEuclideanLin (euclideanRetraction q))
    rw [euclideanRetraction_oneBody]

theorem sectorDualRetraction_oneBody (A : Matrix ι ι ℝ)
    (p : Carrier (WavePolynomial ι)) :
    sectorDualRetraction (dualLift (oneBody A) p) =
      dualLift A.toEuclideanLin (sectorDualRetraction p) := by
  apply Prod.ext
  · exact euclideanRetraction_oneBody A p.1
  · ext x
    change p.2 (oneBody A (euclideanEmbedding x)) =
      p.2 (euclideanEmbedding (A.toEuclideanLin x))
    rw [oneBody_euclideanEmbedding]

/-- Mixed pairings identify the extended finite covector explicitly. -/
theorem euclideanEmbedding_pairing_retraction (x : EuclideanSpace ℝ ι)
    (p : WavePolynomial ι) :
    fockPairing (euclideanEmbedding x) p = inner ℝ x (euclideanRetraction p) := by
  calc
    fockPairing (euclideanEmbedding x) p =
        fockPairing (euclideanEmbedding x) (oneParticleProjector p) := by
      simpa only [euclideanEmbedding_apply, oneParticleProjector_linearForm] using
        oneParticleProjector_symmetric (euclideanEmbedding x) p
    _ = fockPairing (euclideanEmbedding x)
        (euclideanEmbedding (euclideanRetraction p)) := by
      rw [euclideanEmbedding_euclideanRetraction]
    _ = inner ℝ x (euclideanRetraction p) := euclideanEmbedding_pairing _ _

/-- The positive graph becomes the genuine ambient Fock covector graph. -/
theorem sectorDualEmbedding_positiveEmbedding (x : EuclideanSpace ℝ ι) :
    sectorDualEmbedding (positiveEmbedding x) =
      ((1 / 2 : ℝ) • euclideanEmbedding x, fockToDual (euclideanEmbedding x)) := by
  apply Prod.ext
  · exact map_smul euclideanEmbedding (1 / 2 : ℝ) x
  · apply LinearMap.ext
    intro p
    change realInnerDuality x (euclideanRetraction p) =
      fockPairing (euclideanEmbedding x) p
    rw [realInnerDuality_apply, euclideanEmbedding_pairing_retraction]

end InfoGeometry.Twistor.RealPolynomialCCR
