/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovGroupInverseStationaryReadout
import InfoGeometry.QuantumContext.MarkovMatrixStageK0

/-!
# Stationary Markov readout in the matrix-stage colimit

For a strictly positive finite row-stochastic real matrix with a normalized
invariant row weight, the stationary-mean matrix is the complementary
group-inverse idempotent. This file transports that concrete readout through
the explicit real-to-complex matrix stage and its quotient direct-colimit map,
then identifies the corresponding finitely generated projective-module
`K₀` class. Positivity and probability semantics are asserted only at the
finite real stage.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovStationaryColimitK0

open InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovGroupInverseStageColimit
open InfoGeometry.QuantumContext.MarkovMatrixStageK0

universe u

local instance : AddCommGroup (K0 MatrixStageLimit) := by
  change AddCommGroup (Grothendieck (ProjectiveModuleClass MatrixStageLimit))
  infer_instance

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- The stationary-mean representative at the quotient matrix-stage limit. -/
def stationaryMeanStage (n : ℕ) (e : ι ≃ BitWord n) (π : ι → ℝ) :
    MatrixStageLimit :=
  canonicalStageHom n (realMatrixToComplexStage n e (stationaryMeanMatrix π))

/-- The group-inverse complementary idempotent at the quotient matrix-stage
limit. -/
def stationaryProjectorStage (n : ℕ) (e : ι ≃ BitWord n)
    (P G : Matrix ι ι ℝ) : MatrixStageLimit :=
  principalIdempotent
    (canonicalStageHom n (realMatrixToComplexStage n e (1 - P)))
    (canonicalStageHom n (realMatrixToComplexStage n e G))

/-- The finite stationary-mean matrix, after the repository's explicit
real-to-complex stage map and quotient-colimit inclusion, is the complementary
idempotent of the transported group inverse. -/
theorem stationaryMeanMatrix_canonicalStageHom_eq_principalIdempotent
    (n : ℕ) (e : ι ≃ BitWord n)
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G) :
    stationaryMeanStage n e π = stationaryProjectorStage n e P G := by
  have hread := markovStationaryProjector_eq_stationaryMeanMatrix
    P π hP hPpos hπsum hstat G hG
  have hmap := congrArg (fun M : Matrix ι ι ℝ =>
    canonicalStageHom n (realMatrixToComplexStage n e M)) hread
  change canonicalStageHom n
      (realMatrixToComplexStage n e (stationaryMeanMatrix π)) =
    principalIdempotent
      (canonicalStageHom n (realMatrixToComplexStage n e (1 - P)))
      (canonicalStageHom n (realMatrixToComplexStage n e G))
  rw [← principalIdempotent_canonicalStageHom]
  simpa [markovStationaryProjector, markovRangeIdempotent,
    principalIdempotent, regularIdempotent] using hmap.symm

/-- Equality of idempotent carriers identifies their projective-module
`K₀` classes; the idempotence proofs are propositionally irrelevant. -/
theorem k0Class_rightIdempotentProjectiveModule_congr
    {R : Type u} [Ring R] (a b : R) (ha : a * a = a) (hb : b * b = b)
    (h : a = b) :
    k0Class R (rightIdempotentProjectiveModule a ha) =
      k0Class R (rightIdempotentProjectiveModule b hb) := by
  cases h
  have hp : ha = hb := Subsingleton.elim _ _
  rw [hp]

/-- At the quotient direct-colimit carrier, the stationary-mean matrix and
the group-inverse stationary idempotent cut out the same projective left
module and therefore the same algebraic `K₀` class. -/
theorem stationaryMeanMatrix_projectiveK0_eq
    (n : ℕ) (e : ι ≃ BitWord n)
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G) :
    k0Class MatrixStageLimit
        (rightIdempotentProjectiveModule (stationaryMeanStage n e π)
          (by
            rw [stationaryMeanMatrix_canonicalStageHom_eq_principalIdempotent
              n e P π hP hPpos hπsum hstat G hG]
            exact principalIdempotent_idempotent
              (groupInverse_canonicalStageHom n
                (realMatrixToComplexStage n e (1 - P))
                (realMatrixToComplexStage n e G)
                (groupInverse_realMatrixToComplexStage n e (1 - P) G hG)))) =
      k0Class MatrixStageLimit
        (rightIdempotentProjectiveModule (stationaryProjectorStage n e P G)
          (principalIdempotent_idempotent
            (groupInverse_canonicalStageHom n
              (realMatrixToComplexStage n e (1 - P))
              (realMatrixToComplexStage n e G)
              (groupInverse_realMatrixToComplexStage n e (1 - P) G hG)))) := by
  let hGStage := groupInverse_realMatrixToComplexStage n e (1 - P) G hG
  let hGlim := groupInverse_canonicalStageHom n
    (realMatrixToComplexStage n e (1 - P))
    (realMatrixToComplexStage n e G) hGStage
  have hS : stationaryMeanStage n e π * stationaryMeanStage n e π =
      stationaryMeanStage n e π := by
    rw [stationaryMeanMatrix_canonicalStageHom_eq_principalIdempotent
      n e P π hP hPpos hπsum hstat G hG]
    exact principalIdempotent_idempotent hGlim
  have hQ : stationaryProjectorStage n e P G * stationaryProjectorStage n e P G =
      stationaryProjectorStage n e P G := principalIdempotent_idempotent hGlim
  apply k0Class_rightIdempotentProjectiveModule_congr
    (stationaryMeanStage n e π) (stationaryProjectorStage n e P G) hS hQ
  exact stationaryMeanMatrix_canonicalStageHom_eq_principalIdempotent
    n e P π hP hPpos hπsum hstat G hG

end InfoGeometry.QuantumContext.MarkovStationaryColimitK0

end
