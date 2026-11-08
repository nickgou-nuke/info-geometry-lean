/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovGroupInverseStationaryProjection
import InfoGeometry.QuantumContext.MarkovAttentionKemenySnell

/-!
# Matrix readout of the Markov group-inverse stationary projector

Under strict positivity and a normalized invariant row weight, the
complementary group-inverse projector on the full matrix carrier is the
constant-row stationary-mean matrix. This reads the algebraic projector
through the existing stationary-mean matrix theorem. It does not assert that
arbitrary invariant rows are probability distributions or assert an iterate
limit.
-/

noncomputable section

namespace InfoGeometry.QuantumContext

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Under the hypotheses of the stationary-mean owner theorem, the
matrix-level complementary group-inverse projector is exactly the
constant-row stationary-mean matrix. -/
theorem markovStationaryProjector_eq_stationaryMeanMatrix
    [Nonempty ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    markovStationaryProjector P G = stationaryMeanMatrix π := by
  apply Matrix.toLin'.injective
  have hprincipal := principalIdempotent_toLin_eq_stationaryMeanMatrix
    P π hP hPpos hπsum hstat G hG
  change Matrix.toLin' (1 - ((1 - P) * G)) =
    Matrix.toLin' (stationaryMeanMatrix π)
  have hreadout : Matrix.toLin' (1 - ((1 - P) * G)) =
      principalIdempotent (Matrix.toLin' (1 - P)) (Matrix.toLin' G) := by
    simp [principalIdempotent, regularIdempotent, Matrix.toLin'_mul,
      Module.End.mul_eq_comp, Matrix.toLin'_one, Module.End.one_eq_id]
  rw [hreadout, hprincipal]

end InfoGeometry.QuantumContext

end
