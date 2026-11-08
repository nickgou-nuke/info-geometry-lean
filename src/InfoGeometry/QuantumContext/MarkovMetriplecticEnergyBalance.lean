/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMetriplecticFlowBridge
import InfoGeometry.QuantumContext.MarkovGroupInversePetzSupport

/-!
# Full-matrix energy-force pairing for Markov metriplectic flows

The Markov packet proves energy degeneracy of its dissipative Onsager map.
This bridge assumes a reversible generator skew for a strictly positive
stationary-weighted matrix pairing. It proves that the pairing of the energy
force with the resulting instantaneous total velocity is zero on the full
matrix carrier. A separate theorem records the group-inverse recovery of the
projected dissipative force; neither theorem asserts a trajectory limit.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.QuantumContext

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The weighted Frobenius pairing is additive in its second matrix input. -/
theorem weightedMatrixPairing_add_right (π : ι → ℝ)
    (X Y Z : Matrix ι ι ℝ) :
    weightedMatrixPairing π X (Y + Z) =
      weightedMatrixPairing π X Y + weightedMatrixPairing π X Z := by
  simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn,
    Matrix.add_apply, mul_add, Finset.sum_add_distrib]

omit [DecidableEq ι] in
/-- A reversible generator skew for a symmetric weighted Frobenius pairing has
zero self-pairing at the chosen energy force. -/
theorem weightedMatrixPairing_energy_reversible_eq_zero
    (π : ι → ℝ) (J : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ)
    (hJ : ∀ X Y, weightedMatrixPairing π X (J Y) =
      - weightedMatrixPairing π (J X) Y) :
    weightedMatrixPairing π (constantOneMatrix (ι := ι))
      (J (constantOneMatrix (ι := ι))) = 0 := by
  have hskew := hJ (constantOneMatrix (ι := ι))
    (constantOneMatrix (ι := ι))
  rw [weightedMatrixPairing_comm π
    (J (constantOneMatrix (ι := ι))) (constantOneMatrix (ι := ι))] at hskew
  exact (add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hskew))

/-- Applying the matrix group inverse to the Markov dissipative velocity
recovers the entropy force after projection by the canonical range idempotent.
This is the group-inverse bridge for the full-matrix Onsager flow; the
projection can be oblique. -/
theorem markovGroupInverse_recovers_projected_entropyForce
    [Nontrivial ι]
    (P G entropyForce : Matrix ι ι ℝ)
    (hG : InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
      (1 - P) G) :
    G * markovLeftOnsager P entropyForce =
      markovRangeIdempotent P G * entropyForce := by
  change G * ((1 - P) * entropyForce) = ((1 - P) * G) * entropyForce
  calc
    G * ((1 - P) * entropyForce) = (G * (1 - P)) * entropyForce := by
      rw [mul_assoc]
    _ = ((1 - P) * G) * entropyForce := by rw [← hG.2.2]

/-- Instantaneous total force-velocity pairing for a finite Markov
metriplectic packet on the full matrix carrier. Strict positivity of `π`
excludes the zero-weight pairing; skewness of the specified reversible map
and Markov Onsager energy degeneracy imply the stated pairing identity. This
is not a trajectory conservation theorem and does not use the group inverse. -/
theorem markovMetriplectic_energyForce_totalVelocity_pairing_eq_zero
    [Nontrivial ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπpos : ∀ i, 0 < π i)
    (entropyForce : Matrix ι ι ℝ)
    (J : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ)
    (hJ : ∀ X Y, weightedMatrixPairing π X (J Y) =
      - weightedMatrixPairing π (J X) Y) :
    weightedMatrixPairing π (constantOneMatrix (ι := ι))
      (J (constantOneMatrix (ι := ι)) +
        markovLeftOnsager P entropyForce) = 0 := by
  let H : Matrix ι ι ℝ := constantOneMatrix
  have hπ : ∀ i, 0 ≤ π i := fun i => le_of_lt (hπpos i)
  have hRev : weightedMatrixPairing π H (J H) = 0 := by
    simpa [H] using weightedMatrixPairing_energy_reversible_eq_zero π J hJ
  have hDiss : weightedMatrixPairing π H
      (markovLeftOnsager P entropyForce) = 0 := by
    have h :=
      (markovMetriplecticFlow P π hP hDB hπ entropyForce (J H)).dissipative_energy_change_eq_zero
    simpa [H, markovMetriplecticFlow, markovLeftOnsager] using h
  rw [weightedMatrixPairing_add_right, hRev, hDiss]
  simp

end InfoGeometry.QuantumContext.MarkovDrazin
