import Mathlib
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.SplitCliffordChiralProjection
import InfoGeometry.Canonical.DrazinAnomalousProjector
import InfoGeometry.Canonical.ModularSL2R

/-!
# InfoGeometry.Canonical.CantorHaarDiracSea

Finite Haar/chiral readout on the `M₂(ℝ)` seed.

This file formalizes the concrete identities:
- `φ = N_left + N_right = 1`,
- `ψ = N_left - N_right = K`,
- `ψ² = 1`,
- `traceForm ψ N = 0`.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.CantorHaarDiracSea

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.SplitCliffordChiralProjection
open InfoGeometry.Canonical.DrazinAnomalousProjector
open InfoGeometry.Canonical.ModularSL2R

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Haar scaling operator (`φ`). -/
noncomputable def HaarPhi : M2R := N_left + N_right

/-- Haar wavelet operator (`ψ`). -/
noncomputable def HaarPsi : M2R := N_left - N_right

/-- `φ` is the identity. -/
theorem HaarPhi_is_identity : HaarPhi = (1 : M2R) := by
  unfold HaarPhi
  simpa using mp_projector_completeness

/-- `ψ` is exactly the modular generator `K`. -/
theorem HaarPsi_eq_K : HaarPsi = InfoGeometry.Canonical.ModularLorentzBoost.K := by
  unfold HaarPsi
  simpa using K_eq_chiral_difference.symm

/-- `ψ² = 1` (involution). -/
theorem HaarPsi_involution : HaarPsi * HaarPsi = (1 : M2R) := by
  rw [HaarPsi_eq_K, InfoGeometry.Canonical.ModularLorentzBoost.K_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Boundary regularization: `traceForm ψ N = 0`. -/
theorem HaarPsi_boundary_regularization :
    traceForm HaarPsi N = 0 := by
  rw [HaarPsi_eq_K]
  exact trace_K_boundary_from_MP

end InfoGeometry.Canonical.CantorHaarDiracSea

