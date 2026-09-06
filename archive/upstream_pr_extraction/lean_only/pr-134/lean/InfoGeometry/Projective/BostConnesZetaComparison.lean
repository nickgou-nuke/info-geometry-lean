import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Canonical.BostConnesAmplituhedronBoundary
import InfoGeometry.Projective.BostConnesZeta
import InfoGeometry.Physics.AmplituhedronVolume
import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Bost-Connes Zeta-Volume Comparison

This module packages a theorem-safe zeta-volume comparison interface by
instantiating `AmplituhedronZetaComparison` from an explicit comparison
premise. It provides the Bost--Connes zeta readout, local summand bridges to
Bost--Connes KMS projection weights, and a readback theorem for supplied
volume comparisons. It does not assert a global analytic equality between the
zeta partition function and an all-loop amplituhedron volume.
-/

open InfoGeometry.Canonical.BostConnesAmplituhedronBoundary
open InfoGeometry.Projective.BostConnes
open InfoGeometry.Physics.AmplituhedronVolume
open InfoGeometry.Canonical.BostConnesKMS
open InfoGeometry.Clifford.LogCftMonodromy

noncomputable section

/-- The Riemann zeta partition function evaluated at β = 2.
    We fix this value across the manifold as a readout used by the comparison carrier. -/
def bost_connes_zeta : BostConnesPartitionData ℂ :=
  fun _ => riemannZeta (2 : ℂ)

/-- Trivial readback of the supplied comparison premise. -/
theorem zeta_volume_comparison_readback (β : ℂ) (L : ℕ)
    (Vol : AmplituhedronVolumeData ℂ)
    (hComparison : bost_connes_zeta β = Vol L) :
    bost_connes_zeta β = Vol L :=
  hComparison

/--
Termwise bridge between the normalized Hadjiivanov/amplituhedron trace summand
and the unnormalized diagonal Bost--Connes KMS projection readout.

This is a local summand equality; it is not a global zeta-volume or all-loop
amplituhedron theorem.
-/
theorem amplituhedron_volume_summand_eq_kms_readout (β : ℝ) (n : ℕ) :
    let n_pnat : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
    Complex.exp (- (β : ℂ) * Real.log (n + 1 : ℝ)) =
      ((kmsProjectionReadout β 1 n_pnat n_pnat) : ℂ) := by
  intro n_pnat
  dsimp [kmsProjectionReadout, kmsProjectionWeight]
  have h_eq : (n_pnat : ℕ) = n + 1 := rfl
  rw [if_pos rfl, div_one]
  have h_cast : ((n_pnat : ℕ) : ℝ) = (n + 1 : ℝ) := by
    rw [h_eq]
    push_cast
    rfl
  rw [h_cast]
  have h_rpow : ((n + 1 : ℝ) ^ (-β)) = Real.exp (Real.log (n + 1 : ℝ) * -β) := by
    exact Real.rpow_def_of_pos (by positivity) (-β)
  rw [h_rpow]
  push_cast
  congr 1
  ring

/--
Termwise bridge from the normalized amplituhedron/Hadjiivanov trace summand to
the diagonal Bost--Connes KMS readout.
-/
theorem normalized_trace_summand_eq_kms_readout (β : ℝ) (n : ℕ) :
    let n_pnat : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
    (1 / 2 : ℂ) *
        (hadjiivanovMonodromy (conformalWeight (β : ℂ) (n + 1))).trace =
      ((kmsProjectionReadout β 1 n_pnat n_pnat) : ℂ) := by
  intro n_pnat
  rw [normalized_trace_eq_dirichlet_term]
  have h_eq : (n_pnat : ℕ) = n + 1 := rfl
  dsimp [kmsProjectionReadout, kmsProjectionWeight]
  rw [if_pos rfl, div_one]
  have h_cast : ((n_pnat : ℕ) : ℝ) = (n + 1 : ℝ) := by
    rw [h_eq]
    push_cast
    rfl
  have hlog : Real.log (((n + 1 : ℕ) : ℝ)) = Real.log (n + 1 : ℝ) := by
    push_cast
    rfl
  rw [hlog, h_cast]
  have h_rpow : ((n + 1 : ℝ) ^ (-β)) = Real.exp (Real.log (n + 1 : ℝ) * -β) := by
    exact Real.rpow_def_of_pos (by positivity) (-β)
  rw [h_rpow]
  push_cast
  congr 1
  ring

/-- The zeta-volume comparison carrier built from an explicit comparison premise. -/
def bost_connes_amplituhedron_synthesis
    (Vol : AmplituhedronVolumeData ℂ)
    (hComparison : ∀ (β : ℂ) (L : ℕ), bost_connes_zeta β = Vol L) :
    InfoGeometry.Canonical.BostConnesAmplituhedronBoundary.AmplituhedronZetaComparison ℂ where
  Z := bost_connes_zeta
  Vol := Vol
  comparison β L := hComparison β L

/-- Read back the family equality using the explicit comparison. -/
theorem bost_connes_comparison_readback (Vol : AmplituhedronVolumeData ℂ)
    (hComparison : ∀ (β : ℂ) (L : ℕ), bost_connes_zeta β = Vol L) :
    ∀ (β : ℂ) (L : ℕ),
      (bost_connes_amplituhedron_synthesis Vol hComparison).Z β =
        (bost_connes_amplituhedron_synthesis Vol hComparison).Vol L := by
  intro β L
  exact (bost_connes_amplituhedron_synthesis Vol hComparison).comparison β L

end
