import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Physics.ChiralCausalCone
import Mathlib.Tactic

/-! Infinitesimal root weights for the bipolar logarithmic Cartan element. -/

noncomputable section

namespace InfoGeometry.Canonical.BipolarPauliRootWeights

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Physics.ChiralCausalCone

def cartan (s : ℂ) : M2C := (bipolarLog s / 2) • σ3c

def commutator (A B : M2C) : M2C := A * B - B * A

theorem cartan_comm_sigmaPlus (s : ℂ) :
    commutator (cartan s) σPlus = bipolarLog s • σPlus := by
  unfold commutator cartan
  rw [smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]
  rw [comm_σ3_σPlus]
  simp [smul_smul]

theorem cartan_comm_sigmaMinus (s : ℂ) :
    commutator (cartan s) σMinus = -bipolarLog s • σMinus := by
  unfold commutator cartan
  rw [smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]
  rw [comm_σ3_σMinus]
  simp [smul_smul]

theorem cartan_root_weight_packet (s : ℂ) :
    commutator (cartan s) σPlus = bipolarLog s • σPlus ∧
      commutator (cartan s) σMinus = -bipolarLog s • σMinus :=
  ⟨cartan_comm_sigmaPlus s, cartan_comm_sigmaMinus s⟩

end InfoGeometry.Canonical.BipolarPauliRootWeights
