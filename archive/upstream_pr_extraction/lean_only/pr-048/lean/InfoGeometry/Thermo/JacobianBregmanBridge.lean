import InfoGeometry.Topology.ThermodynamicSL2MobiusFlow
import InfoGeometry.Thermo.FromBregman
import InfoGeometry.Thermo.FromLogDet

/-!
# Jacobian log-volume bridge to finite Bregman/log-det thermodynamics

This module does not identify a Möbius Jacobian with a statistical free energy by
name.  It gives typed bridge theorems: once a pointwise calibration proves that
an existing Legendre/Bregman or SPD log-det energy equals the negative local
Möbius log-volume entropy, the corresponding finite Gibbs free energy is the
Gibbs free energy of that calibrated Jacobian-derived energy.
-/

noncomputable section

namespace InfoGeometry.Thermo

open InfoGeometry.Convex
open InfoGeometry.Jordan
open InfoGeometry.Topology.ThermodynamicSL2MobiusFlow

section Finite

variable {Ω : Type _}
variable {n : ℕ}

/-- Finite energy obtained from the negative local Möbius log-volume entropy. -/
noncomputable def jacobianLogVolumeEnergy
    (v : ThermodynamicSL2Variation) (kB : ℝ)
    (time : Ω → ℂ) (point : Ω → ℂ) : Ω → ℝ :=
  fun ω => -v.boltzmannLogJacobianEntropy kB (time ω) (point ω)

/-- Finite Gibbs free energy of the Jacobian log-volume energy. -/
noncomputable def freeEnergyFromJacobianLogVolume
    [Fintype Ω] (v : ThermodynamicSL2Variation) (kB : ℝ)
    (time : Ω → ℂ) (point : Ω → ℂ) (ε : ℝ) : ℝ :=
  freeEnergy (jacobianLogVolumeEnergy (Ω := Ω) v kB time point) ε

/-- Squared barrier energy from the local Möbius log-volume entropy. -/
noncomputable def jacobianLogVolumeBarrierEnergy
    (v : ThermodynamicSL2Variation) (kB : ℝ)
    (time : Ω → ℂ) (point : Ω → ℂ) : Ω → ℝ :=
  fun ω => (v.boltzmannLogJacobianEntropy kB (time ω) (point ω)) ^ (2 : ℕ)

/-- Finite Gibbs free energy of the squared Jacobian log-volume barrier. -/
noncomputable def freeEnergyFromJacobianLogVolumeBarrier
    [Fintype Ω] (v : ThermodynamicSL2Variation) (kB : ℝ)
    (time : Ω → ℂ) (point : Ω → ℂ) (ε : ℝ) : ℝ :=
  freeEnergy (jacobianLogVolumeBarrierEnergy v kB time point) ε

/-- A one-dimensional SPD carrier with determinant `exp r`. -/
noncomputable def spdOneExp (r : ℝ) : SPD 1 where
  mat := Matrix.diagonal (fun _ : Fin 1 => Real.exp r)
  symm := Matrix.isSymm_diagonal _
  pos := Matrix.PosDef.diagonal (fun _ => Real.exp_pos r)

/-- Determinant readout of the one-dimensional exponential SPD carrier. -/
lemma spdOneExp_det (r : ℝ) : Matrix.det (spdOneExp r).mat = Real.exp r := by
  rw [Matrix.det_fin_one]
  simp [spdOneExp]

/-- The log-det/Burg divergence of `spdOneExp r` from `spdOneExp 0` is `r²`. -/
lemma logDetBregman_spdOneExp_zero (r : ℝ) :
    logDetBregman (spdOneExp r) (spdOneExp 0) = r ^ (2 : ℕ) := by
  rw [logDetBregman_eq_burg_form]
  rw [spdOneExp_det, spdOneExp_det]
  simp

/-- A Legendre/Bregman calibration identifies its pointwise energy with the
negative local Möbius log-volume entropy. -/
theorem energyFromBregman_eq_jacobianLogVolumeEnergy
    (v : ThermodynamicSL2Variation) (kB : ℝ)
    (time : Ω → ℂ) (point : Ω → ℂ)
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ)
    (hcal : ∀ ω,
      L.bregman (θ ω) θ0 =
        -v.boltzmannLogJacobianEntropy kB (time ω) (point ω)) :
    energyFromBregman (L := L) θ0 θ =
      jacobianLogVolumeEnergy (Ω := Ω) v kB time point := by
  funext ω
  simp [energyFromBregman, jacobianLogVolumeEnergy, hcal ω]

/-- Under a pointwise Legendre/Bregman calibration, the finite Bregman free
energy is exactly the Gibbs free energy of the Jacobian log-volume energy. -/
theorem freeEnergyFromBregman_eq_freeEnergyFromJacobianLogVolume
    [Fintype Ω] (v : ThermodynamicSL2Variation) (kB : ℝ)
    (time : Ω → ℂ) (point : Ω → ℂ)
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ)
    (hcal : ∀ ω,
      L.bregman (θ ω) θ0 =
        -v.boltzmannLogJacobianEntropy kB (time ω) (point ω)) :
    freeEnergyFromBregman (L := L) θ0 θ ε =
      freeEnergyFromJacobianLogVolume (Ω := Ω) v kB time point ε := by
  unfold freeEnergyFromBregman freeEnergyFromJacobianLogVolume
  rw [energyFromBregman_eq_jacobianLogVolumeEnergy
    (v := v) (kB := kB) (time := time) (point := point)
    (L := L) (θ0 := θ0) (θ := θ) hcal]

/-- The self-Bregman point calibrates the identity-time Jacobian log-volume energy. -/
theorem bregmanSelf_calibrates_zeroTimeJacobianLogVolume
    (v : ThermodynamicSL2Variation) (kB : ℝ)
    (point : Ω → ℂ) (L : LegendrePotential) (θ0 : ℝ) :
    ∀ ω : Ω,
      L.bregman θ0 θ0 =
        -v.boltzmannLogJacobianEntropy kB 0 (point ω) := by
  intro ω
  simp [InfoGeometry.bregmanDiv_self,
    ThermodynamicSL2Variation.boltzmannLogJacobianEntropy_zero]

/-- Consequently, a constant self-Bregman ensemble realizes the identity-time
Jacobian log-volume free energy. -/
theorem freeEnergyFromBregman_self_eq_zeroTimeJacobianLogVolume
    [Fintype Ω] (v : ThermodynamicSL2Variation) (kB : ℝ)
    (point : Ω → ℂ) (L : LegendrePotential) (θ0 ε : ℝ) :
    freeEnergyFromBregman (L := L) θ0 (fun _ : Ω => θ0) ε =
      freeEnergyFromJacobianLogVolume (Ω := Ω) v kB (fun _ : Ω => 0) point ε := by
  exact freeEnergyFromBregman_eq_freeEnergyFromJacobianLogVolume
    (v := v) (kB := kB) (time := fun _ : Ω => 0) (point := point)
    (L := L) (θ0 := θ0) (θ := fun _ : Ω => θ0) (ε := ε)
    (bregmanSelf_calibrates_zeroTimeJacobianLogVolume
      (v := v) (kB := kB) (point := point) (L := L) (θ0 := θ0))

/-- A log-det/Burg calibration identifies its pointwise energy with the negative
local Möbius log-volume entropy. -/
theorem energyFromLogDet_eq_jacobianLogVolumeEnergy
    (v : ThermodynamicSL2Variation) (kB : ℝ)
    (time : Ω → ℂ) (point : Ω → ℂ)
    (X0 : SPD n) (X : Ω → SPD n)
    (hcal : ∀ ω,
      logDetBregman (X ω) X0 =
        -v.boltzmannLogJacobianEntropy kB (time ω) (point ω)) :
    energyFromLogDet (X0 := X0) X =
      jacobianLogVolumeEnergy (Ω := Ω) v kB time point := by
  funext ω
  simp [energyFromLogDet, jacobianLogVolumeEnergy, hcal ω]

/-- Under a pointwise log-det/Burg calibration, the finite log-det free energy is
exactly the Gibbs free energy of the Jacobian log-volume energy. -/
theorem freeEnergyFromLogDet_eq_freeEnergyFromJacobianLogVolume
    [Fintype Ω] (v : ThermodynamicSL2Variation) (kB : ℝ)
    (time : Ω → ℂ) (point : Ω → ℂ)
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ)
    (hcal : ∀ ω,
      logDetBregman (X ω) X0 =
        -v.boltzmannLogJacobianEntropy kB (time ω) (point ω)) :
    freeEnergyFromLogDet (X0 := X0) X ε =
      freeEnergyFromJacobianLogVolume (Ω := Ω) v kB time point ε := by
  unfold freeEnergyFromLogDet freeEnergyFromJacobianLogVolume
  rw [energyFromLogDet_eq_jacobianLogVolumeEnergy
    (v := v) (kB := kB) (time := time) (point := point)
    (X0 := X0) (X := X) hcal]

/-- The self log-det/Burg point calibrates the identity-time Jacobian log-volume energy. -/
theorem logDetSelf_calibrates_zeroTimeJacobianLogVolume
    (v : ThermodynamicSL2Variation) (kB : ℝ)
    (point : Ω → ℂ) (X0 : SPD n) :
    ∀ ω : Ω,
      logDetBregman X0 X0 =
        -v.boltzmannLogJacobianEntropy kB 0 (point ω) := by
  intro ω
  simp [ThermodynamicSL2Variation.boltzmannLogJacobianEntropy_zero]

/-- Consequently, a constant self-log-det ensemble realizes the identity-time
Jacobian log-volume free energy. -/
theorem freeEnergyFromLogDet_self_eq_zeroTimeJacobianLogVolume
    [Fintype Ω] (v : ThermodynamicSL2Variation) (kB : ℝ)
    (point : Ω → ℂ) (X0 : SPD n) (ε : ℝ) :
    freeEnergyFromLogDet (X0 := X0) (fun _ : Ω => X0) ε =
      freeEnergyFromJacobianLogVolume (Ω := Ω) v kB (fun _ : Ω => 0) point ε := by
  exact freeEnergyFromLogDet_eq_freeEnergyFromJacobianLogVolume
    (v := v) (kB := kB) (time := fun _ : Ω => 0) (point := point)
    (X0 := X0) (X := fun _ : Ω => X0) (ε := ε)
    (logDetSelf_calibrates_zeroTimeJacobianLogVolume
      (v := v) (kB := kB) (point := point) (X0 := X0))

/-- The one-dimensional exponential SPD carrier realizes the squared local
Möbius log-volume entropy as a log-det/Burg energy. -/
theorem logDet_spdOneExp_calibrates_jacobianLogVolumeBarrier
    (v : ThermodynamicSL2Variation) (kB : ℝ)
    (time : Ω → ℂ) (point : Ω → ℂ) :
    ∀ ω : Ω,
      logDetBregman
        (spdOneExp (v.boltzmannLogJacobianEntropy kB (time ω) (point ω)))
        (spdOneExp 0) =
      jacobianLogVolumeBarrierEnergy v kB time point ω := by
  intro ω
  simp [jacobianLogVolumeBarrierEnergy, logDetBregman_spdOneExp_zero]

/-- Therefore the finite log-det free energy of the exponential SPD carrier is
the finite Gibbs free energy of the squared Jacobian log-volume barrier. -/
theorem freeEnergyFromLogDet_spdOneExp_eq_jacobianLogVolumeBarrier
    [Fintype Ω] (v : ThermodynamicSL2Variation) (kB : ℝ)
    (time : Ω → ℂ) (point : Ω → ℂ) (ε : ℝ) :
    freeEnergyFromLogDet (X0 := spdOneExp 0)
      (fun ω : Ω => spdOneExp (v.boltzmannLogJacobianEntropy kB (time ω) (point ω))) ε =
    freeEnergyFromJacobianLogVolumeBarrier v kB time point ε := by
  unfold freeEnergyFromLogDet freeEnergyFromJacobianLogVolumeBarrier energyFromLogDet
  congr 1
  funext ω
  exact logDet_spdOneExp_calibrates_jacobianLogVolumeBarrier v kB time point ω

end Finite

end InfoGeometry.Thermo
