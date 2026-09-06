import InfoGeometry.Jordan.LogDet
import InfoGeometry.Thermo.Gibbs

/-!
# Thermodynamics from Log-Det (Burg) Energy

Finite Gibbs thermodynamics where energy is induced by the SPD log-det/Burg
divergence to a fixed reference matrix.
-/

namespace InfoGeometry.Thermo

open InfoGeometry.Jordan

section Finite

variable {n : ℕ}
variable {Ω : Type _} [Fintype Ω]

/-- Energy induced by log-det/Burg divergence to a reference SPD matrix. -/
noncomputable def energyFromLogDet
    (X0 : SPD n) (X : Ω → SPD n) : Ω → ℝ :=
  fun ω => logDetBregman (X ω) X0

/-- Gibbs probability induced by log-det/Burg energy. -/
noncomputable def gibbsProbFromLogDet
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) :
    Ω → ℝ :=
  gibbsProb (energyFromLogDet (X0 := X0) X) ε

/-- Free energy induced by log-det/Burg energy. -/
noncomputable def freeEnergyFromLogDet
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) : ℝ :=
  freeEnergy (energyFromLogDet (X0 := X0) X) ε

/-- Named partition alias for the log-det/Burg-induced ensemble. -/
noncomputable def partitionFromLogDet
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) : ℝ :=
  Z (energyFromLogDet (X0 := X0) X) ε

section ProbabilisticLemmas

variable [Nonempty Ω]

lemma partitionFromLogDet_pos
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) :
    0 < Z (energyFromLogDet (X0 := X0) X) ε :=
  Z_pos (E := energyFromLogDet (X0 := X0) X) ε

lemma partitionFromLogDet_pos'
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) :
    0 < partitionFromLogDet (X0 := X0) X ε := by
  simpa [partitionFromLogDet] using partitionFromLogDet_pos (X0 := X0) (X := X) ε

lemma gibbsProbFromLogDet_nonneg
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) (ω : Ω) :
    0 ≤ gibbsProbFromLogDet (X0 := X0) X ε ω := by
  simpa [gibbsProbFromLogDet] using
    (gibbsProb_nonneg (E := energyFromLogDet (X0 := X0) X) ε ω)

lemma partitionFromLogDet_ne_zero
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) :
    partitionFromLogDet (X0 := X0) X ε ≠ 0 := by
  simpa [partitionFromLogDet] using
    (partitionFromLogDet_pos (X0 := X0) (X := X) ε).ne'

lemma gibbsProbFromLogDet_sum_one
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) :
    ∑ ω, gibbsProbFromLogDet (X0 := X0) X ε ω = 1 := by
  simpa [gibbsProbFromLogDet] using
    (gibbsProb_sum_one (E := energyFromLogDet (X0 := X0) X) ε)

omit [Nonempty Ω] in
@[simp] lemma freeEnergyFromLogDet_eq_neg_scale_log_partition
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) :
    freeEnergyFromLogDet (X0 := X0) X ε
      = -ε * Real.log (partitionFromLogDet (X0 := X0) X ε) := by
  rfl

lemma freeEnergyFromLogDet_eq_internal_sub_scale_entropy
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) (hε : ε ≠ 0) :
    freeEnergyFromLogDet (X0 := X0) X ε
      =
    internalEnergy (energyFromLogDet (X0 := X0) X) ε
      - ε * shannonEntropy (energyFromLogDet (X0 := X0) X) ε := by
  simpa [freeEnergyFromLogDet] using
    (freeEnergy_eq_internal_sub_scale_entropy
      (E := energyFromLogDet (X0 := X0) X) ε hε)

lemma freeEnergyFromLogDet_eq_internal_sub_scale_entropy_of_pos
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) (hε : 0 < ε) :
    freeEnergyFromLogDet (X0 := X0) X ε
      =
    internalEnergy (energyFromLogDet (X0 := X0) X) ε
      - ε * shannonEntropy (energyFromLogDet (X0 := X0) X) ε :=
  freeEnergyFromLogDet_eq_internal_sub_scale_entropy (X0 := X0) (X := X) ε hε.ne'

end ProbabilisticLemmas

end Finite

end InfoGeometry.Thermo
