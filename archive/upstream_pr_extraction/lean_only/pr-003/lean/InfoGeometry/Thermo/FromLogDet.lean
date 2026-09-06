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
    [Nonempty Ω]
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) :
    Ω → ℝ :=
  gibbsProb (energyFromLogDet (X0 := X0) X) ε

/-- Free energy induced by log-det/Burg energy. -/
noncomputable def freeEnergyFromLogDet
    [Nonempty Ω]
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) : ℝ :=
  freeEnergy (energyFromLogDet (X0 := X0) X) ε

section ProbabilisticLemmas

variable [Nonempty Ω]

lemma partitionFromLogDet_pos
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) :
    0 < Z (energyFromLogDet (X0 := X0) X) ε :=
  Z_pos (E := energyFromLogDet (X0 := X0) X) ε

lemma gibbsProbFromLogDet_sum_one
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) :
    ∑ ω, gibbsProbFromLogDet (X0 := X0) X ε ω = 1 := by
  simpa [gibbsProbFromLogDet] using
    (gibbsProb_sum_one (E := energyFromLogDet (X0 := X0) X) ε)

lemma freeEnergyFromLogDet_eq_internal_sub_scale_entropy
    (X0 : SPD n) (X : Ω → SPD n) (ε : ℝ) (hε : ε ≠ 0) :
    freeEnergyFromLogDet (X0 := X0) X ε
      =
    internalEnergy (energyFromLogDet (X0 := X0) X) ε
      - ε * shannonEntropy (energyFromLogDet (X0 := X0) X) ε := by
  simpa [freeEnergyFromLogDet] using
    (freeEnergy_eq_internal_sub_scale_entropy
      (E := energyFromLogDet (X0 := X0) X) ε hε)

end ProbabilisticLemmas

end Finite

end InfoGeometry.Thermo

