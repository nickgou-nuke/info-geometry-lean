import InfoGeometry.Convex.Legendre
import InfoGeometry.Convex.Duality
import InfoGeometry.Thermo.Gibbs

/-!
# Thermodynamics from Bregman Energy

Bind finite thermodynamics to a Legendre potential by defining energy as a
Bregman divergence gap to a reference point.
-/

namespace InfoGeometry.Thermo

open InfoGeometry.Convex

section Finite

variable {Ω : Type _} [Fintype Ω]

/-- Energy induced from a Legendre potential via a reference point `θ₀`. -/
noncomputable def energyFromBregman
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) : Ω → ℝ :=
  fun ω => L.bregman (θ ω) θ0

/-- Compatibility alias for Bregman-induced energy. -/
@[deprecated energyFromBregman (since := "2026-02-18")]
noncomputable def energyFromDivergence
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) : Ω → ℝ :=
  energyFromBregman (L := L) θ0 θ

/-- Gibbs probability induced by Bregman energy. -/
noncomputable def gibbsProbFromBregman
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    Ω → ℝ :=
  gibbsProb (energyFromBregman (L := L) θ0 θ) ε

/-- Free energy induced by Bregman energy. -/
noncomputable def freeEnergyFromBregman
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) : ℝ :=
  freeEnergy (energyFromBregman (L := L) θ0 θ) ε

/-! ### Optimal-Transport / Bayesian Naming Bridge -/

/-- OT naming alias: Bregman-induced energy as a transport ground energy. -/
noncomputable abbrev entropicTransportEnergyFromBregman
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) : Ω → ℝ :=
  energyFromBregman (L := L) θ0 θ

/-- OT naming alias: Gibbs law as an entropic transport plan on finite support. -/
noncomputable abbrev entropicTransportPlanFromBregman
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    Ω → ℝ :=
  gibbsProbFromBregman (L := L) θ0 θ ε

/-- Bayesian naming alias: same scalar free-energy objective. -/
noncomputable abbrev bayesianFreeEnergyFromBregman
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) : ℝ :=
  freeEnergyFromBregman (L := L) θ0 θ ε

omit [Fintype Ω] in
@[simp] lemma entropicTransportEnergyFromBregman_eq
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) :
    entropicTransportEnergyFromBregman (L := L) θ0 θ
      = energyFromBregman (L := L) θ0 θ := rfl

@[simp] lemma entropicTransportPlanFromBregman_eq
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    entropicTransportPlanFromBregman (L := L) θ0 θ ε
      = gibbsProbFromBregman (L := L) θ0 θ ε := rfl

@[simp] lemma bayesianFreeEnergyFromBregman_eq
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    bayesianFreeEnergyFromBregman (L := L) θ0 θ ε
      = freeEnergyFromBregman (L := L) θ0 θ ε := rfl

/-- Information Boltzmann weight for Bregman-induced energy. -/
noncomputable def gibbsWeightDivergence
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(energyFromBregman (L := L) θ0 θ ω) / ε)

/-- Partition function for the Bregman-induced ensemble. -/
noncomputable def partitionDivergence
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) : ℝ :=
  ∑ ω, gibbsWeightDivergence (L := L) θ0 θ ε ω

/-- Free energy for the Bregman-induced ensemble. -/
noncomputable def freeEnergyDivergence
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) : ℝ :=
  -ε * Real.log (partitionDivergence (L := L) θ0 θ ε)

lemma freeEnergyDivergence_def
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    freeEnergyDivergence (L := L) θ0 θ ε
      =
    -ε * Real.log (∑ ω, Real.exp (-(L.bregman (θ ω) θ0) / ε)) := by
  simp [freeEnergyDivergence, partitionDivergence, gibbsWeightDivergence,
    energyFromBregman]

section ProbabilisticLemmas

variable [Nonempty Ω]

omit [Nonempty Ω] in
@[simp] lemma partitionDivergence_eq_Z
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    partitionDivergence (L := L) θ0 θ ε
      = Z (E := energyFromBregman (L := L) θ0 θ) ε := by
  simp [partitionDivergence, gibbsWeightDivergence, Z, weight]

lemma partitionDivergence_pos
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    0 < partitionDivergence (L := L) θ0 θ ε := by
  simpa [partitionDivergence, gibbsWeightDivergence, energyFromBregman] using
    (Z_pos (E := energyFromBregman (L := L) θ0 θ) ε)

lemma partitionDivergence_ne_zero
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    partitionDivergence (L := L) θ0 θ ε ≠ 0 :=
  (partitionDivergence_pos (L := L) θ0 θ ε).ne'

lemma gibbsProbFromBregman_nonneg
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) (ω : Ω) :
    0 ≤ gibbsProbFromBregman (L := L) θ0 θ ε ω := by
  simpa [gibbsProbFromBregman] using
    (gibbsProb_nonneg (E := energyFromBregman (L := L) θ0 θ) ε ω)

lemma gibbsProbFromBregman_sum_one
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    ∑ ω, gibbsProbFromBregman (L := L) θ0 θ ε ω = 1 := by
  simpa [gibbsProbFromBregman] using
    (gibbsProb_sum_one (E := energyFromBregman (L := L) θ0 θ) ε)

omit [Nonempty Ω] in
lemma gibbsProbFromBregman_eq_weight_over_partition
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) (ω : Ω) :
    gibbsProbFromBregman (L := L) θ0 θ ε ω
      = gibbsWeightDivergence (L := L) θ0 θ ε ω
          / partitionDivergence (L := L) θ0 θ ε := by
  simp [gibbsProbFromBregman, gibbsProb, gibbsWeightDivergence, partitionDivergence_eq_Z, weight]

omit [Nonempty Ω] in
@[simp] lemma freeEnergyDivergence_eq_freeEnergyFromBregman
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    freeEnergyDivergence (L := L) θ0 θ ε
      = freeEnergyFromBregman (L := L) θ0 θ ε := by
  simp [freeEnergyDivergence, freeEnergyFromBregman, freeEnergy, logZ,
    partitionDivergence, gibbsWeightDivergence, Z, weight]

lemma freeEnergyFromBregman_eq_internal_sub_scale_entropy
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ)
    (hε : ε ≠ 0) :
    freeEnergyFromBregman (L := L) θ0 θ ε
      =
    internalEnergy (energyFromBregman (L := L) θ0 θ) ε
      - ε * shannonEntropy (energyFromBregman (L := L) θ0 θ) ε := by
  simpa [freeEnergyFromBregman] using
    (freeEnergy_eq_internal_sub_scale_entropy
      (E := energyFromBregman (L := L) θ0 θ) ε hε)

lemma freeEnergyDivergence_eq_internal_sub_scale_entropy
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ)
    (hε : ε ≠ 0) :
    freeEnergyDivergence (L := L) θ0 θ ε
      =
    internalEnergy (energyFromBregman (L := L) θ0 θ) ε
      - ε * shannonEntropy (energyFromBregman (L := L) θ0 θ) ε := by
  rw [freeEnergyDivergence_eq_freeEnergyFromBregman]
  exact freeEnergyFromBregman_eq_internal_sub_scale_entropy
    (L := L) θ0 θ ε hε

lemma bayesianFreeEnergyFromBregman_eq_internal_sub_scale_entropy
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ)
    (hε : ε ≠ 0) :
    bayesianFreeEnergyFromBregman (L := L) θ0 θ ε
      =
    internalEnergy (energyFromBregman (L := L) θ0 θ) ε
      - ε * shannonEntropy (energyFromBregman (L := L) θ0 θ) ε := by
  simpa [bayesianFreeEnergyFromBregman] using
    (freeEnergyFromBregman_eq_internal_sub_scale_entropy
      (L := L) θ0 θ ε hε)

end ProbabilisticLemmas

lemma KL_param_eq_bregman_energy
    (L : LegendrePotential) (θ θ' : ℝ) :
    InfoGeometry.ConvexDuality.KL_param L.f θ θ' = L.bregman θ' θ := by
  simp [InfoGeometry.ConvexDuality.KL_param, InfoGeometry.ConvexDuality.bregman,
    InfoGeometry.bregmanDiv, InfoGeometry.Convex.LegendrePotential.bregman]

/-- OT/convex bridge: parameterized KL cost is exactly the Bregman transport gap. -/
lemma entropicTransportCost_eq_bregman_gap
    (L : LegendrePotential) (θ θ' : ℝ) :
    InfoGeometry.ConvexDuality.KL_param L.f θ θ' = L.bregman θ' θ :=
  KL_param_eq_bregman_energy (L := L) θ θ'

end Finite

end InfoGeometry.Thermo
