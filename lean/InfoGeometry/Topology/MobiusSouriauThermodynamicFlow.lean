import InfoGeometry.Topology.MobiusGeometry
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.Metriplectic
import InfoGeometry.Thermo.Gibbs
import InfoGeometry.Physics.SouriauEntropyFoliation

/-!
# Möbius--Souriau finite thermodynamic symmetry

This module connects the existing Möbius action on the Riemann sphere to the
finite Souriau/Gibbs thermodynamic owners.

A Möbius transformation that permutes a finite chart and preserves an effective
potential preserves the induced partition function, Massieu potential, Gibbs
law, mean energy, Boltzmann entropy, and free energy. This is the finite
reversible symmetry channel. No differentiable one-parameter PGL₂ flow or
infinite-dimensional metriplectic evolution is claimed here.
-/

namespace InfoGeometry.Topology.MobiusSouriauThermodynamicFlow

open scoped BigOperators
open InfoGeometry
open InfoGeometry.Physics.SouriauMassieuPlanckFunctional

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Pull an energy function along a finite symmetry permutation. -/
def pullEnergy (σ : Equiv.Perm ι) (energy : ι → ℝ) : ι → ℝ :=
  InfoGeometry.Physics.SouriauEntropyFoliation.permuteWeight σ energy

/-- The finite Souriau partition function is invariant under state relabeling. -/
theorem souriauPartition_pullEnergy
    (σ : Equiv.Perm ι) (beta : ℝ) (energy : ι → ℝ) :
    souriauPartition beta (pullEnergy σ energy) =
      souriauPartition beta energy := by
  unfold souriauPartition pullEnergy
  simpa using
    (Fintype.sum_equiv σ.symm
      (fun i => Real.exp (-beta * energy (σ.symm i)))
      (fun i => Real.exp (-beta * energy i))
      (fun _ => rfl))

/-- Gibbs weights transform equivariantly under finite state relabeling. -/
theorem gibbsWeight_pullEnergy
    (σ : Equiv.Perm ι) (beta : ℝ) (energy : ι → ℝ) (i : ι) :
    gibbsWeight beta (pullEnergy σ energy) i =
      gibbsWeight beta energy (σ.symm i) := by
  unfold gibbsWeight
  rw [souriauPartition_pullEnergy]
  rfl

/-- Mean energy is invariant under finite state relabeling. -/
theorem meanEnergy_pullEnergy
    (σ : Equiv.Perm ι) (beta : ℝ) (energy : ι → ℝ) :
    meanEnergy beta (pullEnergy σ energy) = meanEnergy beta energy := by
  unfold meanEnergy
  simp_rw [gibbsWeight_pullEnergy, pullEnergy]
  simpa using
    (Fintype.sum_equiv σ.symm
      (fun i => gibbsWeight beta energy (σ.symm i) * energy (σ.symm i))
      (fun i => gibbsWeight beta energy i * energy i)
      (fun _ => rfl))

/-- Boltzmann entropy is invariant under finite state relabeling. -/
theorem boltzmannEntropy_pullEnergy
    (σ : Equiv.Perm ι) (beta : ℝ) (energy : ι → ℝ) :
    boltzmannEntropy (gibbsWeight beta (pullEnergy σ energy)) =
      boltzmannEntropy (gibbsWeight beta energy) := by
  have hweight :
      gibbsWeight beta (pullEnergy σ energy) =
        InfoGeometry.Physics.SouriauEntropyFoliation.permuteWeight σ
          (gibbsWeight beta energy) := by
    funext i
    exact gibbsWeight_pullEnergy σ beta energy i
  rw [hweight]
  exact InfoGeometry.Physics.SouriauEntropyFoliation.boltzmannEntropy_permuteWeight
    σ (gibbsWeight beta energy)

/-- The Massieu/log-partition potential is invariant under relabeling. -/
theorem massieuPlanckPotential_pullEnergy
    (σ : Equiv.Perm ι) (beta : ℝ) (energy : ι → ℝ) :
    massieuPlanckPotential beta (pullEnergy σ energy) =
      massieuPlanckPotential beta energy := by
  unfold massieuPlanckPotential
  rw [souriauPartition_pullEnergy]

/-- Gibbs free energy is invariant under finite state relabeling. -/
theorem freeEnergy_pullEnergy [Nonempty ι]
    (σ : Equiv.Perm ι) (energy : ι → ℝ) (epsilon : ℝ) :
    InfoGeometry.Thermo.freeEnergy (pullEnergy σ energy) epsilon =
      InfoGeometry.Thermo.freeEnergy energy epsilon := by
  unfold InfoGeometry.Thermo.freeEnergy InfoGeometry.Thermo.logZ
    InfoGeometry.Thermo.Z InfoGeometry.Thermo.weight pullEnergy
  congr 2
  simpa using
    (Fintype.sum_equiv σ.symm
      (fun i => Real.exp (-energy (σ.symm i) / epsilon))
      (fun i => Real.exp (-energy i / epsilon))
      (fun _ => rfl))

/-- A Möbius transformation realizes a permutation of a finite sphere chart. -/
def RealizesFiniteOrbit
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι) : Prop :=
  ∀ i, M.eval (chart i) = chart (σ i)

/-- Effective energy induced on a finite chart of the Riemann sphere. -/
def inducedEnergy (potential : RiemannSphere → ℝ) (chart : ι → RiemannSphere) :
    ι → ℝ :=
  fun i => potential (chart i)

/-- Energy read on the Möbius-transformed finite chart. -/
def transportedEnergy
    (M : MobiusTransform) (potential : RiemannSphere → ℝ)
    (chart : ι → RiemannSphere) : ι → ℝ :=
  fun i => potential (M.eval (chart i))

omit [Fintype ι] in
/-- A realized finite Möbius orbit is exactly permutation transport of energy. -/
theorem transportedEnergy_eq_pullEnergy
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ)
    (horbit : RealizesFiniteOrbit M chart σ) :
    transportedEnergy M potential chart =
      pullEnergy σ.symm (inducedEnergy potential chart) := by
  funext i
  unfold transportedEnergy pullEnergy inducedEnergy
  rw [horbit]
  simp [InfoGeometry.Physics.SouriauEntropyFoliation.permuteWeight]

omit [Fintype ι] in
/-- An invariant effective potential is unchanged on the transformed chart. -/
theorem transportedEnergy_eq
    (M : MobiusTransform) (chart : ι → RiemannSphere)
    (potential : RiemannSphere → ℝ)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    transportedEnergy M potential chart = inducedEnergy potential chart := by
  funext i
  exact hpotential (chart i)

omit [Fintype ι] in
/-- Möbius invariance of the potential makes the induced finite energy equivariant. -/
theorem inducedEnergy_pullEnergy_eq
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ)
    (horbit : RealizesFiniteOrbit M chart σ)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    pullEnergy σ (inducedEnergy potential chart) = inducedEnergy potential chart := by
  funext i
  unfold pullEnergy inducedEnergy
  have horbit' := horbit (σ.symm i)
  have hpot := hpotential (chart (σ.symm i))
  rw [horbit'] at hpot
  simpa using hpot.symm

omit [Fintype ι] in
/-- Public alias: a chart-realized Möbius symmetry leaves the induced finite energy unchanged. -/
theorem mobius_realized_inducedEnergy_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ)
    (horbit : RealizesFiniteOrbit M chart σ)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    pullEnergy σ (inducedEnergy potential chart) = inducedEnergy potential chart :=
  inducedEnergy_pullEnergy_eq M chart σ potential horbit hpotential

/-- Gibbs weights are constant along the realized finite Möbius orbit. -/
theorem mobius_realized_gibbsWeight_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ) (beta : ℝ) (i : ι)
    (horbit : RealizesFiniteOrbit M chart σ)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    gibbsWeight beta (inducedEnergy potential chart) (σ.symm i) =
      gibbsWeight beta (inducedEnergy potential chart) i := by
  have hE := inducedEnergy_pullEnergy_eq M chart σ potential horbit hpotential
  have hg := gibbsWeight_pullEnergy σ beta (inducedEnergy potential chart) i
  rw [hE] at hg
  exact hg.symm

/-- A realized finite Möbius symmetry preserves the Souriau partition through permutation. -/
theorem mobius_realized_partition_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ) (beta : ℝ)
    (_horbit : RealizesFiniteOrbit M chart σ)
    (_hpotential : ∀ z, potential (M.eval z) = potential z) :
    souriauPartition beta (pullEnergy σ (inducedEnergy potential chart)) =
      souriauPartition beta (inducedEnergy potential chart) :=
  souriauPartition_pullEnergy σ beta (inducedEnergy potential chart)

/-- A realized finite Möbius symmetry preserves the Massieu/log-partition potential. -/
theorem mobius_realized_massieu_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ) (beta : ℝ)
    (_horbit : RealizesFiniteOrbit M chart σ)
    (_hpotential : ∀ z, potential (M.eval z) = potential z) :
    massieuPlanckPotential beta (pullEnergy σ (inducedEnergy potential chart)) =
      massieuPlanckPotential beta (inducedEnergy potential chart) :=
  massieuPlanckPotential_pullEnergy σ beta (inducedEnergy potential chart)

/-- A realized finite Möbius symmetry preserves mean energy. -/
theorem mobius_realized_meanEnergy_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ) (beta : ℝ)
    (_horbit : RealizesFiniteOrbit M chart σ)
    (_hpotential : ∀ z, potential (M.eval z) = potential z) :
    meanEnergy beta (pullEnergy σ (inducedEnergy potential chart)) =
      meanEnergy beta (inducedEnergy potential chart) :=
  meanEnergy_pullEnergy σ beta (inducedEnergy potential chart)

/-- A realized finite Möbius symmetry preserves Boltzmann entropy. -/
theorem mobius_realized_boltzmannEntropy_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ) (beta : ℝ)
    (_horbit : RealizesFiniteOrbit M chart σ)
    (_hpotential : ∀ z, potential (M.eval z) = potential z) :
    boltzmannEntropy
        (gibbsWeight beta (pullEnergy σ (inducedEnergy potential chart))) =
      boltzmannEntropy (gibbsWeight beta (inducedEnergy potential chart)) :=
  boltzmannEntropy_pullEnergy σ beta (inducedEnergy potential chart)

/-- A realized finite Möbius symmetry preserves finite Gibbs free energy. -/
theorem mobius_realized_freeEnergy_invariant [Nonempty ι]
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ) (epsilon : ℝ)
    (_horbit : RealizesFiniteOrbit M chart σ)
    (_hpotential : ∀ z, potential (M.eval z) = potential z) :
    InfoGeometry.Thermo.freeEnergy
        (pullEnergy σ (inducedEnergy potential chart)) epsilon =
      InfoGeometry.Thermo.freeEnergy (inducedEnergy potential chart) epsilon :=
  freeEnergy_pullEnergy σ (inducedEnergy potential chart) epsilon

/--
Closed finite Riemann-sphere chart packet: a chart-realized Möbius symmetry and
an invariant effective potential preserve the induced energy and all finite
Souriau/Gibbs thermodynamic readouts used here.
-/
theorem mobius_realized_thermodynamic_packet [Nonempty ι]
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ) (beta epsilon : ℝ)
    (horbit : RealizesFiniteOrbit M chart σ)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    pullEnergy σ (inducedEnergy potential chart) = inducedEnergy potential chart ∧
      (∀ i, gibbsWeight beta (inducedEnergy potential chart) (σ.symm i) =
        gibbsWeight beta (inducedEnergy potential chart) i) ∧
      souriauPartition beta (pullEnergy σ (inducedEnergy potential chart)) =
        souriauPartition beta (inducedEnergy potential chart) ∧
      massieuPlanckPotential beta (pullEnergy σ (inducedEnergy potential chart)) =
        massieuPlanckPotential beta (inducedEnergy potential chart) ∧
      meanEnergy beta (pullEnergy σ (inducedEnergy potential chart)) =
        meanEnergy beta (inducedEnergy potential chart) ∧
      boltzmannEntropy
          (gibbsWeight beta (pullEnergy σ (inducedEnergy potential chart))) =
        boltzmannEntropy (gibbsWeight beta (inducedEnergy potential chart)) ∧
      InfoGeometry.Thermo.freeEnergy
          (pullEnergy σ (inducedEnergy potential chart)) epsilon =
        InfoGeometry.Thermo.freeEnergy (inducedEnergy potential chart) epsilon := by
  exact ⟨
    mobius_realized_inducedEnergy_invariant M chart σ potential horbit hpotential,
    (fun i => mobius_realized_gibbsWeight_invariant M chart σ potential beta i horbit hpotential),
    mobius_realized_partition_invariant M chart σ potential beta horbit hpotential,
    mobius_realized_massieu_invariant M chart σ potential beta horbit hpotential,
    mobius_realized_meanEnergy_invariant M chart σ potential beta horbit hpotential,
    mobius_realized_boltzmannEntropy_invariant M chart σ potential beta horbit hpotential,
    mobius_realized_freeEnergy_invariant M chart σ potential epsilon horbit hpotential⟩

/-- Möbius symmetry preserves the finite Souriau partition function. -/
theorem mobius_partition_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere)
    (potential : RiemannSphere → ℝ) (beta : ℝ)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    souriauPartition beta (transportedEnergy M potential chart) =
      souriauPartition beta (inducedEnergy potential chart) := by
  rw [transportedEnergy_eq M chart potential hpotential]

/-- Möbius symmetry preserves the finite Massieu potential. -/
theorem mobius_massieu_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere)
    (potential : RiemannSphere → ℝ) (beta : ℝ)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    massieuPlanckPotential beta (transportedEnergy M potential chart) =
      massieuPlanckPotential beta (inducedEnergy potential chart) := by
  rw [transportedEnergy_eq M chart potential hpotential]

/-- Möbius symmetry preserves the transported finite Gibbs law pointwise. -/
theorem mobius_gibbsWeight_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere)
    (potential : RiemannSphere → ℝ) (beta : ℝ) (i : ι)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    gibbsWeight beta (transportedEnergy M potential chart) i =
      gibbsWeight beta (inducedEnergy potential chart) i := by
  rw [transportedEnergy_eq M chart potential hpotential]

/-- Möbius symmetry preserves finite mean energy. -/
theorem mobius_meanEnergy_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere)
    (potential : RiemannSphere → ℝ) (beta : ℝ)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    meanEnergy beta (transportedEnergy M potential chart) =
      meanEnergy beta (inducedEnergy potential chart) := by
  rw [transportedEnergy_eq M chart potential hpotential]

/-- Möbius symmetry preserves the local finite Boltzmann entropy. -/
theorem mobius_boltzmannEntropy_invariant
    (M : MobiusTransform) (chart : ι → RiemannSphere)
    (potential : RiemannSphere → ℝ) (beta : ℝ)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    boltzmannEntropy
        (gibbsWeight beta (transportedEnergy M potential chart)) =
      boltzmannEntropy (gibbsWeight beta (inducedEnergy potential chart)) := by
  rw [transportedEnergy_eq M chart potential hpotential]

/-- Möbius symmetry preserves finite Gibbs free energy. -/
theorem mobius_freeEnergy_invariant [Nonempty ι]
    (M : MobiusTransform) (chart : ι → RiemannSphere)
    (potential : RiemannSphere → ℝ) (epsilon : ℝ)
    (hpotential : ∀ z, potential (M.eval z) = potential z) :
    InfoGeometry.Thermo.freeEnergy
        (transportedEnergy M potential chart) epsilon =
      InfoGeometry.Thermo.freeEnergy (inducedEnergy potential chart) epsilon := by
  rw [transportedEnergy_eq M chart potential hpotential]

/--
Metriplectic readout: entropy production is the metric channel; the Poisson
channel contributes zero by the owner laws of `MetriplecticStructure`.
-/
theorem metriplectic_entropyProduction_metric_channel
    {R : Type*} [CommRing R]
    (M : InfoGeometry.Topology.Metriplectic.MetriplecticStructure R) :
    InfoGeometry.Topology.Metriplectic.totalEvolution M M.S = M.metric M.S M.S :=
  InfoGeometry.Topology.Metriplectic.entropy_evolution M

/-- The conservative Poisson channel annihilates entropy in the metriplectic owner. -/
theorem metriplectic_entropy_poisson_channel_zero
    {R : Type*} [CommRing R]
    (M : InfoGeometry.Topology.Metriplectic.MetriplecticStructure R) :
    M.poisson M.S M.H = 0 :=
  M.poisson_S_left_zero M.H

/--
Combined metriplectic readout: entropy production is exactly the metric channel,
and the reversible Poisson channel contributes zero to entropy.
-/
theorem metriplectic_entropy_channel_packet
    {R : Type*} [CommRing R]
    (M : InfoGeometry.Topology.Metriplectic.MetriplecticStructure R) :
    InfoGeometry.Topology.Metriplectic.totalEvolution M M.S = M.metric M.S M.S ∧
      M.poisson M.S M.H = 0 :=
  ⟨metriplectic_entropyProduction_metric_channel M,
    metriplectic_entropy_poisson_channel_zero M⟩

end

end InfoGeometry.Topology.MobiusSouriauThermodynamicFlow
