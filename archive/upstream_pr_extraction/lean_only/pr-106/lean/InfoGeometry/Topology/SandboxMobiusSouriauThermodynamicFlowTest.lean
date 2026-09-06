import InfoGeometry.Topology.MobiusSouriauThermodynamicFlow

open InfoGeometry.Topology.MobiusSouriauThermodynamicFlow

#check pullEnergy
#check souriauPartition_pullEnergy
#check gibbsWeight_pullEnergy
#check meanEnergy_pullEnergy
#check boltzmannEntropy_pullEnergy
#check massieuPlanckPotential_pullEnergy
#check freeEnergy_pullEnergy
#check RealizesFiniteOrbit
#check transportedEnergy
#check transportedEnergy_eq_pullEnergy
#check transportedEnergy_eq
#check inducedEnergy_pullEnergy_eq
#check mobius_realized_inducedEnergy_invariant
#check mobius_realized_gibbsWeight_invariant
#check mobius_realized_partition_invariant
#check mobius_realized_massieu_invariant
#check mobius_realized_meanEnergy_invariant
#check mobius_realized_boltzmannEntropy_invariant
#check mobius_realized_freeEnergy_invariant
#check mobius_realized_thermodynamic_packet
#check mobius_partition_invariant
#check mobius_massieu_invariant
#check mobius_gibbsWeight_invariant
#check mobius_meanEnergy_invariant
#check mobius_boltzmannEntropy_invariant
#check mobius_freeEnergy_invariant
#check metriplectic_entropyProduction_metric_channel
#check metriplectic_entropy_poisson_channel_zero
#check metriplectic_entropy_channel_packet

open InfoGeometry
open InfoGeometry.Physics.SouriauMassieuPlanckFunctional

example {ι : Type*} (σ : Equiv.Perm ι) (energy : ι → ℝ) (i : ι) :
    pullEnergy σ energy i = energy (σ.symm i) := rfl

example {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (beta : ℝ) (energy : ι → ℝ) (i : ι) :
    gibbsWeight beta (pullEnergy σ energy) i =
      gibbsWeight beta energy (σ.symm i) :=
  gibbsWeight_pullEnergy σ beta energy i

example {ι : Type*}
    (M : MobiusTransform) (chart : ι → RiemannSphere) (σ : Equiv.Perm ι)
    (potential : RiemannSphere → ℝ)
    (horbit : RealizesFiniteOrbit M chart σ) :
    transportedEnergy M potential chart =
      pullEnergy σ.symm (inducedEnergy potential chart) :=
  transportedEnergy_eq_pullEnergy M chart σ potential horbit
