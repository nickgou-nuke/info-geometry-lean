import InfoGeometry.Canonical.GrandSynthesisThermo
import InfoGeometry.Canonical.GrandSynthesisGeometry
import InfoGeometry.Canonical.GrandSynthesisBott
import InfoGeometry.Canonical.GrandSynthesisSingular

/-!
# The Grand Unification of the Physics of Information in Lean 4

Umbrella facade re-exporting the owned GrandSynthesis theorem families.
The actual mathematics now lives in lower owner files split by lane.
-/

namespace GrandSynthesis

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.RicciMongeAmpere

section CanopyAssembly

variable (n : Nat)

/--
Thermodynamic canopy package: a doubly-stochastic Sinkhorn branch carrying the
thermodynamic and entropy monotonicity legs.
-/
structure ThermoCanopyPackage where
  trajectory : DoublyStochasticSinkhornTrajectory n

/--
Thermodynamic canopy closure: one package discharges both equilibrium and
RN-entropy monotonicity branches.
-/
theorem canopy_thermo_equilibrium_and_entropy
    (P : ThermoCanopyPackage n) :
    ThermodynamicEquilibrium n P.trajectory ∧
      SinkhornEntropyMonotoneRN n P.trajectory.traj := by
  refine ⟨?_, ?_⟩
  · exact thermodynamicEquilibrium_of_doublyStochastic (n := n) P.trajectory
  · exact doublyStochastic_sinkhornEntropyMonotoneRN (n := n) P.trajectory

variable {X : Type*}

/--
Geometric canopy closure: Ricci fixed-point flow gives constant component
readout along any differentiable component.
-/
theorem canopy_geometric_component_constant
    (flow : RicciFlow X) (u v : X)
    (hDiff : Differentiable ℝ (fun s => flow s u v))
    (hGeo : IsRicciFixedPoint flow) :
    ∃ c : ℝ, ∀ s, flow s u v = c := by
  exact ricci_component_constant_of_geometricEquilibrium
    (flow := flow) (u := u) (v := v) hDiff hGeo

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Singular boundary canopy closure: boundary-generator vanishing implies regular
radial transport closure.
-/
theorem canopy_singular_boundary_closure
    (S : SingularTransportSystem E)
    (hZero : S.boundary.boundaryGenerator = 0) :
    S.boundary.regularRadialTransportCloses := by
  exact regularRadialTransportCloses_of_boundaryGenerator_eq_zero (S := S) hZero

/--
Trunk-to-canopy closure packet for the GrandSynthesis canopy:
thermodynamic, geometric, and singular branches are discharged together.
-/
theorem grandSynthesis_trunk_to_canopy_closure
    (P : ThermoCanopyPackage n)
    {X : Type*}
    (flow : RicciFlow X) (u v : X)
    (hDiff : Differentiable ℝ (fun s => flow s u v))
    (hGeo : IsRicciFixedPoint flow)
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : SingularTransportSystem E)
    (hZero : S.boundary.boundaryGenerator = 0) :
    ThermodynamicEquilibrium n P.trajectory ∧
      SinkhornEntropyMonotoneRN n P.trajectory.traj ∧
      (∃ c : ℝ, ∀ s, flow s u v = c) ∧
      S.boundary.regularRadialTransportCloses := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (canopy_thermo_equilibrium_and_entropy (n := n) P).1
  · exact (canopy_thermo_equilibrium_and_entropy (n := n) P).2
  · exact canopy_geometric_component_constant flow u v hDiff hGeo
  · exact canopy_singular_boundary_closure (S := S) hZero

/--
Root-factorization packet for the GrandSynthesis canopy:
the combined closure decomposes into existential geometric component plus
thermodynamic/singular witnesses.
-/
theorem grandSynthesis_root_factorization
    (P : ThermoCanopyPackage n)
    {X : Type*}
    (flow : RicciFlow X) (u v : X)
    (hDiff : Differentiable ℝ (fun s => flow s u v))
    (hGeo : IsRicciFixedPoint flow)
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : SingularTransportSystem E)
    (hZero : S.boundary.boundaryGenerator = 0) :
    ∃ c : ℝ,
      ThermodynamicEquilibrium n P.trajectory ∧
      SinkhornEntropyMonotoneRN n P.trajectory.traj ∧
      (∀ s, flow s u v = c) ∧
      S.boundary.regularRadialTransportCloses := by
  obtain ⟨c, hc⟩ := canopy_geometric_component_constant flow u v hDiff hGeo
  refine ⟨c, ?_⟩
  refine ⟨?_, ?_, hc, ?_⟩
  · exact (canopy_thermo_equilibrium_and_entropy (n := n) P).1
  · exact (canopy_thermo_equilibrium_and_entropy (n := n) P).2
  · exact canopy_singular_boundary_closure (S := S) hZero

end CanopyAssembly

end GrandSynthesis
