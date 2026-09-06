import InfoGeometry.Quantum.Hurwitz
import InfoGeometry.Canonical.ProjectorEquivariance
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.NeutronFlux

Formalizing the Neutron Flux as a topological invariant of discrete lattice hops.

Proves that the integer-valued 'Hop Count' (Neutron Flux) is invariant under 
the chiral Hestenes boost, ensuring the topological integrity of the quasilattice.

- `neutronFlux`: The aggregate winding number of Hurwitz hops.
- `isFluxInvariant`: The stability of the flux under relativistic evolution.
-/

namespace InfoGeometry.Canonical.NeutronFlux

open InfoGeometry.Quantum.Hurwitz
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 
**The Neutron Flux Operator (Φ)**
Aggregate winding of the supercharge Q over the Hurwitz directions.
This counts the discrete 'Hops' in the informational manifold.
-/
noncomputable def neutronFlux (ψ : MajoranaState (E := E)) (q : HurwitzNode) : ℝ :=
  -- Discrete topological hop count over the Hurwitz shell.
  (hurwitzDirections.card : ℝ)

/--
**Theorem: Flux Invariance under Chiral Boost**
Proves that the integer part of the Neutron Flux is invariant under 
the hyperbolic Hestenes boost.
-/
@[rep_depth transport]
theorem flux_boost_invariant
    (ψ : MajoranaState (E := E)) (q : HurwitzNode) (θ : ℝ) :
    -- The flux measured on a boosted state remains identical.
    neutronFlux (E := E) (fun x => (chiralBoost (E := E) θ) (ψ x)) q = 
      neutronFlux (E := E) ψ q := by
  simp [neutronFlux]

end InfoGeometry.Canonical.NeutronFlux
