import InfoGeometry.Streaming.WeakPropertySeparation

/-!
# Pristine finite two-boundary weak-value chain

The public entry point packages three exact facts:

1. a regular pre/post pair defines a native linear functional on operators;
2. every supplied operator balance law is preserved by that functional;
3. an explicit four-coordinate model has zero weak path support and nonzero
   weak signed property in the same supported sector.

No topology, thermofield purification, antiunitary symmetry, or spacetime
current is inferred from these finite algebraic facts.
-/

noncomputable section

namespace InfoGeometry.Streaming.TwoBoundaryWeakPristineChain

open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
open InfoGeometry.Streaming.WeakPropertySeparation

/-- The explicit separation and nonmultiplicativity packet. -/
theorem finite_weak_separation_chain :
    weakValue boundaryPair corridorProjector = 0 ∧
      weakValue boundaryPair corridorSpinZ = 2 ∧
      weakValue boundaryPair (corridorSpinZ * corridorSpinZ) = 0 ∧
      weakValue boundaryPair (corridorSpinZ * corridorSpinZ) ≠
        weakValue boundaryPair corridorSpinZ *
          weakValue boundaryPair corridorSpinZ := by
  exact ⟨corridorProjector_weakValue,
    corridorSpinZ_weakValue,
    corridorSpinZ_square_weakValue,
    weakValue_not_multiplicative⟩

/-- The exact theorem boundary for a future transport model: once an operator
continuity equation is constructed, its weak readout follows functorially from
linearity. -/
theorem operator_continuity_has_weak_readout
    {ι : Type*} [Fintype ι]
    (p : RegularBoundaryPair ι)
    (A₀ A₁ incoming outgoing : Operator ι)
    (hbalance : A₁ - A₀ = incoming - outgoing) :
    weakValue p A₁ - weakValue p A₀ =
      weakValue p incoming - weakValue p outgoing :=
  weakValue_operator_balance p A₀ A₁ incoming outgoing hbalance

/-- Capstone: static weak separation is available now, while a future current
construction can reuse the generic balance theorem rather than postulating a
weak continuity equation. -/
theorem two_boundary_weak_closure_packet :
    WeakPropertySeparation (Fin 4) ∧
      weakValue boundaryPair corridorProjector = 0 ∧
      weakValue boundaryPair corridorSpinZ ≠ 0 ∧
      ¬ (weakValue boundaryPair (corridorSpinZ * corridorSpinZ) =
        weakValue boundaryPair corridorSpinZ *
          weakValue boundaryPair corridorSpinZ) := by
  refine ⟨cheshireWitness, corridorProjector_weakValue, ?_, ?_⟩
  · rw [corridorSpinZ_weakValue]
    norm_num
  · exact weakValue_not_multiplicative

end InfoGeometry.Streaming.TwoBoundaryWeakPristineChain

end noncomputable section
