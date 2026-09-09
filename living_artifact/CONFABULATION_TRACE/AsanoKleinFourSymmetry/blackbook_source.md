# BlackBookSource: Asano-Klein Four Symmetry

## Symbolic Origin
The Asano contraction argument for Lee-Yang circle theorem, reduced to a finite V₄ (Klein-four) group action on the complex fugacity plane. The V₄ = {id, inv, conj, cpt} where:
- inv: z ↦ z⁻¹ (inversion)
- conj: z ↦ z̄ (complex conjugation)
- cpt: z ↦ z̄⁻¹ (CPT = inversion ∘ conjugation)

The Lee-Yang circle is the unit circle |z| = 1 in the complex fugacity plane.

## Symbolic Pressure
The Asano-Ruelle contraction theorem (Ruelle A.1) establishes that for a multi-affine polynomial P(z₁, z₂) = A + Bz₁ + Cz₂ + Dz₁z₂ non-vanishing on the open unit disk, the contraction (P ⊛)(z) = A + Dz has zeros on the boundary if and only if the original polynomial has zeros in the product space.

The topological endpoint proof (AsanoRuelleTopologicalEndpoint.lean) forces the pole -C/D into the forbidden set K₁ under boundedness/non-degeneracy conditions.

The V₄ symmetry provides a finite reduction: the global analytic covering argument reduces to checking endpoint representatives in the V₄ orbit.

## Motif
**Geometric inversion as finite symmetry reduction.** The Möbius transformation z ↦ z⁻¹ (inversion) and z ↦ z̄ (conjugation) generate a Klein-four group that preserves the Lee-Yang circle. This finite symmetry collapses the global analytic problem to a finite orbit check.

## Structural Tension
The global analytic Asano theorem (non-degenerate branch) remains a socket debt. The finite V₄ action is proved, but the global covering argument requires the analytic statement that the Lee-Yang circle is the zero-locus boundary for the renormalized partition function.

## Bridge Target
Thermodynamics/AsanoKleinFourSymmetry.lean: `AsanoCompactificationWitness` socket — packages the finite V₄ symmetry content that a concrete prime/Majorana system must supply.