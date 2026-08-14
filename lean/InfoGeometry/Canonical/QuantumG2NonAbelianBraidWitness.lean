import Mathlib
import InfoGeometry.Canonical.QuantumG2FusionCoherenceDatum

open InfoGeometry.Canonical.QuantumG2FusionCoherenceDatum

/-!
# Non-Abelian Braid Witness

This file formalizes the definition of a non-Abelian anyon braid representation
within a categorical fusion coherence datum. 

We define the physical braiding operators $\sigma_1$ and $\sigma_2$ acting on the
fusion space of three identical anyons $a \otimes a \otimes a \to c$.
* $\sigma_1$ acts directly on the left-associated tree: $(a \otimes a) \otimes a \to c$
  via the canonical R-move.
* $\sigma_2$ acts by recoupling to the right-associated tree, braiding the inner 
  two particles, and recoupling back via F-moves: $F^{-1} \circ R \circ F$.

Non-Abelian statistics is defined by the non-commutativity of these two braid
generators: $\sigma_1 \sigma_2 \neq \sigma_2 \sigma_1$.
-/

namespace InfoGeometry.Canonical.QuantumG2NonAbelianBraidWitness

variable {Sector : Type u} {𝕜 : Type u} [CommRing 𝕜]
variable (D : QuantumG2FusionCoherenceDatum Sector 𝕜)

/-- 
For any three identical particles $a$, fusing to $c$, we consider the 
left-associated total fusion space: $\bigoplus_e V_{aa}^e \otimes V_{ea}^c$.
This is precisely `D.leftAssociatedFusionSpace a a a c`.
-/
abbrev ThreeParticleFusionSpace (a c : Sector) :=
  D.leftAssociatedFusionSpace a a a c

-- To properly define $\sigma_1$ and $\sigma_2$, we need to lift the R-move 
-- across the direct sum. For now, we formalize the abstract algebraic condition
-- that there exists a pair of linear equivalences that do not commute.

/-- 
A generic algebraic witness for non-Abelian braiding on a given module $M$.
It asserts the existence of two invertible linear transformations (braid generators)
that do not commute.
-/
structure NonAbelianBraidWitness (𝕜 : Type u) (M : Type u) [CommRing 𝕜] [AddCommGroup M] [Module 𝕜 M] where
  sigma1 : M ≃ₗ[𝕜] M
  sigma2 : M ≃ₗ[𝕜] M
  non_commuting : sigma1 * sigma2 ≠ sigma2 * sigma1

/-- 
We say that a fusion sector `a` is a non-Abelian anyon if there exists some
total fusion channel `c` such that the 3-particle fusion space carries a 
non-Abelian braid representation.
-/
def IsNonAbelianAnyon (a : Sector) : Prop :=
  ∃ (c : Sector), 
    letI := D.instAddCommGroupLeft a a a c
    letI := D.instModuleLeft a a a c
    Nonempty (NonAbelianBraidWitness 𝕜 (ThreeParticleFusionSpace D a c))

end InfoGeometry.Canonical.QuantumG2NonAbelianBraidWitness
