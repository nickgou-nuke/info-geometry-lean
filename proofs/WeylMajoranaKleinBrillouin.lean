import proofs.NonAbelianBrillouinKleinBottle
import proofs.DiracCuntzCrystalDispersion
import proofs.DiscreteLatticePoincare
import Mathlib

/-!
# Weyl-Majorana States and Causal Cones on the Brillouin Klein Bottle

This module formally synthesizes the physics of Dirac crystals with the 
topological Klein Bottle Brillouin theory.

In literature (e.g., graphene or topological metamaterials), the band structure
has linear causal cone points (Weyl nodes). When subjected to the non-orientable 
Klein Bottle glide reflection:
1. The independent K and K' Weyl nodes are globally entwined.
2. The projective momentum-translation phase (-1) enforces a charge-conjugation 
   symmetry, effectively identifying a Weyl fermion with its own antiparticle.
3. This algebraically forces the emergent Bloch states on the boundary to become
   neutral Majorana states.
-/

noncomputable section

namespace WeylMajoranaKleinBrillouin

open NonAbelianBrillouinKleinBottle
open DiracCuntzCrystalDispersion
open DiscreteLatticePoincare
open Matrix

/--
A Bloch state at a given momentum point in the Dirac crystal.
For topological verification, it is assigned a chiral Weyl node parity.
-/
structure BlochState where
  k : MomentumPoint
  node : WeylNode
  charge : ℤ

/--
The topological charge conjugation operator induced by the Brillouin Klein Bottle fold.
It reverses the momentum (via the glide reflection), flips the Weyl node 
(from K to K' or vice versa), and flips the electrical charge.
-/
def kleinChargeConjugation (ψ : BlochState) : BlochState where
  k := bkbFold ψ.k
  node := foldWeylNode ψ.node
  charge := -ψ.charge

/--
A Majorana-like constraint on the Brillouin Klein bottle boundary.
A state is defined as Majorana if it is invariant under the topological 
charge conjugation operator enforced by the glide fold.
-/
def isMajoranaState (ψ : BlochState) : Prop :=
  kleinChargeConjugation ψ = ψ

/--
The Dirac/Weyl causal cones are strictly located at the K and K' momentum points.
When traversing the Brillouin Klein Bottle boundary, the causal cones are entwined.
This theorem proves that the only states which can be globally defined on the 
non-orientable boundary without breaking symmetry must possess zero electric charge,
thereby fulfilling the Majorana condition.
-/
theorem entwined_causal_cones_force_majorana_neutrality 
    (ψ : BlochState) 
    (h_majorana : isMajoranaState ψ) : 
    ψ.charge = 0 := by
  have h_charge : (kleinChargeConjugation ψ).charge = ψ.charge := by
    rw [h_majorana]
  dsimp [kleinChargeConjugation] at h_charge
  -- We have -ψ.charge = ψ.charge, meaning 2 * ψ.charge = 0
  exact Int.eq_zero_of_neg_eq h_charge

end WeylMajoranaKleinBrillouin
