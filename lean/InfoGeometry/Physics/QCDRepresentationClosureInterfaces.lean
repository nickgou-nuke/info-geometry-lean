import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.QCDSU3ColorSpinorBridge

/-!
# Typed representation-closure interfaces for the QCD structural lane

The main library already owns a genuine infinitesimal matrix representation on
`ColorSpinor4 V`.  The remaining representation-theoretic gap is not another
commutator identity: it is an explicit intertwiner from that carrier to a
second carrier such as a complexified Clifford/Furey module.

This file makes that gap type-safe without postulating a particular target.
It does not construct an intertwiner into `fureyGeneration` and therefore does
not close the physical or Clifford representation debt by itself.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDRepresentationClosureInterfaces

open InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain

/-- Proof-carrying intertwiner between the native triplet-plus-singlet color
representation and an arbitrary complex target representation. -/
structure ColorRepresentationIntertwiner
    (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] where
  targetAction : M3C → W →ₗ[ℂ] W
  map : ColorSpinor4 V →ₗ[ℂ] W
  intertwines : ∀ (A : M3C) (ψ : ColorSpinor4 V),
    map (colorLieAction4 A ψ) = targetAction A (map ψ)

namespace ColorRepresentationIntertwiner

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- The intertwiner transports a represented matrix commutator to the target
carrier.  No assumption that the target action is itself a representation is
needed: this identity follows by transporting the already-proved source
commutator action. -/
theorem map_commutator
    (I : ColorRepresentationIntertwiner V W)
    (A B : M3C) (ψ : ColorSpinor4 V) :
    I.map (colorLieAction4 (A * B - B * A) ψ) =
      I.targetAction A (I.targetAction B (I.map ψ)) -
        I.targetAction B (I.targetAction A (I.map ψ)) := by
  rw [colorLieAction4_commutator]
  simp only [LinearMap.map_sub]
  rw [I.intertwines, I.intertwines, I.intertwines, I.intertwines]

/-- If the intertwiner is injective, equality of target actions on mapped
states reflects back to equality on the source color-spinor representation. -/
theorem reflect_action_eq
    (I : ColorRepresentationIntertwiner V W)
    (hinj : Function.Injective I.map)
    (A B : M3C) (ψ : ColorSpinor4 V)
    (h : I.targetAction A (I.map ψ) = I.targetAction B (I.map ψ)) :
    colorLieAction4 A ψ = colorLieAction4 B ψ := by
  apply hinj
  rw [I.intertwines, I.intertwines]
  exact h

end ColorRepresentationIntertwiner

end InfoGeometry.Physics.QCDRepresentationClosureInterfaces

end noncomputable section
