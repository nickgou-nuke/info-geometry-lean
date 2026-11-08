import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain

/-!
# Native SU(3) color-spinor representation bridge

The repository already owns an infinitesimal matrix action on
`ColorSpinor4 V = (Fin 3 → V) × V`: the first three components transform by
matrix multiplication and the fourth component is a singlet.  This module
exposes that representation in the QCD structural lane.

This is an algebraic representation theorem on a generic complex module.  It
is not yet an action on the real `Cl(5,5)` Furey span and is not identified
with the physical QCD quark representation.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDSU3ColorSpinorBridge

open InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
open InfoGeometry.Physics.GellMannSU3

/-- Matrix multiplication is represented by composition on the triplet-plus-
singlet color-spinor carrier, and matrix commutators are represented by action
commutators. -/
theorem color_spinor_representation_packet
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : M3C) (ψ : ColorSpinor4 V) :
    colorLieAction4 (A * B) ψ =
        colorLieAction4 A (colorLieAction4 B ψ) ∧
    colorLieAction4 (A * B - B * A) ψ =
        colorLieAction4 A (colorLieAction4 B ψ) -
          colorLieAction4 B (colorLieAction4 A ψ) :=
  ⟨colorLieAction4_mul A B ψ, colorLieAction4_commutator A B ψ⟩

/-- The concrete Gell-Mann relation `[λ₁, λ₂] = 2 i λ₃` is represented on every
triplet-plus-singlet color spinor. -/
theorem gellMann_color_spinor_commutator
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((2 * Complex.I) • gl3) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl2 ψ) -
        colorLieAction4 gl2 (colorLieAction4 gl1 ψ) :=
  colorAction_gl1_gl2_commutator ψ

/-- The Cartan pair `λ₃, λ₈` acts by commuting infinitesimal transformations. -/
theorem gellMann_color_spinor_cartan_commutes
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 gl3 (colorLieAction4 gl8 ψ) =
      colorLieAction4 gl8 (colorLieAction4 gl3 ψ) :=
  colorAction_gl3_gl8_commute ψ

end InfoGeometry.Physics.QCDSU3ColorSpinorBridge

end noncomputable section
