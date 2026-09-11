import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge
import InfoGeometry.Physics.QCDZornColorSlotBridge

/-!
# Exceptional/Artin structural bridge for the QCD-facing lane

This file combines two exact repository facts on independent carriers:

* the `G₂/I₂(6)` Artin spin lift and braid preservation of square-zero chiral
  operators;
* preservation of the two Zorn three-vector extraction slots by explicitly
  OP-stabilizing composition maps.

It does **not** identify the Artin group with the QCD gauge group, nor the Zorn
slots with physical color representations.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDExceptionalArtinBridge

open InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge
open InfoGeometry.Physics.QCDZornColorSlotBridge
open InfoGeometry.Exceptional.ArtinOperators
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

/-- Artin spin closure and preservation of square-zero chiral shape. -/
theorem artin_chiral_packet
    (ρ : G2SpinOperatorLift)
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (B : (Module.End ℂ H)ˣ) (Q : Module.End ℂ H)
    (hQ : Q ^ 2 = 0) :
    (ρ.Bs * ρ.Bl) ^ 6 = -1 ∧
      (ρ.Bs * ρ.Bl) ^ 12 = 1 ∧
      ((B : Module.End ℂ H) * Q * (↑B⁻¹ : Module.End ℂ H)) ^ 2 = 0 :=
  ⟨ρ.coxeter_pow_six_eq_neg_one,
    ρ.spin_coxeter_pow_twelve,
    artin_conjugation_preserves_nuclear_nilpotent_shape B Q hQ⟩

/-- Exceptional/Artin data and Zorn slot preservation coexist as exact
structural invariants without identifying their carriers. -/
theorem artin_zorn_slot_packet
    (ρ : G2SpinOperatorLift)
    {R : Type*} [CommRing R]
    (f : ZMat R → ZMat R)
    (hf : IsOPStabilizingCompositionMap f)
    (X : ZMat R) :
    (ρ.Bs * ρ.Bl) ^ 12 = 1 ∧
      f (colorPart X) = colorPart (f X) ∧
      f (anticolorPart X) = anticolorPart (f X) :=
  ⟨ρ.spin_coxeter_pow_twelve,
    (op_stabilizer_preserves_three_vector_slots f hf X).1,
    (op_stabilizer_preserves_three_vector_slots f hf X).2⟩

end InfoGeometry.Physics.QCDExceptionalArtinBridge

end noncomputable section
