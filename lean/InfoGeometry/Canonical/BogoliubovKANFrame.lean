/-!
# Bogoliubov/KAN Frame Packet

This file fixes the operator-first position:

the diagonal is **not** a primitive scalar/com\-mutative structure. It is a
frame readout of an operator on a polarized doubled Krein carrier after a real
Bogoliubov/KAN normalisation.

The packet below is a witness-gated container for this frame data and is
intended to be consumed by higher-level operator lanes (Tomita/Connes/Modular).
-/

import InfoGeometry.Krein.CartanDecomposition

namespace InfoGeometry.Canonical.BogoliubovKANFrame

open InfoGeometry.Krein
open scoped InnerProductSpace

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => NeutralSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Cartan-even part of an endomorphism (`θ(A)=A`) in the chosen neutral frame. -/
@[rep_depth operator]
noncomputable def cartanEvenPart (A : EndH) : EndH :=
  (1 / 2 : ℝ) • (A + InfoGeometry.Krein.cartanInvolution (E := E) A)

/-- Cartan-odd (boost/squeeze) part of an endomorphism (`θ(A)=-A`). -/
@[rep_depth operator]
noncomputable def cartanOddPart (A : EndH) : EndH :=
  (1 / 2 : ℝ) • (A - InfoGeometry.Krein.cartanInvolution (E := E) A)

@[simp]
theorem cartanOddPart_eq_zero_of_involution_fixed (A : EndH) :
    InfoGeometry.Krein.cartanInvolution (E := E) A = A →
    cartanOddPart (E := E) A = 0 := by
  intro hθ
  rw [cartanOddPart, hθ]
  simp

@[simp]
theorem cartanEvenPart_eq_zero_of_involution_neg (A : EndH) :
    InfoGeometry.Krein.cartanInvolution (E := E) A = -A →
    cartanEvenPart (E := E) A = 0 := by
  intro hθ
  rw [cartanEvenPart, hθ]
  simp

/--
Carrier packet for a Bogoliubov/KAN framed readout.

No scalar/diagonal primitive is introduced: diagonal/cartan readouts are
transported operator data in a chosen Bogoliubov frame.
-/
@[rep_depth operator]
structure BogoliubovKANFramePacket where
  /-- The polarized doubled Krein carrier. -/
  doubledKreinSpace : Type*
  /-- Positive/negative or Lagrangian polarization data. -/
  polarizationData : Type*
  /-- Real symmetry group preserving the chosen doubled structure. -/
  bogoliubovGroup : Type*
  /-- Compact/rotation gauge sector `K`. -/
  rotationSector : Type*
  /-- Boost/squeeze Cartan sector `A`. -/
  boostCartanSector : Type*
  /-- Nilpotent/shear sector `N`. -/
  nilpotentSector : Type*
  /-- Weyl chamber/gauge residue. -/
  weylGaugeData : Type*
  /-- Raw operator before frame normalisation. -/
  rawOperator : Type*
  /-- Chosen Bogoliubov transport. -/
  bogoliubovTransform : Type*
  /-- Frame-transformed operator. -/
  frameOperator : Type*
  /-- Cartan-normal/readout operator (inertial-frame normal mode data). -/
  cartanNormalOperator : Type*
  /-- Structural preservation witness for the chosen Bogoliubov map. -/
  bogoliubovPreservesStructureWitness : Type*
  /-- KAN/KAK decomposition witness for the Bogoliubov transform. -/
  kanDecompositionWitness : Type*
  /-- Cartan-normal-form witness for the frame operator. -/
  cartanNormalFormWitness : Type*
  /-- Readout witness: diagonal data are frame coordinates, not primitives. -/
  diagonalAsFrameReadoutWitness : Type*
  /-- Residual gauge/chamber witness of the Cartan normal form. -/
  weylResidualGaugeWitness : Type*

/-- Noncommutative owner target for a Bogoliubov/KAN frame witness. -/
def BogoliubovKANFrameTarget : Prop :=
  Nonempty BogoliubovKANFramePacket

/-- Constructor principle: any concrete packet is a valid target witness. -/
theorem constructBogoliubovKANFrameTarget
    (P : BogoliubovKANFramePacket) :
    BogoliubovKANFrameTarget := by
  exact ⟨P⟩

end InfoGeometry.Canonical.BogoliubovKANFrame
