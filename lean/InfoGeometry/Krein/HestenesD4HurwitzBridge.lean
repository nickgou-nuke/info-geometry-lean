import InfoGeometry.Krein.HestenesMoebiusClosureBridge
import InfoGeometry.Canonical.DrazinLightConeDictionary
import InfoGeometry.External.Virasoro.VirasoroAlgebra
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# InfoGeometry.Krein.HestenesD4HurwitzBridge

Optional post-seal D4/Hurwitz arithmetic backend for the Hestenes--Krein stack.

This file is deliberately not a prerequisite for the already sealed
Hestenes--Krein / Connes--Wilson / Möbius pipeline.  It also does not construct
the D4 root lattice, Hurwitz units, triality, self-duality, or affine
Kac--Moody representation theory from scratch.

Instead it exposes a theorem-safe arithmetic socket:

* the 24 candidate Hurwitz/D4 roots are identified with the finite
  Wigner--Jones atom layer already carried by `StandardFormOmegaVolumeBridge`;
* D4/Hurwitz, self-duality, triality, and affine Kac--Moody facts are explicit
  backend certificates;
* the affine null-root sockets are calibrated to the existing Drazin
  `ProjectorSplit.uPlus/uMinus` arrows;
* same-arrow null-root nilpotence is inherited from `ProjectorSplit`;
* Virasoro centrality is read from the existing `VirasoroAlgebra.cgen_bracket`.
-/

namespace InfoGeometry.Krein.HestenesD4HurwitzBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesMoebiusClosureBridge
open InfoGeometry.Canonical.DrazinLightConeDictionary
open VirasoroProject

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance d4HurwitzNormedRing : NormedRing EndH := inferInstance
noncomputable local instance d4HurwitzNormedAlgebra : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance d4HurwitzNormedAlgebraRat : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance d4HurwitzTopologicalRing : IsTopologicalRing EndH := inferInstance
local instance d4HurwitzCompleteSpace : CompleteSpace EndH := inferInstance
local instance d4HurwitzSMulCommClass : SMulCommClass ℝ EndH EndH := inferInstance
local instance d4HurwitzIsScalarTower : IsScalarTower ℝ EndH EndH := inferInstance

/--
Generic D4 lattice / Hurwitz / affine Kac--Moody certificate carrier.

This is the theorem-safe version of the arithmetic-crystal layer.  It records
the 24 candidate roots, a discrete symmetry carrier acting on their indices,
and backend certificates for the nontrivial arithmetic facts.

No construction of the Hurwitz maximal order, D4 self-duality, triality, or
affine Kac--Moody representation theory is asserted here.
-/
@[rep_depth projective]
structure D4LatticeKacMoodyBridge
    (Op Automorphism : Type*) [Ring Op] [Algebra ℝ Op] [Group Automorphism] where
  /-- The 24 candidate D4/Hurwitz roots. -/
  hurwitzRoots : Fin 24 → Op

  /-- Discrete Möbius/quaternionic symmetry action on the root labels. -/
  discreteMoebiusAction : Automorphism → Equiv.Perm (Fin 24)

  /-- Backend certificate: the 24 roots form the intended D4/Hurwitz root system. -/
  d4_hurwitz_root_system : Prop

  /-- Evidence for the D4/Hurwitz root-system certificate. -/
  d4_hurwitz_root_system_holds : d4_hurwitz_root_system

  /-- Backend certificate: the Hurwitz order is maximal/arithmetic-closed. -/
  hurwitz_maximal_order : Prop

  /-- Evidence for the maximal-order certificate. -/
  hurwitz_maximal_order_holds : hurwitz_maximal_order

  /-- Backend certificate: the D4 lattice is self-dual in the chosen readout. -/
  d4_self_dual_lattice : Prop

  /-- Evidence for the self-duality certificate. -/
  d4_self_dual_lattice_holds : d4_self_dual_lattice


  /-- Triality action on the three outer nodes of the D4 diagram. -/
  triality_action : Automorphism → Equiv.Perm (Fin 3)

  /-- Triality has order dividing three for every installed symmetry element. -/
  triality_holds : ∀ g : Automorphism, triality_action g ^ 3 = 1

  /-- Backend certificate: affine Kac--Moody closure is installed. -/
  affine_kac_moody_closure : Prop

  /-- Evidence for affine Kac--Moody closure. -/
  affine_kac_moody_closure_holds : affine_kac_moody_closure

  /-- Calibrated affine/Virasoro central charge. -/
  affine_central_charge : ℝ

  /-- Modular discriminant / Dedekind readout supplied by the arithmetic backend. -/
  modular_discriminant_readout : ℝ
  /-- The affine central charge is calibrated to the modular discriminant.
  Di Francesco, Mathieu, Senechal (1997), Conformal Field Theory, §10.4. -/
  central_charge_calibrated : affine_central_charge = modular_discriminant_readout

namespace D4LatticeKacMoodyBridge

variable {Op Automorphism : Type*}
variable [Ring Op] [Algebra ℝ Op] [Group Automorphism]
variable (B : D4LatticeKacMoodyBridge Op Automorphism)

/-- Readback: the supplied roots carry the intended D4/Hurwitz root-system certificate. -/
@[rep_depth projective]
theorem d4_hurwitz_root_system_readback :
    B.d4_hurwitz_root_system :=
  B.d4_hurwitz_root_system_holds

/-- Readback: the Hurwitz maximal-order/arithmetic-closure certificate is available. -/
@[rep_depth projective]
theorem hurwitz_maximal_order_readback :
    B.hurwitz_maximal_order :=
  B.hurwitz_maximal_order_holds

/-- Readback: D4 self-duality is supplied by the arithmetic backend. -/
@[rep_depth projective]
theorem d4_self_dual_in_krein :
    B.d4_self_dual_lattice :=
  B.d4_self_dual_lattice_holds

/-- Readback: triality is supplied by the arithmetic backend. -/
@[rep_depth projective]
theorem triality_readback :
    ∀ g : Automorphism, B.triality_action g ^ 3 = 1 :=
  B.triality_holds

/-- Readback: affine Kac--Moody closure is supplied by the arithmetic backend. -/
@[rep_depth projective]
theorem affine_kac_moody_closure_readback :
    B.affine_kac_moody_closure :=
  B.affine_kac_moody_closure_holds

/-- Readback: the affine central charge is calibrated by the modular-discriminant readout. -/
@[rep_depth projective]
theorem affine_central_charge_calibrated :
    B.affine_central_charge = B.modular_discriminant_readout :=
  B.central_charge_calibrated

end D4LatticeKacMoodyBridge

/--
D4/Hurwitz arithmetic calibration over the sealed Möbius/Connes layer.

The finite word layer is fixed to `Fin 24`; concrete arithmetic backends may
interpret it as the 24 Hurwitz units / D4 root atoms.  This bridge only records
that interpretation as certificates and proves the consequences that follow
from the already-owned atom partition and projector-arrow API.
-/
@[rep_depth krein]
structure D4HurwitzArithmeticBridge where
  /-- Sealed Möbius/Connes/Wilson bridge over a 24-atom layer. -/
  moebius :
    _root_.InfoGeometry.Krein.HestenesMoebiusClosureBridge.Bridge (E := E) (Fin 24)

  /-- Generic Drazin projector split used for affine null-root arrows. -/
  drazinSplit : ProjectorSplit EndH

  /-- Candidate Hurwitz/D4 root atom as a bounded operator. -/
  hurwitzRoot : Fin 24 → EndH

  /-- The Hurwitz/D4 roots are the existing Wigner--Jones atoms. -/
  root_eq_wignerJonesAtom :
    ∀ i : Fin 24, hurwitzRoot i = moebius.wilson.volume.wignerJonesAtom i

  /-- Affine null-root `+` socket. -/
  affineNullRootPlus : EndH → EndH

  /-- Affine null-root `-` socket. -/
  affineNullRootMinus : EndH → EndH

  /-- Calibration of the positive affine null-root socket to `uPlus`. -/
  affineNullRootPlus_eq_uPlus :
    ∀ A : EndH, affineNullRootPlus A = drazinSplit.uPlus A

  /-- Calibration of the negative affine null-root socket to `uMinus`. -/
  affineNullRootMinus_eq_uMinus :
    ∀ A : EndH, affineNullRootMinus A = drazinSplit.uMinus A


  /-- Triality action on the three outer nodes of the D4 diagram. -/
  trialityAction : MoebiusParameter → Equiv.Perm (Fin 3)

  /-- Triality has order dividing three for every Möbius parameter. -/
  triality_holds : ∀ g : MoebiusParameter, trialityAction g ^ 3 = 1


  /-- Calibrated affine central charge. -/
  affineCentralCharge : ℝ

  /-- Expected central charge supplied by the arithmetic backend. -/
  expectedAffineCentralCharge : ℝ
  /-- The calibrated central charge equals the expected readout.
  Di Francesco, Mathieu, Senechal (1997), Conformal Field Theory, §10.4. -/
  central_charge_calibrated : affineCentralCharge = expectedAffineCentralCharge

namespace D4HurwitzArithmeticBridge

variable (B : D4HurwitzArithmeticBridge (E := E))

/-- The supplied triality certificate is available. -/
@[rep_depth projective]
theorem triality_readback :
    ∀ g : MoebiusParameter, B.trialityAction g ^ 3 = 1 :=
  B.triality_holds

/-- Readback of the affine central-charge calibration. -/
@[rep_depth projective]
theorem affineCentralCharge_calibrated :
    B.affineCentralCharge = B.expectedAffineCentralCharge :=
  B.central_charge_calibrated

/-- The Hurwitz root expectation is the existing atom expectation. -/
@[rep_depth projective]
theorem root_atomExpectation_eq (i : Fin 24) :
    B.moebius.wilson.volume.volumeState (B.hurwitzRoot i) =
      B.moebius.wilson.volume.atomExpectation i := by
  rw [B.root_eq_wignerJonesAtom i]
  rfl

/-- The 24 Hurwitz/D4 root expectations have total normalized Ω-volume one. -/
@[rep_depth projective]
theorem total_hurwitz_root_expectation_is_unity :
    (∑ i : Fin 24, B.moebius.wilson.volume.volumeState (B.hurwitzRoot i)) = 1 := by
  calc
    (∑ i : Fin 24, B.moebius.wilson.volume.volumeState (B.hurwitzRoot i))
        = ∑ i : Fin 24, B.moebius.wilson.volume.atomExpectation i := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact B.root_atomExpectation_eq i
    _ = 1 := B.moebius.wilson.volume.total_expectation_is_unity

/-- Hurwitz/D4 root expectations are invariant under the installed Möbius action. -/
@[rep_depth projective]
theorem hurwitzRoot_expectation_moebius_invariant
    (g : MoebiusParameter) (i : Fin 24) :
    B.moebius.wilson.volume.atomExpectation ((B.moebius.wordAction g) i) =
      B.moebius.wilson.volume.atomExpectation i :=
  B.moebius.atomExpectation_moebius_invariant g i

/-- Positive affine null-root socket readback to `uPlus`. -/
@[rep_depth operator]
theorem affineNullRootPlus_eq_uPlus_readback (A : EndH) :
    B.affineNullRootPlus A = B.drazinSplit.uPlus A :=
  B.affineNullRootPlus_eq_uPlus A

/-- Negative affine null-root socket readback to `uMinus`. -/
@[rep_depth operator]
theorem affineNullRootMinus_eq_uMinus_readback (A : EndH) :
    B.affineNullRootMinus A = B.drazinSplit.uMinus A :=
  B.affineNullRootMinus_eq_uMinus A

/-- Same-arrow nilpotence for the positive affine null-root socket. -/
@[rep_depth operator]
theorem affineNullRootPlus_mul_affineNullRootPlus_eq_zero (A C : EndH) :
    B.affineNullRootPlus A * B.affineNullRootPlus C = 0 := by
  rw [B.affineNullRootPlus_eq_uPlus_readback A,
    B.affineNullRootPlus_eq_uPlus_readback C]
  exact B.drazinSplit.uPlus_mul_uPlus_eq_zero A C

/-- Same-arrow nilpotence for the negative affine null-root socket. -/
@[rep_depth operator]
theorem affineNullRootMinus_mul_affineNullRootMinus_eq_zero (A C : EndH) :
    B.affineNullRootMinus A * B.affineNullRootMinus C = 0 := by
  rw [B.affineNullRootMinus_eq_uMinus_readback A,
    B.affineNullRootMinus_eq_uMinus_readback C]
  exact B.drazinSplit.uMinus_mul_uMinus_eq_zero A C

/-- Existing Virasoro central generator brackets trivially with every Virasoro element. -/
@[rep_depth projective]
theorem virasoro_central_bracket_zero (Z : VirasoroAlgebra ℝ) :
    ⁅VirasoroAlgebra.cgen ℝ, Z⁆ = 0 :=
  VirasoroAlgebra.cgen_bracket (𝕜 := ℝ) Z

end D4HurwitzArithmeticBridge

end Core

end InfoGeometry.Krein.HestenesD4HurwitzBridge

end
