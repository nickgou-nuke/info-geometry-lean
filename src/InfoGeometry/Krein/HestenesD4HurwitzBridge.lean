import InfoGeometry.Krein.HestenesMoebiusClosureBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DrazinLightConeDictionary
import InfoGeometry.External.Virasoro.VirasoroAlgebra
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
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
* triality is an explicit permutation relation;
* the affine null-root sockets are calibrated to the existing Drazin
  `ProjectorSplit.uPlus/uMinus` arrows;
* same-arrow null-root nilpotence is inherited from `ProjectorSplit`;
* Virasoro centrality is read from the existing `VirasoroAlgebra.cgen_bracket`.

A D4 root-system theorem requires a root pairing, a Hurwitz maximal-order
theorem requires an explicit order, self-duality requires a lattice and dual,
and affine Kac--Moody closure requires current modes and their bracket.  Those
objects are not replaced here by proposition-valued markers.
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
Finite root-family, triality, and central-charge calibration carrier.

It records 24 candidate roots and discrete symmetry actions on their indices.
The name reflects the intended future realization, but this finite socket does
not assert the absent D4 lattice, Hurwitz order, or affine current algebra.

No construction of the Hurwitz maximal order, D4 self-duality, or affine
Kac--Moody representation theory is asserted here.
-/
@[rep_depth projective]
structure D4LatticeKacMoodyBridge
    (Op Automorphism : Type*) [Ring Op] [Algebra ℝ Op] [Group Automorphism] where
  /-- The 24 candidate D4/Hurwitz roots. -/
  hurwitzRoots : Fin 24 → Op

  /-- Bilinear root-pairing readout used to state the D4 Cartan law. -/
  rootPairing : Op → Op → ℝ

  /-- Four selected simple-root labels inside the 24-root family. -/
  simpleRootLabel : Fin 4 → Fin 24

  /-- The D4 Cartan matrix realized by the selected simple roots. -/
  d4CartanMatrix : Matrix (Fin 4) (Fin 4) ℝ

  /-- Root pairings agree with the supplied D4 Cartan matrix. -/
  rootPairing_eq_cartan :
    ∀ i j,
      rootPairing (hurwitzRoots (simpleRootLabel i))
        (hurwitzRoots (simpleRootLabel j)) = d4CartanMatrix i j

  /-- Explicit Hurwitz-order carrier inside the operator algebra. -/
  hurwitzOrder : Subring Op

  /-- Every selected root belongs to the installed Hurwitz order. -/
  roots_mem_hurwitzOrder : ∀ i, hurwitzRoots i ∈ hurwitzOrder

  /--
  Maximality of the installed Hurwitz order among proper subrings of the
  ambient operator ring: an over-order is either unchanged or the full ring.
  -/
  hurwitzOrder_maximal :
    ∀ O : Subring Op, hurwitzOrder ≤ O → O = hurwitzOrder ∨ O = ⊤

  /-- Additive lattice generated/selected inside the Hurwitz order. -/
  rootLattice : AddSubgroup Op

  /-- Every selected root belongs to the lattice. -/
  roots_mem_rootLattice : ∀ i, hurwitzRoots i ∈ rootLattice

  /--
  Integral dual-lattice characterization.  This is the actual self-duality
  obligation for the supplied pairing, not a Boolean or proposition token.
  -/
  rootLattice_selfDual :
    ∀ x : Op,
      x ∈ rootLattice ↔
        ∀ y ∈ rootLattice, ∃ z : ℤ, rootPairing x y = z

  /-- Discrete Möbius/quaternionic symmetry action on the root labels. -/
  discreteMoebiusAction : Automorphism → Equiv.Perm (Fin 24)

  /-- Triality action on the three outer nodes of the D4 diagram. -/
  triality_action : Automorphism → Equiv.Perm (Fin 3)

  /-- Triality has order dividing three for every installed symmetry element. -/
  triality_holds : ∀ g : Automorphism, triality_action g ^ 3 = 1

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

/-- Readback: triality is supplied by the arithmetic backend. -/
@[rep_depth projective]
theorem triality_readback :
    ∀ g : Automorphism, B.triality_action g ^ 3 = 1 :=
  B.triality_holds

/-- Readback: the affine central charge is calibrated by the modular-discriminant readout. -/
@[rep_depth projective]
theorem affine_central_charge_calibrated :
    B.affine_central_charge = B.modular_discriminant_readout :=
  B.central_charge_calibrated

/-- The selected simple roots realize the installed D4 Cartan matrix. -/
@[rep_depth projective]
theorem simpleRoot_pairing_eq_cartan (i j : Fin 4) :
    B.rootPairing (B.hurwitzRoots (B.simpleRootLabel i))
        (B.hurwitzRoots (B.simpleRootLabel j)) =
      B.d4CartanMatrix i j :=
  B.rootPairing_eq_cartan i j

/-- Every candidate root is an element of the explicit Hurwitz order. -/
@[rep_depth projective]
theorem root_mem_hurwitzOrder (i : Fin 24) :
    B.hurwitzRoots i ∈ B.hurwitzOrder :=
  B.roots_mem_hurwitzOrder i

/--
Concrete replacement for the former unconstrained
`hurwitz_maximal_order : Prop` field.
-/
def hurwitz_maximal_order : Prop :=
  ∀ O : Subring Op,
    B.hurwitzOrder ≤ O → O = B.hurwitzOrder ∨ O = ⊤

/-- The installed over-order law proves maximality of the Hurwitz order. -/
theorem hurwitz_maximal_order_holds :
    B.hurwitz_maximal_order :=
  B.hurwitzOrder_maximal

/-- Restored historical maximal-order readback. -/
theorem hurwitz_maximal_order_readback :
    B.hurwitz_maximal_order :=
  B.hurwitz_maximal_order_holds

/-- Self-duality readback for the explicit root lattice and pairing. -/
@[rep_depth projective]
theorem rootLattice_mem_iff_integral_pairing (x : Op) :
    x ∈ B.rootLattice ↔
      ∀ y ∈ B.rootLattice, ∃ z : ℤ, B.rootPairing x y = z :=
  B.rootLattice_selfDual x

/--
Concrete replacement for the former unconstrained
`d4_hurwitz_root_system : Prop` field: the four selected roots realize the
installed D4 Cartan pairing.
-/
def d4_hurwitz_root_system : Prop :=
  ∀ i j : Fin 4,
    B.rootPairing (B.hurwitzRoots (B.simpleRootLabel i))
        (B.hurwitzRoots (B.simpleRootLabel j)) =
      B.d4CartanMatrix i j

/-- The installed Cartan-pairing law proves the derived D4 root predicate. -/
theorem d4_hurwitz_root_system_holds :
    B.d4_hurwitz_root_system :=
  B.rootPairing_eq_cartan

/--
Concrete replacement for the former unconstrained
`d4_self_dual_lattice : Prop` field, using the installed integral dual-lattice
characterization.
-/
def d4_self_dual_lattice : Prop :=
  ∀ x : Op,
    x ∈ B.rootLattice ↔
      ∀ y ∈ B.rootLattice, ∃ z : ℤ, B.rootPairing x y = z

/-- The installed dual-lattice law proves the derived self-duality predicate. -/
theorem d4_self_dual_lattice_holds :
    B.d4_self_dual_lattice :=
  B.rootLattice_selfDual

/-- Restored historical readback for the concrete D4 Cartan law. -/
theorem d4_hurwitz_root_system_readback :
    B.d4_hurwitz_root_system :=
  B.d4_hurwitz_root_system_holds

/-- Restored historical readback for the concrete lattice self-duality law. -/
theorem d4_self_dual_in_krein :
    B.d4_self_dual_lattice :=
  B.d4_self_dual_lattice_holds

end D4LatticeKacMoodyBridge

/-!
## Native affine Kac-Moody realization

The finite D4/Hurwitz packet and affine current algebra remain type-distinct.
An instantiation must provide the actual loop-current bracket in the native
`AffineCurrentDatum` carrier.
-/

structure D4AffineKacMoodyRealization
    (Finite Alg : Type*)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  affine :
    InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.AffineCurrentDatum Finite Alg
  current_mode_bracket :
    ∀ (m n : ℤ) (X Y : Finite),
      ⁅affine.Current m X, affine.Current n Y⁆ =
        affine.Current (m + n) ⁅X, Y⁆ +
          ((m : ℝ) * affine.killingForm X Y) •
            (if m + n = 0 then affine.kCentral else 0)
  central_commutes : ∀ X : Alg, ⁅affine.kCentral, X⁆ = 0

namespace D4AffineKacMoodyRealization

variable
    {Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (A : D4AffineKacMoodyRealization Finite Alg)

theorem bracket_readback (m n : ℤ) (X Y : Finite) :
    ⁅A.affine.Current m X, A.affine.Current n Y⁆ =
      A.affine.Current (m + n) ⁅X, Y⁆ +
        ((m : ℝ) * A.affine.killingForm X Y) •
          (if m + n = 0 then A.affine.kCentral else 0) :=
  A.affine.current_mode_bracket A.current_mode_bracket m n X Y

theorem central_readback (X : Alg) :
    ⁅A.affine.kCentral, X⁆ = 0 :=
  A.affine.central_commutes_with A.central_commutes X

/--
Native replacement for the former unconstrained
`affine_kac_moody_closure : Prop` field.  Closure is the current-mode bracket
together with centrality of the affine central generator.
-/
def affine_kac_moody_closure : Prop :=
  (∀ (m n : ℤ) (X Y : Finite),
      ⁅A.affine.Current m X, A.affine.Current n Y⁆ =
        A.affine.Current (m + n) ⁅X, Y⁆ +
          ((m : ℝ) * A.affine.killingForm X Y) •
            (if m + n = 0 then A.affine.kCentral else 0)) ∧
    ∀ X : Alg, ⁅A.affine.kCentral, X⁆ = 0

/-- Every installed affine realization satisfies its derived closure law. -/
theorem affine_kac_moody_closure_holds :
    A.affine_kac_moody_closure :=
  ⟨A.current_mode_bracket, A.central_commutes⟩

/-- Restored historical readback for native affine Kac-Moody closure. -/
theorem affine_kac_moody_closure_readback :
    A.affine_kac_moody_closure :=
  A.affine_kac_moody_closure_holds

end D4AffineKacMoodyRealization

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

/-- The Hurwitz/D4 root atom is canonically the existing Wigner--Jones atom. -/
def hurwitzRoot (i : Fin 24) : EndH :=
  B.moebius.wilson.volume.wignerJonesAtom i

/-- The positive affine null-root map is canonically the Drazin `uPlus` map. -/
def affineNullRootPlus (A : EndH) : EndH :=
  B.drazinSplit.uPlus A

/-- The negative affine null-root map is canonically the Drazin `uMinus` map. -/
def affineNullRootMinus (A : EndH) : EndH :=
  B.drazinSplit.uMinus A

/-- The canonical Hurwitz roots are the existing Wigner--Jones atoms. -/
@[simp, rep_depth projective]
theorem root_eq_wignerJonesAtom (i : Fin 24) :
    B.hurwitzRoot i = B.moebius.wilson.volume.wignerJonesAtom i :=
  rfl

/-- The canonical positive affine null-root map is `uPlus`. -/
@[simp, rep_depth operator]
theorem affineNullRootPlus_eq_uPlus (A : EndH) :
    B.affineNullRootPlus A = B.drazinSplit.uPlus A :=
  rfl

/-- The canonical negative affine null-root map is `uMinus`. -/
@[simp, rep_depth operator]
theorem affineNullRootMinus_eq_uMinus (A : EndH) :
    B.affineNullRootMinus A = B.drazinSplit.uMinus A :=
  rfl

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
  B.moebius.atomExpectation_wordAction_invariant g i

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
