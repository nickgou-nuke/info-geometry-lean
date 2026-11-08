import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorLocalCl11HopParity
import InfoGeometry.Canonical.CuntzTensorToeplitzThreeBridge
import InfoGeometry.OperatorAlgebra.SplitOctonionChiralTriplet

/-!
# Three-mode chiral/Fock bridge

This file is an integration surface.  The one-mode matrix CAR/projector laws
remain owned by `CantorLocalCl11HopParity`; the three-mode occupation and CAR
shadow remain owned by `SplitOctonionChiralFockSpectrum`; and the polarized
Cayley cross product remains owned by `SplitOctonionChiralTriplet`.

The bridge records only the common dictionary:

* the local `(+,-)` projectors are vacuum/occupied projectors;
* the three-mode carrier has `1 + 3 + 3 + 1` degree multiplicities;
* complement reflection exchanges degree one and degree two, giving the
  finite Hodge/complement correspondence;
* the existing triplet cross product is the coordinate Levi--Civita/Hodge
  realization.

No equality between ordinary associative CAR multiplication and the polarized
split-Cayley product is asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.ThreeModeChiralFockSplitOctonionBridge

open InfoGeometry.Canonical.CantorLocalCl11HopParity
open InfoGeometry.Canonical.SplitCliffordCantorFock
open InfoGeometry.OperatorAlgebra.SplitOctonionChiralFockSpectrum
open InfoGeometry.OperatorAlgebra.SplitOctonionChiralTriplet
open InfoGeometry.Canonical.CuntzTensorToeplitzThreeBridge
open InfoGeometry.Canonical.NativeToeplitzCuntzThree
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge

/-! ## The local `Cl(1,1)`/Nambu packet -/

theorem local_cl11_nambu_packet :
    localHopOperator * localHopOperator = (1 : M2R) ∧
    localParityOperator * localParityOperator = (1 : M2R) ∧
    localHopOperator * localParityOperator =
      -(localParityOperator * localHopOperator) ∧
    localPhaseOperator * localPhaseOperator = -(1 : M2R) := by
  exact ⟨localHopOperator_sq, localParityOperator_sq,
    localHop_anticommutes_localParity, localPhaseOperator_sq⟩

theorem local_cl11_state_packet :
    localHopOperator * cantorState false = cantorState true ∧
    localHopOperator * cantorState true = cantorState false ∧
    localParityOperator * cantorState false = cantorState false ∧
    localParityOperator * cantorState true = -cantorState true ∧
    localPhaseOperator * cantorState false = cantorState true ∧
    localPhaseOperator * cantorState true = -cantorState false := by
  exact ⟨localHop_false, localHop_true, localParity_false,
    localParity_true, localPhase_false, localPhase_true⟩

theorem local_cl11_projector_packet :
    localPlusProjection * localPlusProjection = localPlusProjection ∧
    localMinusProjection * localMinusProjection = localMinusProjection ∧
    localPlusProjection * localMinusProjection = 0 ∧
    localMinusProjection * localPlusProjection = 0 ∧
    localPlusProjection + localMinusProjection = (1 : M2R) ∧
    localPlusProjection - localMinusProjection = localParityOperator := by
  exact ⟨localPlusProjection_sq, localMinusProjection_sq,
    localPlusProjection_mul_localMinusProjection,
    localMinusProjection_mul_localPlusProjection,
    localPlusProjection_add_localMinusProjection,
    localPlusProjection_sub_localMinusProjection⟩

/-! ## One-mode chiral projectors and CAR dictionary -/

theorem local_chiral_projector_packet :
    localPlusProjection * localPlusProjection = localPlusProjection ∧
    localMinusProjection * localMinusProjection = localMinusProjection ∧
    localPlusProjection * localMinusProjection = 0 ∧
    localMinusProjection * localPlusProjection = 0 ∧
    localPlusProjection + localMinusProjection = (1 : M2R) ∧
    localPlusProjection - localMinusProjection = localParityOperator := by
  exact ⟨localPlusProjection_sq, localMinusProjection_sq,
    localPlusProjection_mul_localMinusProjection,
    localMinusProjection_mul_localPlusProjection,
    localPlusProjection_add_localMinusProjection,
    localPlusProjection_sub_localMinusProjection⟩

theorem local_chiral_projectors_are_hole_number :
    localPlusProjection = a_op * aDag_op ∧
    localMinusProjection = num_op := by
  constructor
  · exact localPlusProjection_eq_localHoleOperator
  · exact localMinusProjection_eq_localNumberOperator

theorem local_parity_is_hole_minus_number :
    localParityOperator = (a_op * aDag_op) - num_op := by
  rw [localParityOperator, localVacuumProjection,
    localOccupiedProjection]
  rfl

theorem local_chiral_corner_packet :
    a_op = localPlusProjection * a_op * localMinusProjection ∧
    aDag_op = localMinusProjection * aDag_op * localPlusProjection := by
  exact ⟨localAnnihilation_corner, localCreation_corner⟩

/-! ## Three-mode occupation/Fock dictionary -/

theorem three_mode_degree_packet :
    Fintype.card {w : Occupation3 // degree w = 0} = 1 ∧
    Fintype.card {w : Occupation3 // degree w = 1} = 3 ∧
    Fintype.card {w : Occupation3 // degree w = 2} = 3 ∧
    Fintype.card {w : Occupation3 // degree w = 3} = 1 := by
  exact ⟨degree_zero_card, degree_one_card, degree_two_card, degree_three_card⟩

theorem three_mode_car_packet (i j : Fin 3) :
    annihilation i * annihilation j + annihilation j * annihilation i = 0 ∧
    creation i * creation j + creation j * creation i = 0 ∧
    annihilation i * creation j + creation j * annihilation i =
      if i = j then
        (1 : InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.Cl44)
      else 0 := by
  exact ⟨annihilation_anticomm i j, creation_anticomm i j,
    car_pairing i j⟩

theorem three_mode_parity_packet (w : Occupation3) :
    paritySign w * paritySign w = 1 ∧
    paritySign (reflected w) = -paritySign w := by
  exact ⟨paritySign_sq w, paritySign_reflected w⟩

/-! ## Finite Hodge/complement correspondence -/

def hodgeOneToTwo :
    {w : Occupation3 // degree w = 1} ≃
      {w : Occupation3 // degree w = 2} where
  toFun w := ⟨reflected w, by simpa [degree_reflected, w.property]⟩
  invFun w := ⟨reflected w, by simpa [degree_reflected, w.property]⟩
  left_inv w := by
    apply Subtype.ext
    simpa [reflected] using
      InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.Occupation.complement_involutive w.1
  right_inv w := by
    apply Subtype.ext
    simpa [reflected] using
      InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.Occupation.complement_involutive w.1

theorem hodgeOneToTwo_card :
    Fintype.card {w : Occupation3 // degree w = 1} =
      Fintype.card {w : Occupation3 // degree w = 2} := by
  exact Fintype.card_congr hodgeOneToTwo

theorem chiral_even_odd_card :
    Fintype.card {w : Occupation3 // Even (degree w)} = 4 ∧
    Fintype.card {w : Occupation3 // ¬ Even (degree w)} = 4 := by
  exact ⟨even_sector_card, odd_sector_card⟩

/-! The finite coordinate form of the oriented two-form/Hodge map. -/

theorem hodge_cross_components (a b : Vec3 ℝ) :
    cross a b 0 = a 1 * b 2 - a 2 * b 1 ∧
    cross a b 1 = a 2 * b 0 - a 0 * b 2 ∧
    cross a b 2 = a 0 * b 1 - a 1 * b 0 := by
  exact ⟨ChiralAmplitude.cross_component_zero a b,
    ChiralAmplitude.cross_component_one a b,
    ChiralAmplitude.cross_component_two a b⟩

/-! ## Toeplitz--Cuntz vacuum boundary

The native three-generator carrier is retained as an infinite-word boundary
model.  Only its already-proved defect facts are imported here; it is not
identified with the finite three-fermion exterior sector above.
-/

theorem native_toeplitz_vacuum_packet :
    nativeToeplitzThreeGenerators.P0 * nativeToeplitzThreeGenerators.P0 =
        nativeToeplitzThreeGenerators.P0 ∧
    star nativeToeplitzThreeGenerators.P0 = nativeToeplitzThreeGenerators.P0 ∧
    nativeToeplitzThreeGenerators.P1 +
        nativeToeplitzThreeGenerators.P2 +
        nativeToeplitzThreeGenerators.P3 +
        nativeToeplitzThreeGenerators.P0 =
      (1 : NativeToeplitzThree) := by
  exact ⟨native_defect_is_projection,
    native_defect_is_self_adjoint,
    native_three_resolution⟩

end InfoGeometry.OperatorAlgebra.ThreeModeChiralFockSplitOctonionBridge
