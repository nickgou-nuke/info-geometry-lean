import InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
import InfoGeometry.OperatorAlgebra.ModularTwinZornRepresentation
import InfoGeometry.OperatorAlgebra.KleinDiracKahlerOperatorZorn
import InfoGeometry.OperatorAlgebra.ChiralWeylOperatorZornRepresentation
import InfoGeometry.OperatorAlgebra.TwinLightconeWeylOperatorZorn
import InfoGeometry.OperatorAlgebra.KreinModularTwinFourVector
import InfoGeometry.OperatorAlgebra.TwoBoundaryWeakValueZorn
import InfoGeometry.Clifford.Pin55KramersKleinAll

/-!
# Capstone: twin operator-Zorn formalism

The capstone exposes one typed architecture while preserving the distinctions
between its operations:

* a `4+4` module coordinate equivalent to the native operator-Zorn carrier;
* a non-associative Zorn product with explicit commutator-cross defects;
* an associative `2 x 2` operator block with Peirce and Cartan decomposition;
* two-boundary normalized matrix-coefficient readouts;
* a Tomita-style algebra/commutant exchange with square `+1`;
* a Kramers antiunitary with square `-1`;
* a Dirac--Kahler odd block and diagonal square;
* a Klein sheet exchange satisfying `G T G = T^{-1}`;
* abstract left/right chiral representation intertwiners;
* cyclotomic roots of identity and Peirce roots of zero.

The capstone deliberately does not identify the native Zorn product with the
associative matrix product, the Tomita involution with Kramers time reversal,
or an abstract chiral representation pair with the Lorentz group before an
explicit representation is supplied.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorZornTwinFormalism

open InfoGeometry.Canonical
open InfoGeometry.Physics
open InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
open InfoGeometry.OperatorAlgebra.ModularTwinZornRepresentation
open InfoGeometry.OperatorAlgebra.KleinDiracKahlerOperatorZorn
open InfoGeometry.OperatorAlgebra.ChiralWeylOperatorZornRepresentation
open InfoGeometry.OperatorAlgebra.TwinLightconeWeylOperatorZorn
open InfoGeometry.Quantum.ComplexKramersAntiunitary

variable {A : Type*} [Ring A]

/-- Literal `4+4` module-coordinate equivalence. -/
def fourPlusFourEquiv :
    TwinFourOperatorVector A ≃ InfoGeometry.Canonical.OperatorZornMatrix A :=
  equivNativeZorn

/-- In the native non-associative product, the self-cross obstruction vanishes
exactly when the three operator components commute pairwise. -/
theorem native_self_cross_obstruction
    (u : Fin 3 -> A) :
    operatorCross u u = 0 ↔
      u 1 * u 2 = u 2 * u 1 ∧
      u 2 * u 0 = u 0 * u 2 ∧
      u 0 * u 1 = u 1 * u 0 :=
  operatorCross_self_eq_zero_iff u

section Associative

variable [StarRing A]

/-- Peirce/Cartan packet for the associative shell. -/
theorem associative_peirce_cartan_packet :
    ePlus (A := A) * ePlus = ePlus ∧
      eMinus (A := A) * eMinus = eMinus ∧
      ePlus (A := A) * eMinus = 0 ∧
      eMinus (A := A) * ePlus = 0 ∧
      ePlus (A := A) + eMinus = 1 ∧
      grading (A := A) * grading = 1 ∧
      sheetExchange (A := A) * sheetExchange = 1 := by
  exact ⟨ePlus_sq, eMinus_sq, ePlus_mul_eMinus,
    eMinus_mul_ePlus, ePlus_add_eMinus, grading_sq,
    sheetExchange_sq⟩

/-- A generic Dirac--Kahler datum has an odd Zorn block whose square is the
negative doubled Laplacian. -/
theorem diracKahler_block_packet
    (K : RingDiracKahler A) :
    IsOdd K.zornBlock ∧
      K.zornBlock * K.zornBlock =
        (⟨-K.laplacian, -K.laplacian, 0, 0⟩ : ZornBlock A) := by
  exact ⟨pureDiracBlock_isOdd K.dirac K.dirac,
    K.zornBlock_sq⟩

/-- The operator representation of the Klein relation. -/
theorem klein_operator_relation (u : Units A) :
    kleinGlide * phaseTranslation u * kleinGlide =
      phaseTranslation u⁻¹ :=
  kleinGlide_conjugates_phaseTranslation u

end Associative

/-- The scalar Pauli paravector is exactly the scalar specialization of the
operator light-cone/Weyl soldering. -/
theorem scalar_weyl_soldering
    (p : InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector) :
    weylMatrix (ofPauliParavector p) = p.pauliMatrix :=
  weylMatrix_ofPauliParavector p

section ModularVsKramers

variable {B : Type*} [Ring B] [StarRing B]
variable [StarRing A]

/-- Tomita-style modular exchange and Kramers time reversal have different
square laws on different carriers. -/
theorem modular_and_kramers_square_separation
    (P : ModularTwinRepresentation A B)
    (Z : ZornBlock B) (v : H2) :
    P.modularExchange (P.modularExchange Z) = Z ∧
      timeReversal (timeReversal v) = -v := by
  exact ⟨P.modularExchange_involutive Z,
    timeReversal_sq v⟩

end ModularVsKramers

section ChiralRepresentation

variable {G B : Type*} [Group G] [Ring B] [StarRing B]

/-- An explicitly supplied left/right representation pair fixes every block
made from genuine opposite intertwiners. -/
theorem left_right_chiral_block_invariant
    (R : ChiralRepresentationPair G B)
    (g : G) (Q : R.ChiralIntertwiner) :
    R.conjugate g (R.pureChiralBlock Q) = R.pureChiralBlock Q :=
  R.conjugate_pureChiralBlock g Q

end ChiralRepresentation

/-- Kramers remains the square-minus-one complex antiunitary already proved in
the stacked base branch. -/
theorem kramers_square_minus_one (v : H2) :
    timeReversal (timeReversal v) = -v :=
  timeReversal_sq v

end InfoGeometry.OperatorAlgebra.OperatorZornTwinFormalism
