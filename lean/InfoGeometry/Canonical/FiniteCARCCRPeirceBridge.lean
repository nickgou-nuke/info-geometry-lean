/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
import InfoGeometry.Canonical.Cl55CommonCarrierIntertwiner
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.UHFHeisenbergSugawaraVirasoroPoset

/-!
# Finite CAR–CCR carrier as a Peirce current system

The two chiral CAR supercharge blocks on the shared polynomial–Clifford Fock
carrier are the opposite off-diagonal corners of a single matrix idempotent.
This connects the finite CAR/CCR representation to the existing Peirce current
operators without identifying the distinct CCR and CAR brackets.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteCARCCRPeirceBridge

open InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
open InfoGeometry.Canonical.CliffordFockSuperTwistorBridge
open InfoGeometry.Twistor.RealSupertwistor
open InfoGeometry.Clifford.Clifford55

abbrev Carrier := SuperOperator (Fin 5) (Fin 5 → ℝ)
abbrev BlockCarrier := Matrix (Fin 2) (Fin 2) Carrier

/-- The first chiral block projection on the two-component common Fock module. -/
def chiralProjection : BlockCarrier := !![1, 0; 0, 0]

/-- The CAR source and sink are combined into one odd operator on the block carrier. -/
def chiralCurrent (i : Fin 5) : BlockCarrier :=
  commonCarrierQPlus i + commonCarrierQMinus i

/-- The upper chiral supercharge block is the finite Clifford-stage
contraction operator, identified through the common exterior-Fock carrier. -/
theorem commonCarrierQPlus_is_stageContraction (i : Fin 5) :
    commonCarrierQPlus i = !![0, stageContraction 5 i; 0, 0] := by
  have h := cl55_creation_eq_common_fermionAnnihilate i
  have hOp : cl55CommonCarrierRep (creation55 i) = stageContraction 5 i := by
    calc
      cl55CommonCarrierRep (creation55 i) =
          fermionAnnihilate (Fin 5) (Fin 5 → ℝ)
            (InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.dualBasisVector i) := h
      _ = fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj i) := by
        rfl
      _ = stageContraction 5 i := (stageContraction_eq_fermionAnnihilate 5 i).symm
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [commonCarrierQPlus, hOp]

/-- The lower chiral supercharge block is the finite Clifford-stage
creation operator, identified through the common exterior-Fock carrier. -/
theorem commonCarrierQMinus_is_stageCreation (i : Fin 5) :
    commonCarrierQMinus i = !![0, 0; cliffordFermionCreate 5 i, 0] := by
  have h := cl55_annihilation_eq_common_fermionCreate i
  have hOp : cl55CommonCarrierRep (annihilation55 i) = cliffordFermionCreate 5 i := by
    calc
      cl55CommonCarrierRep (annihilation55 i) = fermionCreate 5 i := h
      _ = cliffordFermionCreate 5 i :=
        (cliffordFermionCreate_eq_fermionCreate 5 i).symm
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [commonCarrierQMinus, hOp]

/-- The CAR chiral current is the block Dirac operator built from the
finite Clifford-stage creator and contraction on the common carrier. -/
theorem chiralCurrent_is_finiteClifford_block (i : Fin 5) :
    chiralCurrent i = !![0, stageContraction 5 i; cliffordFermionCreate 5 i, 0] := by
  rw [chiralCurrent, commonCarrierQPlus_is_stageContraction,
    commonCarrierQMinus_is_stageCreation]
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c <;> simp

/-- The standard block idempotent defines the positive Peirce source corner. -/
theorem chiralProjection_idempotent : chiralProjection * chiralProjection = chiralProjection := by
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c <;> simp [chiralProjection]

/-- The common-carrier CAR creation block is exactly the upper Peirce current
of the block idempotent. -/
theorem car_creation_is_peirce_source (i : Fin 5) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus chiralProjection (chiralCurrent i) =
      commonCarrierQPlus i := by
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      chiralProjection, chiralCurrent, commonCarrierQPlus, commonCarrierQMinus,
      Matrix.mul_apply, Fin.sum_univ_two]; noncomm_ring

/-- The common-carrier CAR annihilation block is exactly the lower Peirce
current of the complementary block idempotent. -/
theorem car_annihilation_is_peirce_sink (i : Fin 5) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus chiralProjection (chiralCurrent i) =
      commonCarrierQMinus i := by
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
      chiralProjection, chiralCurrent, commonCarrierQPlus, commonCarrierQMinus,
      Matrix.mul_apply, Fin.sum_univ_two]; noncomm_ring

/-- The CAR anticommutator becomes the two diagonal Peirce partner operators
under the source/sink identification. -/
theorem car_current_anticommutator_is_peirce_hodge (i j : Fin 5) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus chiralProjection (chiralCurrent i) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus chiralProjection (chiralCurrent j) +
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus chiralProjection (chiralCurrent j) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus chiralProjection (chiralCurrent i) =
      commonCarrierQPlus i * commonCarrierQMinus j +
        commonCarrierQMinus j * commonCarrierQPlus i := by
  rw [car_creation_is_peirce_source, car_annihilation_is_peirce_sink]

/-- The resulting Hodge operator is the represented CAR partner pair, with no
commutation assumption between the diagonal partner operators. -/
theorem car_current_anticommutator_diagonal (i j : Fin 5) :
    commonCarrierQPlus i * commonCarrierQMinus j +
      commonCarrierQMinus j * commonCarrierQPlus i =
        !![cl55CommonCarrierRep (creation55 i * annihilation55 j), 0;
           0, cl55CommonCarrierRep (annihilation55 j * creation55 i)] := by
  exact commonCarrier_chiral_supercharge_anticommutator i j

/-- A represented CAR creator and annihilator genuinely fail to commute on the
shared carrier. The witness follows from their CAR relation and the creator's
square-zero law, without choosing coordinates for Fock states. -/
theorem commonCarrier_car_creation_annihilation_noncommute (i : Fin 5) :
    let c := cl55CommonCarrierRep (creation55 i)
    let a := cl55CommonCarrierRep (annihilation55 i)
    c * a ≠ a * c := by
  dsimp
  let c := cl55CommonCarrierRep (creation55 i)
  let a := cl55CommonCarrierRep (annihilation55 i)
  have hc : c * c = 0 := by
    change cl55CommonCarrierRep (creation55 i) * cl55CommonCarrierRep (creation55 i) = 0
    rw [← map_mul, creation55_sq i, map_zero]
  have hcar : a * c + c * a = 1 := by
    simpa [a, c] using commonCarrier_cl55_CAR i i
  intro hcomm
  have htwice : c * a + c * a = 1 := by
    calc
      c * a + c * a = a * c + c * a := by rw [hcomm]
      _ = 1 := hcar
  have hcaZero : c * (c * a) = 0 := by
    calc
      c * (c * a) = (c * c) * a := by rw [← mul_assoc]
      _ = 0 := by rw [hc, zero_mul]
  have hcZero : c = 0 := by
    have hmul := congrArg (fun z : Carrier => c * z) htwice
    have : 0 = c := by simpa [mul_add, hcaZero] using hmul
    exact this.symm
  have hzero : (0 : Carrier) = 1 := by
    rw [hcZero] at hcar
    simp at hcar
  exact zero_ne_one hzero

/-- Equivalently, the ordered CAR pair has a nonzero operator commutator. -/
theorem commonCarrier_car_commutator_ne_zero (i : Fin 5) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (cl55CommonCarrierRep (creation55 i))
      (cl55CommonCarrierRep (annihilation55 i)) ≠ 0 := by
  intro hzero
  apply commonCarrier_car_creation_annihilation_noncommute i
  exact sub_eq_zero.mp hzero

/-- The source-minus-sink CAR density is the diagonal particle/hole
commutator on the common Fock carrier. The two diagonal entries retain their
operator order; no scalar occupation-number reduction is made. -/
theorem car_current_chiral_density_diagonal (i : Fin 5) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus chiralProjection (chiralCurrent i) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus chiralProjection (chiralCurrent i) -
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus chiralProjection (chiralCurrent i) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus chiralProjection (chiralCurrent i) =
      !![cl55CommonCarrierRep (creation55 i * annihilation55 i), 0;
         0, -(cl55CommonCarrierRep (annihilation55 i * creation55 i))] := by
  rw [car_creation_is_peirce_source, car_annihilation_is_peirce_sink]
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [commonCarrierQPlus, commonCarrierQMinus, cl55CommonCarrierRep] <;> abel

/-- The common-carrier CAR current is odd for the Peirce chiral parity:
commuting the involution through it doubles the source-minus-sink density.
This is the finite CAR realization of the generic Peirce chiral-current law. -/
theorem car_current_chiral_parity_commutator (i : Fin 5) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.invS chiralProjection)
        (chiralCurrent i) =
      (2 : ℤ) • (commonCarrierQPlus i - commonCarrierQMinus i) := by
  have h :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.chiral_parity_charge_and_source_sink_currents
      chiralProjection_idempotent (chiralCurrent i) (chiralCurrent i)
  rcases h with ⟨_, _, _, _, _, hcomm, _, _, _⟩
  have hcomm' : InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.OperatorAlgebra.PeirceSpine.invS chiralProjection)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.chiralSource chiralProjection (chiralCurrent i) +
        InfoGeometry.OperatorAlgebra.PeirceSpine.chiralSink chiralProjection (chiralCurrent i)) =
      (2 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.chiralSource
        chiralProjection (chiralCurrent i) -
        InfoGeometry.OperatorAlgebra.PeirceSpine.chiralSink
          chiralProjection (chiralCurrent i)) := by
    simpa [InfoGeometry.OperatorAlgebra.PeirceSpine.chiralParityCharge,
      InfoGeometry.OperatorAlgebra.PeirceSpine.invS,
      InfoGeometry.OperatorAlgebra.PeirceSpine.vectorCurrent,
      InfoGeometry.OperatorAlgebra.PeirceSpine.axialCurrent] using hcomm
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.OperatorAlgebra.PeirceSpine.invS chiralProjection)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus chiralProjection (chiralCurrent i) +
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus chiralProjection (chiralCurrent i)) =
      (2 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
        chiralProjection (chiralCurrent i) -
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus
          chiralProjection (chiralCurrent i)) at hcomm'
  rw [car_creation_is_peirce_source, car_annihilation_is_peirce_sink] at hcomm'
  exact hcomm'

end InfoGeometry.Canonical.FiniteCARCCRPeirceBridge

end
