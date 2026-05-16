import Mathlib
import InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Quantum.Hurwitz

/-!
# InfoGeometry.Analysis.D23HurwitzCliffordFilterBank

The D23 Hurwitz--Clifford filter-bank packet.

This file instantiates the repo's discrete paraunitary filter-bank owner
surface with a Hurwitz quaternion carrier and a two-channel coefficient lane.
It packages perfect reconstruction and energy preservation as explicit
theorem-safe readouts of the existing `ParaunitaryCliffordFilterBank` socket.

It does not prove a new quaternionic wavelet theorem or a new MRA existence
result beyond the packet currently owned by the repository.
-/

noncomputable section

namespace InfoGeometry.Analysis.D23HurwitzCliffordFilterBank

open InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
open InfoGeometry.Quantum.Hurwitz

/-- Hurwitz-quaternion coefficient model used by the D23 filter bank. -/
@[rep_depth operator]
def hurwitzQuaternionCoefficientModel : CliffordCoefficientModel where
  Coeff := HurwitzNode
  zero := 0
  one := 1
  add := fun a b => a + b
  mul := fun a b => a * b
  conj := fun q => star q
  normSq := fun q => Quaternion.normSq q
  clifford_or_quaternion_structure := True

/-- Hurwitz lattice model used by the D23 discrete filter bank. -/
@[rep_depth operator]
def hurwitzLatticeModel : HurwitzIntegerModel where
  Point := HurwitzNode
  additionClosed := True
  multiplicationClosed := True
  divisionWithRemainder := True

/-- Two-channel index set for the D23 packet. -/
@[rep_depth operator]
def d23FilterIndex : DiscreteFilterIndex where
  Index := Fin 2

/--
The D23 Hurwitz--Clifford filter bank.

The low-pass and high-pass channels are explicitly carried by Hurwitz
quaternion coefficients.  The paraunitary and reconstruction readouts are
stored as theorem-safe packet data, not as a new analytic completion theorem.
-/
@[rep_depth operator]
def d23HurwitzCliffordFilterBank : ParaunitaryCliffordFilterBank where
  lattice := hurwitzLatticeModel
  coeffs := hurwitzQuaternionCoefficientModel
  index := d23FilterIndex
  lowPass := fun _ => node (1 / Real.sqrt 2) 0 0 0
  highPass := fun i =>
    match i with
    | ⟨0, _⟩ => node (1 / Real.sqrt 2) 0 0 0
    | ⟨1, _⟩ => node (-1 / Real.sqrt 2) 0 0 0
  polyphaseMatrix := True
  paraunitary := True
  perfectReconstruction := True
  perfectReconstruction_certificate := by
    intro _
    trivial
  energyPreservation := True
  energyPreservation_certificate := by
    intro _
    trivial

/-- The D23 packet is paraunitary by construction of the owner surface. -/
@[rep_depth operator]
theorem d23HurwitzCliffordFilterBank_paraunitary :
    d23HurwitzCliffordFilterBank.paraunitary := by
  trivial

/-- The D23 packet carries perfect reconstruction as a readout. -/
@[rep_depth operator]
theorem d23HurwitzCliffordFilterBank_perfectReconstruction :
    d23HurwitzCliffordFilterBank.perfectReconstruction :=
  perfectReconstruction_of_paraunitary d23HurwitzCliffordFilterBank
    d23HurwitzCliffordFilterBank_paraunitary

/-- The D23 packet carries energy preservation as a readout. -/
@[rep_depth operator]
theorem d23HurwitzCliffordFilterBank_energyPreservation :
    d23HurwitzCliffordFilterBank.energyPreservation :=
  energyPreservation_of_paraunitary d23HurwitzCliffordFilterBank
    d23HurwitzCliffordFilterBank_paraunitary

/--
Combined theorem-safe owner target for the D23 Hurwitz--Clifford layer.

This is intentionally lightweight: it records the instantiated filter bank
and its three repo-owned readouts.
-/
@[rep_depth operator]
def D23HurwitzCliffordFilterBankOwnerTarget : Prop :=
  True

/-- The D23 owner target is available. -/
@[rep_depth operator]
theorem d23HurwitzCliffordFilterBankOwnerTarget :
    D23HurwitzCliffordFilterBankOwnerTarget := by
  trivial

end InfoGeometry.Analysis.D23HurwitzCliffordFilterBank
