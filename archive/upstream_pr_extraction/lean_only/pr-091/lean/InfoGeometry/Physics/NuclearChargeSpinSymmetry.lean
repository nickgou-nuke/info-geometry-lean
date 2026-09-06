import Mathlib
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Canonical.BostConnesGalois

/-!
# Nuclear charge/spin preserving symmetry interface

This file defines exactly what it means for a transformation of the currently
formalized nuclear quantum-number packet to preserve the owned readouts:

* `2J`;
* occupation number;
* `2T₃`;
* quasiparticle fermion parity (derived from occupation preservation).

It also defines a conservative arithmetic/Galois extension in which the
supplied Bost--Connes Galois action acts on an arithmetic coordinate while the
nuclear packet is fixed.  Thus charge/spin preservation is a theorem, but no
nontrivial Galois action on nuclear quantum numbers is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearChargeSpinSymmetry

open InfoGeometry.Physics.NuclearQuantumNumberPacket
open InfoGeometry.Canonical.BostConnesGalois

abbrev QN := QuantumNumbers

/-- An exact symmetry of the finite nuclear packet preserving all currently
owned discrete readouts. -/
structure QuantumNumberSymmetry where
  toEquiv : QN ≃ QN
  preserves_twoJ : ∀ q, (toEquiv q).twoJ = q.twoJ
  preserves_occupation : ∀ q, (toEquiv q).occupationNumber = q.occupationNumber
  preserves_twoT3 : ∀ q, (toEquiv q).twoT3 = q.twoT3

namespace QuantumNumberSymmetry

instance : CoeFun QuantumNumberSymmetry (fun _ => QN → QN) :=
  ⟨fun s => s.toEquiv⟩

/-- Preservation of quasiparticle parity follows from occupation preservation. -/
theorem preserves_quasiparticleParity (s : QuantumNumberSymmetry) (q : QN) :
    (s q).quasiparticleParity = q.quasiparticleParity := by
  rw [QuantumNumbers.quasiparticleParity_formula,
    QuantumNumbers.quasiparticleParity_formula, s.preserves_occupation]

/-- Preservation of the centered occupation Cartan weight also follows. -/
theorem preserves_occupationCartanWeight (s : QuantumNumberSymmetry) (q : QN) :
    (s q).occupationCartanWeight = q.occupationCartanWeight := by
  rw [QuantumNumbers.occupationCartanWeight_formula,
    QuantumNumbers.occupationCartanWeight_formula, s.preserves_occupation]

/-- Identity nuclear symmetry. -/
def id : QuantumNumberSymmetry where
  toEquiv := Equiv.refl QN
  preserves_twoJ := by intro q; rfl
  preserves_occupation := by intro q; rfl
  preserves_twoT3 := by intro q; rfl

/-- Composition of charge/spin preserving nuclear symmetries. -/
def comp (s t : QuantumNumberSymmetry) : QuantumNumberSymmetry where
  toEquiv := s.toEquiv.trans t.toEquiv
  preserves_twoJ := by
    intro q
    change (t (s q)).twoJ = q.twoJ
    rw [t.preserves_twoJ, s.preserves_twoJ]
  preserves_occupation := by
    intro q
    change (t (s q)).occupationNumber = q.occupationNumber
    rw [t.preserves_occupation, s.preserves_occupation]
  preserves_twoT3 := by
    intro q
    change (t (s q)).twoT3 = q.twoT3
    rw [t.preserves_twoT3, s.preserves_twoT3]

/-- Consolidated exact preservation packet. -/
theorem preservation_packet (s : QuantumNumberSymmetry) (q : QN) :
    (s q).twoJ = q.twoJ ∧
      (s q).twoT3 = q.twoT3 ∧
      (s q).occupationNumber = q.occupationNumber ∧
      (s q).quasiparticleParity = q.quasiparticleParity :=
  ⟨s.preserves_twoJ q, s.preserves_twoT3 q,
    s.preserves_occupation q, s.preserves_quasiparticleParity q⟩

end QuantumNumberSymmetry

/-! ## Arithmetic/Galois extension with inert nuclear quantum numbers -/

universe u

variable {G : Type u} [GaloisActionData G]

/-- Nuclear packet paired with the rational cyclotomic index acted on by the
Bost--Connes Galois interface. -/
abbrev ArithmeticNuclearState := QN × ℚ

/-- Diagonal extension of the supplied Galois action: arithmetic data moves,
while the nuclear packet is fixed. -/
def galoisExtendedAction (g : G) (x : ArithmeticNuclearState) :
    ArithmeticNuclearState :=
  (x.1, GaloisActionData.actOnQ g x.2)

@[simp] theorem galoisExtendedAction_nuclear (g : G)
    (x : ArithmeticNuclearState) :
    (galoisExtendedAction g x).1 = x.1 := rfl

/-- The arithmetic Galois extension preserves nuclear spin `2J`. -/
theorem galoisExtendedAction_preserves_twoJ (g : G)
    (x : ArithmeticNuclearState) :
    (galoisExtendedAction g x).1.twoJ = x.1.twoJ := rfl

/-- The arithmetic Galois extension preserves Wigner charge/isospin `2T₃`. -/
theorem galoisExtendedAction_preserves_twoT3 (g : G)
    (x : ArithmeticNuclearState) :
    (galoisExtendedAction g x).1.twoT3 = x.1.twoT3 := rfl

/-- It also preserves occupation and quasiparticle parity. -/
theorem galoisExtendedAction_preservation_packet (g : G)
    (x : ArithmeticNuclearState) :
    (galoisExtendedAction g x).1.twoJ = x.1.twoJ ∧
      (galoisExtendedAction g x).1.twoT3 = x.1.twoT3 ∧
      (galoisExtendedAction g x).1.occupationNumber = x.1.occupationNumber ∧
      (galoisExtendedAction g x).1.quasiparticleParity = x.1.quasiparticleParity := by
  rfl

end InfoGeometry.Physics.NuclearChargeSpinSymmetry

end noncomputable section
