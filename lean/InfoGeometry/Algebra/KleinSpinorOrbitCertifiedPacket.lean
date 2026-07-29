import InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure
import Mathlib.Tactic

open InfoGeometry.Clifford.Arxiv160309063

/-!
# Proof-carrying replacement for the weak Klein-spinor orbit socket

`SplitJordanSpinor.KleinSpinorOrbitStratification` stores the orbit-closure claims
as bare propositions. This file does not edit that dirty/off-limits surface.
Instead it introduces a parallel proof-carrying packet whose fields are the exact
finite theorems already verified in `KleinSpinorOrbitSocketClosure`.

Scope:
* split-complex `E = 1 + j` finite square law `E^2 = E + E`;
* generic/null/diagonal raw stabilizer equivalences;
* explicit determinant-one generic stabilizer family;
* explicit determinant-one null `Ebar`-annihilator stabilizer family.

Boundary:
* no full orbit classification;
* no dimension-count theorem;
* no `Spin(2,2) ≃ SL(2,C_s)` theorem.
-/

namespace InfoGeometry.Algebra.KleinSpinorOrbitCertifiedPacket

open InfoGeometry.Algebra.KleinSpinorOrbit
open InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure

/-- Proof-carrying finite packet parallel to the weak socket structure. -/
abbrev CertifiedOrbitPacket : Type :=
  Σ' epsilon : Cs.Cs,
    Cs.mul epsilon epsilon = Cs.add epsilon epsilon ∧
      (∀ M : CsMatrix2,
        Stabilizes M genericRep ↔ M.aa = Cs.one ∧ M.ba = Cs.zero) ∧
        (∀ M : CsMatrix2,
          Stabilizes M nullRep ↔
            Cs.mul M.aa Cs.E = Cs.E ∧ Cs.mul M.ba Cs.E = Cs.zero) ∧
          (∀ M : CsMatrix2,
            Stabilizes M diagonalNullRep ↔
              Cs.add (Cs.mul M.aa Cs.E) (Cs.mul M.ab Cs.E) = Cs.E ∧
                Cs.add (Cs.mul M.ba Cs.E) (Cs.mul M.bb Cs.E) = Cs.E) ∧
            (∀ b : Cs.Cs,
              CsMatrix2.DetOne (CsMatrix2.genericUnipotent b) ∧
                Stabilizes (CsMatrix2.genericUnipotent b) genericRep) ∧
              (∀ t : ℚ,
                CsMatrix2.DetOne (CsMatrix2.nullEbarFamily t) ∧
                  Stabilizes (CsMatrix2.nullEbarFamily t) nullRep)

namespace CertifiedOrbitPacket

abbrev epsilon (P : CertifiedOrbitPacket) : Cs.Cs := P.1

abbrev epsilon_square_two_add (P : CertifiedOrbitPacket) :
    Cs.mul P.epsilon P.epsilon = Cs.add P.epsilon P.epsilon :=
  P.2.1

abbrev generic_representative_complete (P : CertifiedOrbitPacket) :
    ∀ M : CsMatrix2,
      Stabilizes M genericRep ↔ M.aa = Cs.one ∧ M.ba = Cs.zero :=
  P.2.2.1

abbrev null_representative_complete (P : CertifiedOrbitPacket) :
    ∀ M : CsMatrix2,
      Stabilizes M nullRep ↔ Cs.mul M.aa Cs.E = Cs.E ∧ Cs.mul M.ba Cs.E = Cs.zero :=
  P.2.2.2.1

abbrev diagonal_null_representative_complete (P : CertifiedOrbitPacket) :
    ∀ M : CsMatrix2,
      Stabilizes M diagonalNullRep ↔
        Cs.add (Cs.mul M.aa Cs.E) (Cs.mul M.ab Cs.E) = Cs.E ∧
          Cs.add (Cs.mul M.ba Cs.E) (Cs.mul M.bb Cs.E) = Cs.E :=
  P.2.2.2.2.1

abbrev generic_stabilizer_description (P : CertifiedOrbitPacket) :
    ∀ b : Cs.Cs,
      CsMatrix2.DetOne (CsMatrix2.genericUnipotent b) ∧
        Stabilizes (CsMatrix2.genericUnipotent b) genericRep :=
  P.2.2.2.2.2.1

abbrev null_stabilizer_description (P : CertifiedOrbitPacket) :
    ∀ t : ℚ,
      CsMatrix2.DetOne (CsMatrix2.nullEbarFamily t) ∧
        Stabilizes (CsMatrix2.nullEbarFamily t) nullRep :=
  P.2.2.2.2.2.2

end CertifiedOrbitPacket

/-- Certified finite orbit packet over the split-complex lightlike generator `E`. -/
def splitComplexPacket : CertifiedOrbitPacket :=
  ⟨Cs.E,
    by
      apply SplitC.ext <;>
        norm_num [Cs.mul, Cs.add, Cs.E, SplitC.mul, SplitC.add, SplitC.E],
    generic_representative_complete_proved,
    stabilizes_null_iff,
    stabilizes_diagonalNull_iff,
    generic_stabilizer_description_proved,
    by
      intro t
      exact ⟨CsMatrix2.nullEbarFamily_det_one t, null_stabilizer_description_proved t⟩⟩

@[simp] theorem splitComplexPacket_epsilon :
    splitComplexPacket.epsilon = Cs.E := rfl

@[simp] theorem splitComplexPacket_generic (M : CsMatrix2) :
    Stabilizes M genericRep ↔ M.aa = Cs.one ∧ M.ba = Cs.zero :=
  splitComplexPacket.generic_representative_complete M

@[simp] theorem splitComplexPacket_null (M : CsMatrix2) :
    Stabilizes M nullRep ↔ Cs.mul M.aa Cs.E = Cs.E ∧ Cs.mul M.ba Cs.E = Cs.zero :=
  splitComplexPacket.null_representative_complete M

@[simp] theorem splitComplexPacket_diagonal_null (M : CsMatrix2) :
    Stabilizes M diagonalNullRep ↔
      Cs.add (Cs.mul M.aa Cs.E) (Cs.mul M.ab Cs.E) = Cs.E ∧
      Cs.add (Cs.mul M.ba Cs.E) (Cs.mul M.bb Cs.E) = Cs.E :=
  splitComplexPacket.diagonal_null_representative_complete M

end InfoGeometry.Algebra.KleinSpinorOrbitCertifiedPacket
