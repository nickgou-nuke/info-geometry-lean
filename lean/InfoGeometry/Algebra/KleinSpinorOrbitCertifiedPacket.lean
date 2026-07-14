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

namespace KleinSpinorOrbitCertifiedPacket

open InfoGeometry.Algebra.KleinSpinorOrbit
open InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure

/-- Proof-carrying finite packet parallel to the weak socket structure. -/
structure CertifiedOrbitPacket where
  epsilon : Cs.Cs
  epsilon_square_two_add : Cs.mul epsilon epsilon = Cs.add epsilon epsilon
  generic_representative_complete :
    ∀ M : CsMatrix2,
      Stabilizes M genericRep ↔ M.aa = Cs.one ∧ M.ba = Cs.zero
  null_representative_complete :
    ∀ M : CsMatrix2,
      Stabilizes M nullRep ↔ Cs.mul M.aa Cs.E = Cs.E ∧ Cs.mul M.ba Cs.E = Cs.zero
  diagonal_null_representative_complete :
    ∀ M : CsMatrix2,
      Stabilizes M diagonalNullRep ↔
        Cs.add (Cs.mul M.aa Cs.E) (Cs.mul M.ab Cs.E) = Cs.E ∧
        Cs.add (Cs.mul M.ba Cs.E) (Cs.mul M.bb Cs.E) = Cs.E
  generic_stabilizer_description :
    ∀ b : Cs.Cs,
      CsMatrix2.DetOne (CsMatrix2.genericUnipotent b) ∧
        Stabilizes (CsMatrix2.genericUnipotent b) genericRep
  null_stabilizer_description :
    ∀ t : ℚ,
      CsMatrix2.DetOne (CsMatrix2.nullEbarFamily t) ∧
        Stabilizes (CsMatrix2.nullEbarFamily t) nullRep

/-- Certified finite orbit packet over the split-complex lightlike generator `E`. -/
def splitComplexPacket : CertifiedOrbitPacket where
  epsilon := Cs.E
  epsilon_square_two_add := by
    apply SplitC.ext <;> norm_num [Cs.mul, Cs.add, Cs.E, SplitC.mul, SplitC.add, SplitC.E]
  generic_representative_complete := generic_representative_complete_proved
  null_representative_complete := stabilizes_null_iff
  diagonal_null_representative_complete := stabilizes_diagonalNull_iff
  generic_stabilizer_description := generic_stabilizer_description_proved
  null_stabilizer_description := by
    intro t
    exact ⟨CsMatrix2.nullEbarFamily_det_one t, null_stabilizer_description_proved t⟩

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

end KleinSpinorOrbitCertifiedPacket
