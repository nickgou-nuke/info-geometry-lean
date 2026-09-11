import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UnifiedSuperchargeAlgebra

/-!
# Real BdG / Nambu-Gorkov fusion

Canonical bridge from the real doubled BdG carrier to the doubled Nambu-Gorkov
block calculus.

The BdG datum stays the owner surface. The Nambu block operator is derived from
that datum and then read back through the existing `τ₃` grading lemmas.
-/

namespace InfoGeometry.Canonical.RealBdGNambuGorkovFusion

open InfoGeometry.Canonical.RealBdG
open InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
open InfoGeometry.Krein

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- Canonical owner packet for the real BdG carrier. -/
structure RealBdGNambuGorkovPacket
    (E : Type)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  bdg : RealBdGDatum (E := E)

/-- The Nambu-Gorkov operator induced by a real BdG datum. -/
noncomputable def nambuGorkovOp (P : RealBdGNambuGorkovPacket E) :
    NambuGorkovOp H₂ where
  diag11 := P.bdg.H.toAddMonoidHom
  off12 := P.bdg.particleHole.toAddMonoidHom
  off21 := P.bdg.timeReversal.toAddMonoidHom
  diag22 := P.bdg.chiral.toAddMonoidHom

/-- The induced Nambu-Gorkov block action on the doubled carrier. -/
noncomputable def nambuBlock (P : RealBdGNambuGorkovPacket E) :
    NambuSpinor H₂ →+ NambuSpinor H₂ :=
  (nambuGorkovOp (E := E) P).toBlockHom

/-- The BdG-induced Nambu block is `τ₃`-graded with the standard split. -/
theorem nambuTau3_split
    (P : RealBdGNambuGorkovPacket E)
    (v : NambuSpinor H₂) :
    nambuTau3 (nambuBlock (E := E) P v) =
      nambuBlockDiag P.bdg.H.toAddMonoidHom P.bdg.chiral.toAddMonoidHom (nambuTau3 v) -
      nambuBlockOffDiag P.bdg.particleHole.toAddMonoidHom P.bdg.timeReversal.toAddMonoidHom
        (nambuTau3 v) := by
  simpa [nambuBlock, nambuGorkovOp] using
    (nambuTau3_full_split
      (A := H₂)
      (a := P.bdg.H.toAddMonoidHom)
      (b := P.bdg.particleHole.toAddMonoidHom)
      (c := P.bdg.timeReversal.toAddMonoidHom)
      (d := P.bdg.chiral.toAddMonoidHom)
      v)

/-- The induced Nambu block square is the generic doubled square expansion. -/
theorem nambuBlock_square_apply
    (P : RealBdGNambuGorkovPacket E)
    (v : NambuSpinor H₂) :
    nambuBlock (E := E) P (nambuBlock (E := E) P v) =
      (P.bdg.H.toAddMonoidHom (P.bdg.H.toAddMonoidHom v.1)
        + P.bdg.H.toAddMonoidHom (P.bdg.particleHole.toAddMonoidHom v.2)
        + P.bdg.particleHole.toAddMonoidHom (P.bdg.timeReversal.toAddMonoidHom v.1)
        + P.bdg.particleHole.toAddMonoidHom (P.bdg.chiral.toAddMonoidHom v.2),
       P.bdg.timeReversal.toAddMonoidHom (P.bdg.H.toAddMonoidHom v.1)
        + P.bdg.timeReversal.toAddMonoidHom (P.bdg.particleHole.toAddMonoidHom v.2)
        + P.bdg.chiral.toAddMonoidHom (P.bdg.timeReversal.toAddMonoidHom v.1)
        + P.bdg.chiral.toAddMonoidHom (P.bdg.chiral.toAddMonoidHom v.2)) := by
  simpa [nambuBlock, nambuGorkovOp] using
    (NambuGorkovOp.square_apply (A := H₂) (N := nambuGorkovOp (E := E) P) v)

end Core

end InfoGeometry.Canonical.RealBdGNambuGorkovFusion
