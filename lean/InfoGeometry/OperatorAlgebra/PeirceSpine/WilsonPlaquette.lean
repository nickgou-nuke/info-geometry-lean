/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Ordered Peirce plaquette expansions

The four-factor words below are algebraic words in the two nilpotent Peirce
corners. Their expansions retain the chiral-square terms; no geometric or
physical interpretation is assumed.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def wilsonPlaquette (P A C : B) : B :=
  (1 + conePlus P A) * (1 + coneMinus P C) *
    (1 - conePlus P A) * (1 - coneMinus P C)

def wilsonPlaquetteRev (P A C : B) : B :=
  (1 + coneMinus P C) * (1 + conePlus P A) *
    (1 - coneMinus P C) * (1 - conePlus P A)

variable {P : B} (hP : P * P = P)
include hP

theorem wilsonPlaquette_ordered_expansions (A C : B) :
    wilsonPlaquette P A C =
      1 + genSig P A C - genV P A C * genJ P A C +
        qgtPlus P A C * qgtPlus P A C ∧
    wilsonPlaquetteRev P A C =
      1 - genSig P A C + genV P A C * genJ P A C +
        qgtMinus P A C * qgtMinus P A C := by
  constructor <;>
    simp only [wilsonPlaquette, wilsonPlaquetteRev,
      genSig, genV, genJ, qgtPlus, qgtMinus,
      comm, anticomm, conePlus, coneMinus] <;>
    peirce_nf hP

theorem wilsonPlaquette_symmetric_even_part (A C : B) :
    evenGrade P ((1 - wilsonPlaquette P A C) +
      (1 - wilsonPlaquetteRev P A C)) =
        -(genV P A C * genV P A C) := by
  rcases wilsonPlaquette_ordered_expansions hP A C with ⟨h₁, h₂⟩
  rw [h₁, h₂]
  simp only [evenGrade, genV, anticomm, genSig, comm,
    qgtPlus, qgtMinus, conePlus, coneMinus]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
