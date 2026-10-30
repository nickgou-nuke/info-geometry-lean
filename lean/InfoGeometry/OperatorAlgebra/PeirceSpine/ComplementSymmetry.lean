import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# A₃₅: complement symmetry of the Peirce expressions

Replacing `(P,A,C)` by `(1-P,C,A)` exchanges the two corner expressions.
The sum and anticommutator are preserved; the difference and commutator
change sign. These polynomial identities do not require idempotence.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

theorem conePlus_complement (P C : B) :
    conePlus (1 - P) C = coneMinus P C := by
  unfold conePlus coneMinus
  noncomm_ring

theorem coneMinus_complement (P A : B) :
    coneMinus (1 - P) A = conePlus P A := by
  unfold conePlus coneMinus
  noncomm_ring

theorem genPhi_complement (P A C : B) :
    genPhi (1 - P) C A = genPhi P A C := by
  simp only [genPhi, conePlus_complement, coneMinus_complement]
  abel

theorem genJ_complement (P A C : B) :
    genJ (1 - P) C A = -genJ P A C := by
  simp only [genJ, conePlus_complement, coneMinus_complement]
  abel

theorem genV_complement (P A C : B) :
    genV (1 - P) C A = genV P A C := by
  simp only [genV, anticomm, conePlus_complement, coneMinus_complement]
  abel

theorem genSig_complement (P A C : B) :
    genSig (1 - P) C A = -genSig P A C := by
  simp only [genSig, comm, conePlus_complement, coneMinus_complement]
  abel

theorem qgtPlus_complement (P A C : B) :
    qgtPlus (1 - P) C A = qgtMinus P A C := by
  simp only [qgtPlus, qgtMinus, conePlus_complement, coneMinus_complement]

theorem qgtMinus_complement (P A C : B) :
    qgtMinus (1 - P) C A = qgtPlus P A C := by
  simp only [qgtPlus, qgtMinus, conePlus_complement, coneMinus_complement]

end InfoGeometry.OperatorAlgebra.PeirceSpine
