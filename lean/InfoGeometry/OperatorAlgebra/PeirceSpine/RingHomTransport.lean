import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingPerturbation
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Naturality of Peirce polynomial operators

Ring homomorphisms preserve the indicated noncommutative polynomial words.
No injectivity, surjectivity, star structure, or characteristic assumption is
required. This API supplies transport laws; existing colimit and cohomology
owners carry the additional structure needed for those constructions.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B D E : Type*} [Ring B] [Ring D] [Ring E]

theorem map_idempotent (f : B →+* D) {P : B} (hP : P * P = P) :
    f P * f P = f P := by
  rw [← map_mul, hP]

@[simp] theorem map_comm (f : B →+* D) (X Y : B) :
    f (comm X Y) = comm (f X) (f Y) := by
  simp [comm]

@[simp] theorem map_anticomm (f : B →+* D) (X Y : B) :
    f (anticomm X Y) = anticomm (f X) (f Y) := by
  simp [anticomm]

@[simp] theorem map_invS (f : B →+* D) (P : B) :
    f (invS P) = invS (f P) := by
  simp [invS]

@[simp] theorem map_conePlus (f : B →+* D) (P A : B) :
    f (conePlus P A) = conePlus (f P) (f A) := by
  simp [conePlus]

@[simp] theorem map_coneMinus (f : B →+* D) (P C : B) :
    f (coneMinus P C) = coneMinus (f P) (f C) := by
  simp [coneMinus]

@[simp] theorem map_peirce11 (f : B →+* D) (P X : B) :
    f (peirce11 P X) = peirce11 (f P) (f X) := by
  simp [peirce11]

@[simp] theorem map_peirce00 (f : B →+* D) (P X : B) :
    f (peirce00 P X) = peirce00 (f P) (f X) := by
  simp [peirce00]

@[simp] theorem map_evenGrade (f : B →+* D) (P X : B) :
    f (evenGrade P X) = evenGrade (f P) (f X) := by
  simp [evenGrade]

@[simp] theorem map_oddGrade (f : B →+* D) (P X : B) :
    f (oddGrade P X) = oddGrade (f P) (f X) := by
  simp [oddGrade]

@[simp] theorem map_genPhi (f : B →+* D) (P A C : B) :
    f (genPhi P A C) = genPhi (f P) (f A) (f C) := by
  simp [genPhi]

@[simp] theorem map_genJ (f : B →+* D) (P A C : B) :
    f (genJ P A C) = genJ (f P) (f A) (f C) := by
  simp [genJ]

@[simp] theorem map_genV (f : B →+* D) (P A C : B) :
    f (genV P A C) = genV (f P) (f A) (f C) := by
  simp [genV]

@[simp] theorem map_genSig (f : B →+* D) (P A C : B) :
    f (genSig P A C) = genSig (f P) (f A) (f C) := by
  simp [genSig]

@[simp] theorem map_qgtPlus (f : B →+* D) (P A C : B) :
    f (qgtPlus P A C) = qgtPlus (f P) (f A) (f C) := by
  simp [qgtPlus]

@[simp] theorem map_qgtMinus (f : B →+* D) (P A C : B) :
    f (qgtMinus P A C) = qgtMinus (f P) (f A) (f C) := by
  simp [qgtMinus]

@[simp] theorem map_zetaFactor (f : B →+* D) (P A C : B) :
    f (zetaFactor P A C) = zetaFactor (f P) (f A) (f C) := by
  simp [zetaFactor]

@[simp] theorem map_zetaPlusFactor (f : B →+* D) (P A C : B) :
    f (zetaPlusFactor P A C) = zetaPlusFactor (f P) (f A) (f C) := by
  simp [zetaPlusFactor]

@[simp] theorem map_derivSqPhi (f : B →+* D) (P A C X : B) :
    f (derivSqPhi P A C X) = derivSqPhi (f P) (f A) (f C) (f X) := by
  simp [derivSqPhi]

@[simp] theorem map_derivSqJ (f : B →+* D) (P A C X : B) :
    f (derivSqJ P A C X) = derivSqJ (f P) (f A) (f C) (f X) := by
  simp [derivSqJ]

@[simp] theorem map_derivSqSig (f : B →+* D) (P A C X : B) :
    f (derivSqSig P A C X) = derivSqSig (f P) (f A) (f C) (f X) := by
  simp [derivSqSig]

@[simp] theorem map_hProjV (f : B →+* D) (P A C X : B) :
    f (hProjV P A C X) = hProjV (f P) (f A) (f C) (f X) := by
  simp [hProjV]

@[simp] theorem map_hProjPhi (f : B →+* D) (P A C X : B) :
    f (hProjPhi P A C X) = hProjPhi (f P) (f A) (f C) (f X) := by
  simp [hProjPhi]

@[simp] theorem map_hProjJ (f : B →+* D) (P A C X : B) :
    f (hProjJ P A C X) = hProjJ (f P) (f A) (f C) (f X) := by
  simp [hProjJ]

@[simp] theorem map_hProjSig (f : B →+* D) (P A C X : B) :
    f (hProjSig P A C X) = hProjSig (f P) (f A) (f C) (f X) := by
  simp [hProjSig]

theorem map_grading_add_phi (f : B →+* D) (P A C : B) :
    f (invS P + genPhi P A C) = invS (f P) + genPhi (f P) (f A) (f C) := by
  simp

theorem comp_grading_add_phi_sq (f : B →+* D) (g : D →+* E)
    {P : B} (hP : P * P = P) (A C : B) :
    (invS (g (f P)) + genPhi (g (f P)) (g (f A)) (g (f C))) *
      (invS (g (f P)) + genPhi (g (f P)) (g (f A)) (g (f C))) =
      zetaPlusFactor (g (f P)) (g (f A)) (g (f C)) :=
  grading_add_phi_sq (map_idempotent g (map_idempotent f hP)) _ _

end InfoGeometry.OperatorAlgebra.PeirceSpine
