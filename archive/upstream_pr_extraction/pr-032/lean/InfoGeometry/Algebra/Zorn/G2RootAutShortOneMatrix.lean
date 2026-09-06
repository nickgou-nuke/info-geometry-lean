import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
import Mathlib.Tactic

/-!
# Native matrix owner for the first positive-root / PC-word alignment

This file proves the first concrete matrix identity needed to align the
Chevalley root realization with the existing polycyclic normal form.
No CAS result is imported as a theorem: the root-side matrix is reduced
kernel-side from the concrete automorphism definitions, and the PC side uses
the existing native matrix certificate `C3`.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-- The PC exponent `[0,0,0,1,0,0]`. -/
def shortOnePCExp : PCWordExp := oneAt 3

/-- Native 8×8 matrix of the concrete short root at Coxeter position `1`. -/
theorem autMatrix_rootAut_short_one_eq_C3 :
    autMatrix (rootAut (RootLength.Short, (1 : ZMod 6))) = C3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The canonical PC word `[0,0,0,1,0,0]` is the fourth PC generator. -/
theorem pcWord_shortOnePCExp_eq_pc4Aut :
    pcWord shortOnePCExp = pc4Aut := by
  dsimp [shortOnePCExp]
  simpa [pcGenerator] using pcWord_oneAt_eq_generator (3 : Fin 6)

/-- Matrix form of the first root/PC-word alignment. -/
theorem autMatrix_rootAut_short_one_eq_pcWord :
    autMatrix (rootAut (RootLength.Short, (1 : ZMod 6))) =
      autMatrix (pcWord shortOnePCExp) := by
  rw [autMatrix_rootAut_short_one_eq_C3,
    pcWord_shortOnePCExp_eq_pc4Aut,
    autMatrix_pc4Aut_eq_C3]

/-- First native root/PC-word equality. -/
theorem rootAut_short_one_eq_pcWord :
    rootAut (RootLength.Short, (1 : ZMod 6)) = pcWord shortOnePCExp := by
  apply autMatrix_injective
  exact autMatrix_rootAut_short_one_eq_pcWord

end InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
