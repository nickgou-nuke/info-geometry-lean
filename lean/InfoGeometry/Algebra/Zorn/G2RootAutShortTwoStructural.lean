import InfoGeometry.Algebra.Zorn.G2RootAutRotationBridge
import InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
import Mathlib.Tactic

/-!
# Structural second short-root / PC-word alignment

This file derives the `Short(2)` root-to-PC identity from the already verified
`Short(1)` identity and Coxeter rotation.  The only new finite carrier check is
on the PC side:

`c * pc3Aut * c⁻¹ = pc1Aut`.

Thus `rootAut (Short, 2)` is not unfolded or re-enumerated.  The root-side step
is supplied entirely by `c_rootAut_c` through `G2RootAutRotationBridge`.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootAutShortTwoStructural

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2RootAutRotationBridge
open InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-- The PC exponent `[1,0,0,0,0,0]`. -/
def shortTwoPCExp : PCWordExp := oneAt 0

/-- The canonical word `[1,0,0,0,0,0]` is `pc1Aut`. -/
theorem pcWord_shortTwoPCExp_eq_pc1Aut :
    pcWord shortTwoPCExp = pc1Aut := by
  dsimp [shortTwoPCExp]
  simpa [pcGenerator] using pcWord_oneAt_eq_generator (0 : Fin 6)

/-- Pure PC-carrier matrix check for Coxeter conjugation of `pc3Aut`. -/
theorem autMatrix_c_conj_pc3Aut_eq_C0 :
    autMatrix (c * pc3Aut * c⁻¹) = C0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Coxeter rotation sends the first short-root PC word to the second one. -/
theorem c_conj_pc3Aut_eq_pc1Aut :
    c * pc3Aut * c⁻¹ = pc1Aut := by
  apply autMatrix_injective
  calc
    autMatrix (c * pc3Aut * c⁻¹) = C0 := autMatrix_c_conj_pc3Aut_eq_C0
    _ = autMatrix pc1Aut := autMatrix_pc1Aut_eq_C0.symm

/-- Second short-root / PC-word equality, obtained structurally from `Short(1)`. -/
theorem rootAut_short_two_eq_pcWord_structural :
    rootAut (RootLength.Short, (2 : ZMod 6)) = pcWord shortTwoPCExp := by
  calc
    rootAut (RootLength.Short, (2 : ZMod 6)) =
        c * rootAut (RootLength.Short, (1 : ZMod 6)) * c⁻¹ :=
      rootAut_short_two_eq_c_conj_short_one
    _ = c * pc3Aut * c⁻¹ := by
      rw [rootAut_short_one_eq_pcWord, pcWord_shortOnePCExp_eq_pc3Aut]
    _ = pc1Aut := c_conj_pc3Aut_eq_pc1Aut
    _ = pcWord shortTwoPCExp := pcWord_shortTwoPCExp_eq_pc1Aut.symm

end InfoGeometry.Algebra.Zorn.G2RootAutShortTwoStructural
