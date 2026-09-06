import InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment
import InfoGeometry.Algebra.Zorn.G2RootAutPC4Conjugation
import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2UnipotentRootSubgroup

/-!
# Native matrix owner for the first positive-root / PC-word alignment

This file proves the first concrete matrix identity needed to align the
Chevalley root realization with the existing polycyclic normal form.
No CAS result is imported as a theorem: the root-side matrix is reduced
kernel-side from the concrete automorphism definitions, and the PC side uses
the existing native matrix certificate `C2`.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2Unipotent

/-- The PC exponent `[0,0,1,0,0,0]`. -/
def shortOnePCExp : PCWordExp := oneAt 2

/-- Native 8×8 matrix of the concrete short root at Coxeter position `1`. -/
theorem autMatrix_rootAut_short_one_eq_C2 :
    autMatrix (rootAut (RootLength.Short, (1 : ZMod 6))) = C2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The canonical PC word `[0,0,1,0,0,0]` is the third PC generator. -/
theorem pcWord_shortOnePCExp_eq_pc3Aut :
    pcWord shortOnePCExp = pc3Aut := by
  dsimp [shortOnePCExp]
  simpa [pcGenerator] using pcWord_oneAt_eq_generator (2 : Fin 6)

/-- Matrix form of the first root/PC-word alignment. -/
theorem autMatrix_rootAut_short_one_eq_pcWord :
    autMatrix (rootAut (RootLength.Short, (1 : ZMod 6))) =
      autMatrix (pcWord shortOnePCExp) := by
  rw [autMatrix_rootAut_short_one_eq_C2,
    pcWord_shortOnePCExp_eq_pc3Aut,
    autMatrix_pc3Aut_eq_C2]

/-- First native root/PC-word equality. -/
theorem rootAut_short_one_eq_pcWord :
    rootAut (RootLength.Short, (1 : ZMod 6)) = pcWord shortOnePCExp := by
  apply autMatrix_injective
  exact autMatrix_rootAut_short_one_eq_pcWord

def shortOneCorrectedPCExp : Fin 6 → Bool := oneAt 3

private theorem autMatrix_cycle012_native :
    autMatrix cycle012Aut = cycle012Matrix := by
  apply matrix_eq_of_action_eq
  intro X
  rw [autMatrix_action, cycle012Matrix_action, cycle012Aut_apply]

private theorem autMatrix_swapCartan_native :
    autMatrix swapCartanAut = swapCartanMatrix := by
  apply matrix_eq_of_action_eq
  intro X
  rw [autMatrix_action, swapCartanMatrix_action]
  rfl

private theorem autMatrix_c :
    autMatrix c = cycle012Matrix * swapCartanMatrix := by
  rw [c, autMatrix_mul, autMatrix_cycle012Matrix,
    autMatrix_swapCartanMatrix]

private theorem autMatrix_c_pow_five :
    autMatrix (c ^ 5) =
      autMatrix swapCartanAut *
        (autMatrix cycle012Aut * autMatrix cycle012Aut) := by
  rw [c_pow_five_eq_swapCartan_mul_cycle_sq]
  rw [autMatrix_mul, autMatrix_mul]
  rw [autMatrix_swapCartan_native, autMatrix_cycle012_native]
  have hcomm : cycle012Matrix * swapCartanMatrix =
      swapCartanMatrix * cycle012Matrix := by
    have h := congrArg autMatrix swapCartanAut_comm_cycle012
    simpa [autMatrix_mul, autMatrix_swapCartan_native,
      autMatrix_cycle012_native] using h
  calc
    cycle012Matrix * cycle012Matrix * swapCartanMatrix =
        cycle012Matrix * (cycle012Matrix * swapCartanMatrix) :=
      mul_assoc _ _ _
    _ = cycle012Matrix * (swapCartanMatrix * cycle012Matrix) :=
      congrArg (fun M => cycle012Matrix * M) hcomm
    _ = (cycle012Matrix * swapCartanMatrix) * cycle012Matrix :=
      (mul_assoc _ _ _).symm
    _ = swapCartanMatrix * (cycle012Matrix * cycle012Matrix) := by
      rw [hcomm, mul_assoc]

set_option maxHeartbeats 1000000 in
theorem autMatrix_rootAut_short_one_eq_correctedPCWord :
    autMatrix (rootAut (RootLength.Short, (1 : ZMod 6))) =
      autMatrix (G2TwoSylowSubgroup.pcWord shortOneCorrectedPCExp) := by
  dsimp [shortOneCorrectedPCExp]
  rw [pcWord_oneAt_eq_generator, pcGenerator.eq_def,
    autMatrix_pc4Aut_eq_C3]
  dsimp [rootAut]
  rw [autMatrix_mul, autMatrix_mul]
  change autMatrix c⁻¹ * (autMatrix S0 * autMatrix c) = C3
  rw [G2RootAutMatrixAlignment.c_inv_eq_c_pow_five,
    autMatrix_c_pow_five]
  change autMatrix swapCartanAut *
      (autMatrix cycle012Aut * autMatrix cycle012Aut) *
      (autMatrix (unipotentShortAut true) * autMatrix c) = C3
  rw [autMatrix_shortRootMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem rootAut_short_one_eq_correctedPCWord :
    rootAut (RootLength.Short, (1 : ZMod 6)) =
      G2TwoSylowSubgroup.pcWord shortOneCorrectedPCExp := by
  apply autMatrix_injective
  exact autMatrix_rootAut_short_one_eq_correctedPCWord

theorem rootAut_short_two_eq_c_conjugate :
    rootAut (RootLength.Short, (2 : ZMod 6)) =
      c * rootAut (RootLength.Short, (1 : ZMod 6)) * c⁻¹ := by
  simpa [G2TwoRootSystem.cAction] using
    (G2TwoRootSystem.c_rootAut_c
      (RootLength.Short, (1 : ZMod 6))).symm

def shortTwoCorrectedPCExp : Fin 6 → Bool := oneAt 5

set_option maxHeartbeats 1000000 in
theorem autMatrix_c_conjugate_pc4_eq_pc6 :
    autMatrix (c * G2TwoSylowPCAutomorphisms.pc4Aut * c⁻¹) =
      autMatrix G2TwoSylowPCAutomorphisms.pc6Aut := by
  rw [G2RootAutPC4Conjugation.autMatrix_c_conj_pc4_eq_C5,
    G2TwoPCMatrixCertificate.autMatrix_pc6Aut_eq_C5]

theorem autMatrix_rootAut_short_two_eq_correctedPCWord :
    autMatrix (rootAut (RootLength.Short, (2 : ZMod 6))) =
      autMatrix (G2TwoSylowSubgroup.pcWord shortTwoCorrectedPCExp) := by
  dsimp [shortTwoCorrectedPCExp]
  rw [pcWord_oneAt_eq_generator, pcGenerator.eq_def]
  rw [rootAut_short_two_eq_c_conjugate,
    rootAut_short_one_eq_correctedPCWord]
  exact autMatrix_c_conjugate_pc4_eq_pc6

theorem rootAut_short_two_eq_correctedPCWord :
    rootAut (RootLength.Short, (2 : ZMod 6)) =
      G2TwoSylowSubgroup.pcWord shortTwoCorrectedPCExp := by
  apply autMatrix_injective
  exact autMatrix_rootAut_short_two_eq_correctedPCWord

theorem rootAut_short_three_eq_c_conjugate :
    rootAut (RootLength.Short, (3 : ZMod 6)) =
      c * rootAut (RootLength.Short, (2 : ZMod 6)) * c⁻¹ := by
  simpa [G2TwoRootSystem.cAction] using
    (G2TwoRootSystem.c_rootAut_c
      (RootLength.Short, (2 : ZMod 6))).symm

set_option maxHeartbeats 1000000 in
theorem autMatrix_c_conjugate_pc6_eq_pc2_pc5_pc6 :
    autMatrix (c * G2TwoSylowPCAutomorphisms.pc6Aut * c⁻¹) =
      autMatrix (G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc5Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut) := by
  rw [autMatrix_mul, autMatrix_mul]
  conv_rhs => rw [autMatrix_mul, autMatrix_mul]
  rw [
    G2RootAutMatrixAlignment.c_inv_eq_c_pow_five,
    G2RootAutMatrixAlignment.autMatrix_c_pow,
    G2RootAutMatrixAlignment.autMatrix_c,
    G2TwoPCMatrixCertificate.autMatrix_pc6Aut_eq_C5,
    G2TwoPCMatrixCertificate.autMatrix_pc5Aut_eq_C4,
    G2TwoPCMatrixCertificate.autMatrix_pc2Aut_eq_C1]
  native_decide

theorem rootAut_short_three_eq_pcWord :
    rootAut (RootLength.Short, (3 : ZMod 6)) =
      G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc5Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut := by
  rw [rootAut_short_three_eq_c_conjugate,
    rootAut_short_two_eq_correctedPCWord]
  apply autMatrix_injective
  exact autMatrix_c_conjugate_pc6_eq_pc2_pc5_pc6

end InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
