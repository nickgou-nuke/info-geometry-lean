import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import Mathlib.Tactic

/-!
# Native alignment of the six Borel root automorphisms with PC normal-form words

The six Boolean words in this file are external discovery data only.  Every
stated equality is proved in Lean by explicit extensionality of the concrete
8×8 carrier matrices, followed by injectivity of `autMatrix`.

No CAS result, `native_decide`, custom axiom, or ambient group-order fact is
used as a proof object.
-/

namespace InfoGeometry.Algebra.Zorn.G2BorelRootPCWordAlignment

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate

/-- `[0,0,1,0,0,0]`. -/
def short1Exp : PCWordExp
  | 0 => false | 1 => false | 2 => true
  | 3 => false | 4 => false | 5 => false

/-- `[1,0,0,0,0,0]`. -/
def short2Exp : PCWordExp
  | 0 => true | 1 => false | 2 => false
  | 3 => false | 4 => false | 5 => false

/-- `[0,0,1,0,0,1]`. -/
def long2Exp : PCWordExp
  | 0 => false | 1 => false | 2 => true
  | 3 => false | 4 => false | 5 => true

/-- `[1,1,0,0,1,0]`. -/
def short3Exp : PCWordExp
  | 0 => true | 1 => true | 2 => false
  | 3 => false | 4 => true | 5 => false

/-- `[0,1,1,0,0,0]`. -/
def long3Exp : PCWordExp
  | 0 => false | 1 => true | 2 => true
  | 3 => false | 4 => false | 5 => false

/-- `[0,1,0,1,0,0]`. -/
def long4Exp : PCWordExp
  | 0 => false | 1 => true | 2 => false
  | 3 => true | 4 => false | 5 => false

/-! ## Explicit matrix owners

These are the kernel-level bridge.  `rootAut` is noncomputable, so the proof is
not by evaluation of the whole automorphism.  Instead each matrix is extensional
on its 64 entries; after fixing row and column, the concrete basis action
reduces definitionally.
-/

theorem autMatrix_rootAut_short1_eq_pcWord :
    autMatrix (rootAut (RootLength.Short, (1 : ZMod 6))) =
      autMatrix (pcWord short1Exp) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem autMatrix_rootAut_short2_eq_pcWord :
    autMatrix (rootAut (RootLength.Short, (2 : ZMod 6))) =
      autMatrix (pcWord short2Exp) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem autMatrix_rootAut_long2_eq_pcWord :
    autMatrix (rootAut (RootLength.Long, (2 : ZMod 6))) =
      autMatrix (pcWord long2Exp) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem autMatrix_rootAut_short3_eq_pcWord :
    autMatrix (rootAut (RootLength.Short, (3 : ZMod 6))) =
      autMatrix (pcWord short3Exp) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem autMatrix_rootAut_long3_eq_pcWord :
    autMatrix (rootAut (RootLength.Long, (3 : ZMod 6))) =
      autMatrix (pcWord long3Exp) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem autMatrix_rootAut_long4_eq_pcWord :
    autMatrix (rootAut (RootLength.Long, (4 : ZMod 6))) =
      autMatrix (pcWord long4Exp) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ## Concrete automorphism equalities -/

theorem rootAut_short1_eq_pcWord :
    rootAut (RootLength.Short, (1 : ZMod 6)) = pcWord short1Exp := by
  apply autMatrix_injective
  exact autMatrix_rootAut_short1_eq_pcWord

theorem rootAut_short2_eq_pcWord :
    rootAut (RootLength.Short, (2 : ZMod 6)) = pcWord short2Exp := by
  apply autMatrix_injective
  exact autMatrix_rootAut_short2_eq_pcWord

theorem rootAut_long2_eq_pcWord :
    rootAut (RootLength.Long, (2 : ZMod 6)) = pcWord long2Exp := by
  apply autMatrix_injective
  exact autMatrix_rootAut_long2_eq_pcWord

theorem rootAut_short3_eq_pcWord :
    rootAut (RootLength.Short, (3 : ZMod 6)) = pcWord short3Exp := by
  apply autMatrix_injective
  exact autMatrix_rootAut_short3_eq_pcWord

theorem rootAut_long3_eq_pcWord :
    rootAut (RootLength.Long, (3 : ZMod 6)) = pcWord long3Exp := by
  apply autMatrix_injective
  exact autMatrix_rootAut_long3_eq_pcWord

theorem rootAut_long4_eq_pcWord :
    rootAut (RootLength.Long, (4 : ZMod 6)) = pcWord long4Exp := by
  apply autMatrix_injective
  exact autMatrix_rootAut_long4_eq_pcWord

/-- All six concrete Borel root automorphisms lie in the PC-word image. -/
theorem six_borel_roots_mem_pcWord_range :
    rootAut (RootLength.Short, (1 : ZMod 6)) ∈ Set.range pcWord ∧
    rootAut (RootLength.Short, (2 : ZMod 6)) ∈ Set.range pcWord ∧
    rootAut (RootLength.Long,  (2 : ZMod 6)) ∈ Set.range pcWord ∧
    rootAut (RootLength.Short, (3 : ZMod 6)) ∈ Set.range pcWord ∧
    rootAut (RootLength.Long,  (3 : ZMod 6)) ∈ Set.range pcWord ∧
    rootAut (RootLength.Long,  (4 : ZMod 6)) ∈ Set.range pcWord := by
  exact ⟨⟨short1Exp, rootAut_short1_eq_pcWord.symm⟩,
    ⟨short2Exp, rootAut_short2_eq_pcWord.symm⟩,
    ⟨long2Exp, rootAut_long2_eq_pcWord.symm⟩,
    ⟨short3Exp, rootAut_short3_eq_pcWord.symm⟩,
    ⟨long3Exp, rootAut_long3_eq_pcWord.symm⟩,
    ⟨long4Exp, rootAut_long4_eq_pcWord.symm⟩⟩

end InfoGeometry.Algebra.Zorn.G2BorelRootPCWordAlignment
