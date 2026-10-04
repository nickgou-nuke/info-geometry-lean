import InfoGeometry.Lie.CanonicalZornG2BasisAlignment
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Lie.CanonicalZornG2CASReplay

open InfoGeometry.Lie.CanonicalZornG2CASData
open InfoGeometry.Lie.CanonicalZornG2BasisAlignment
open InfoGeometry.Lie.SplitOctonionEllClosedFlow
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Lie.CanonicalZornDerivationDimension

def ratToReal (X : ZornVectorMatrix ℚ) : ZornVectorMatrix ℝ :=
  ⟨X.a, fun i => X.v i, fun i => X.w i, X.b⟩

theorem rationalParameterAction_cast (p : Fin 14 → ℚ)
    (X : ZornVectorMatrix ℚ) :
    ratToReal
        (InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.rationalParameterAction p X) =
      parameterAction (fun i => (p i : ℝ)) (ratToReal X) := by
  apply ZornVectorMatrix.ext
  · simp [ratToReal,
      InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.rationalParameterAction,
      parameterAction]

  · funext i
    fin_cases i <;>
      simp [ratToReal,
        InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.rationalParameterAction,
        parameterAction] <;>
      norm_num
  · funext i
    fin_cases i <;>
      simp [ratToReal,
        InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.rationalParameterAction,
        parameterAction] <;>
      norm_num
  · simp [ratToReal,
      InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.rationalParameterAction,
      parameterAction]

def casBracket (i j : Fin 14) : Matrix (Fin 8) (Fin 8) ℚ :=
  casBasisMatrix i * casBasisMatrix j - casBasisMatrix j * casBasisMatrix i

def casBracketExpansion (i j : Fin 14) : Matrix (Fin 8) (Fin 8) ℚ :=
  ∑ k : Fin 14, casStructureConstant i j k • casBasisMatrix k

theorem casBracket_eq_structure_constants (i j : Fin 14) :
    casBracket i j = casBracketExpansion i j := by
  fin_cases i <;> fin_cases j <;> native_decide

end InfoGeometry.Lie.CanonicalZornG2CASReplay
