import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DiscreteDiracKahlerOperator
import InfoGeometry.Canonical.ZornVectorMatrixRationalEquiv

namespace InfoGeometry.Canonical

def nullRayPlus (iElem liElem : StandardIntegralSplitOctonion) :
    StandardIntegralSplitOctonion :=
  fun r => iElem r + liElem r

def nullRayMinus (iElem liElem : StandardIntegralSplitOctonion) :
    StandardIntegralSplitOctonion :=
  fun r => iElem r - liElem r

def chiralProjectorPlus : StandardRationalSplitOctonion :=
  fun r => if r = .one then (1 / 2 : ℚ) else if r = .l then (1 / 2 : ℚ) else 0

def chiralProjectorMinus : StandardRationalSplitOctonion :=
  fun r => if r = .one then (1 / 2 : ℚ) else if r = .l then (-1 / 2 : ℚ) else 0

theorem null_ray_sq_zero
    (iElem liElem : StandardIntegralSplitOctonion)
    (hISq : splitOctonionMul iElem iElem = (fun _ => -1))
    (hLISq : splitOctonionMul liElem liElem = (fun _ => 1))
    (hAntiComm : splitOctonionMul iElem liElem =
      (fun r => -splitOctonionMul liElem iElem r))
    (hBilinear : ∀ a b c d : StandardIntegralSplitOctonion,
      splitOctonionMul (fun r => a r + b r) (fun r => c r + d r) =
        fun r => splitOctonionMul a c r + splitOctonionMul a d r +
          splitOctonionMul b c r + splitOctonionMul b d r) :
    splitOctonionMul (nullRayPlus iElem liElem) (nullRayPlus iElem liElem) =
      (fun _ => 0) := by
  rw [show nullRayPlus iElem liElem = (fun r => iElem r + liElem r) by rfl]
  rw [hBilinear iElem liElem iElem liElem]
  rw [hISq, hLISq, hAntiComm]
  ext r
  simp

theorem chiral_sector_associator_zero
    (a b c : StandardIntegralSplitOctonion)
    (hAssoc : splitOctonionMul a (splitOctonionMul b c) =
      splitOctonionMul (splitOctonionMul a b) c) :
    (fun r => splitOctonionMul a (splitOctonionMul b c) r -
      splitOctonionMul (splitOctonionMul a b) c r) = (fun _ => 0) := by
  rw [hAssoc]
  funext r
  simp

end InfoGeometry.Canonical
