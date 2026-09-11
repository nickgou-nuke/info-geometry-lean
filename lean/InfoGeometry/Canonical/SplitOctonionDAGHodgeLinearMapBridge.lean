import Mathlib.LinearAlgebra.Matrix.ToLin
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionDAGHodgeIntertwinerBridge

/-!
# Native linear-map transport for the conditional DAG/exterior bridge

The matrix owner `SplitOctonionDAGHodgeIntertwinerBridge` supplies an explicit
finite `8 × 8` intertwiner datum.  This file transports exactly that datum to
native `Module.End` objects.  It does not manufacture a map from an arbitrary
repository `TwoComplex` to the split-octonion carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionDAGHodgeLinearMapBridge

open Matrix
open InfoGeometry.Canonical.SplitOctonionDAGHodgeIntertwinerBridge
open InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge

abbrev End8 := Module.End ℝ (Fin 8 → ℝ)

abbrev DAGMat8 :=
  InfoGeometry.Canonical.SplitOctonionDAGHodgeIntertwinerBridge.Mat8

def dEnd (H : DAGHodgeDatum) : End8 := Matrix.toLin' H.d

def deltaEnd (H : DAGHodgeDatum) : End8 := Matrix.toLin' H.delta

def diracEnd (H : DAGHodgeDatum) : End8 := Matrix.toLin' H.dirac

def laplacianEnd (H : DAGHodgeDatum) : End8 := Matrix.toLin' H.laplacian

def exteriorDEnd : End8 := Matrix.toLin' eps0Mat

def exteriorDeltaEnd : End8 := Matrix.toLin' iota0Mat

def exteriorDiracEnd : End8 := Matrix.toLin' exteriorDiracMat

def exteriorLaplacianEnd : End8 := Matrix.toLin' exteriorLaplacianMat

def intertwinerEnd {H : DAGHodgeDatum}
    (I : DAGSplitOctonionIntertwiner H) : End8 := Matrix.toLin' I.F

theorem intertwiner_d_native {H : DAGHodgeDatum}
    (I : DAGSplitOctonionIntertwiner H) :
    intertwinerEnd I * dEnd H = exteriorDEnd * intertwinerEnd I := by
  have h := congrArg
    (Matrix.toLin' : DAGMat8 → End8) I.intertwine_d
  simpa [intertwinerEnd, dEnd, exteriorDEnd, Matrix.toLin'_mul] using h

theorem intertwiner_delta_native {H : DAGHodgeDatum}
    (I : DAGSplitOctonionIntertwiner H) :
    intertwinerEnd I * deltaEnd H =
      exteriorDeltaEnd * intertwinerEnd I := by
  have h := congrArg
    (Matrix.toLin' : DAGMat8 → End8) I.intertwine_delta
  simpa [intertwinerEnd, deltaEnd, exteriorDeltaEnd, Matrix.toLin'_mul] using h

theorem intertwiner_dirac_native {H : DAGHodgeDatum}
    (I : DAGSplitOctonionIntertwiner H) :
    intertwinerEnd I * diracEnd H =
      exteriorDiracEnd * intertwinerEnd I := by
  have h := congrArg
    (Matrix.toLin' : DAGMat8 → End8) (intertwiner_dirac I)
  simpa [intertwinerEnd, diracEnd, exteriorDiracEnd,
    DAGHodgeDatum.dirac, exteriorDiracMat, Matrix.toLin'_mul] using h

theorem intertwiner_laplacian_native {H : DAGHodgeDatum}
    (I : DAGSplitOctonionIntertwiner H) :
    intertwinerEnd I * laplacianEnd H =
      exteriorLaplacianEnd * intertwinerEnd I := by
  have h := congrArg
    (Matrix.toLin' : DAGMat8 → End8) (intertwiner_laplacian I)
  simpa [intertwinerEnd, laplacianEnd, exteriorLaplacianEnd,
    DAGHodgeDatum.laplacian, Matrix.toLin'_mul] using h

theorem canonical_identity_dirac_native :
    intertwinerEnd canonicalIdentityIntertwiner *
        diracEnd canonicalExteriorHodgeDatum =
      exteriorDiracEnd * intertwinerEnd canonicalIdentityIntertwiner := by
  exact intertwiner_dirac_native canonicalIdentityIntertwiner

theorem canonical_identity_laplacian_native :
    intertwinerEnd canonicalIdentityIntertwiner *
        laplacianEnd canonicalExteriorHodgeDatum =
      exteriorLaplacianEnd * intertwinerEnd canonicalIdentityIntertwiner := by
  exact intertwiner_laplacian_native canonicalIdentityIntertwiner

end InfoGeometry.Canonical.SplitOctonionDAGHodgeLinearMapBridge
