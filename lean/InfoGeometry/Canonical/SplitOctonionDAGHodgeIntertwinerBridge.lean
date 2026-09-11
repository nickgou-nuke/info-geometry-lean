import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge

/-!
# DAG/Split-Octonion Hodge Intertwiner Contract

This module records a finite matrix-level intertwiner contract. It does not
identify the repository's concrete DAG carrier with the split-octonion carrier;
the datum below supplies the matrix operators and an intertwiner as hypotheses.
Thus the results are conditional transport lemmas, not a canonical
DAG-to-split-octonion construction.

1. **Chain complex operators**:
   - $d_{\rm DAG} : C_k \to C_{k+1}$ (discrete boundary / coboundary)
   - $\delta_{\rm DAG} : C_{k+1} \to C_k$ (discrete adjoint)
   - $D_{\rm DAG} := d_{\rm DAG} + \delta_{\rm DAG}$ (discrete Dirac operator)
   - $\Delta_{\rm DAG} := D_{\rm DAG}^2 = d_{\rm DAG} \delta_{\rm DAG} + \delta_{\rm DAG} d_{\rm DAG}$ (discrete Hodge Laplacian)

2. **Exterior / Split-octonion operators**:
   - $d_{\rm ext} := \varepsilon_0$ (creation / wedge)
   - $\delta_{\rm ext} := \iota_0$ (contraction / interior product)
   - $D_{\rm ext} := \varepsilon_0 + \iota_0$ (exterior Hodge–Dirac)
   - $\Delta_{\rm ext} := D_{\rm ext}^2 = \varepsilon_0 \iota_0 + \iota_0 \varepsilon_0 = I$ (Hodge Laplacian / CAR unit)

3. **🏆 THEOREM 1 (Boundary / Coboundary Intertwining)**:
   - $F \circ d_{\rm DAG} = \varepsilon_0 \circ F$
   - $F \circ \delta_{\rm DAG} = \iota_0 \circ F$

4. **🏆 THEOREM 2 (Hodge–Dirac & Laplacian Intertwining)**:
   - $F \circ D_{\rm DAG} = D_{\rm ext} \circ F$
   - $F \circ \Delta_{\rm DAG} = \Delta_{\rm ext} \circ F$
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionDAGHodgeIntertwinerBridge

open Matrix
open InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge

abbrev Mat8 := InfoGeometry.Algebra.FiniteSpin.Mat8R

/-- The exterior Hodge–Dirac matrix $D_{\rm ext} = \varepsilon_0 + \iota_0$. -/
def exteriorDiracMat : Mat8 :=
  eps0Mat + iota0Mat

/-- The exterior Hodge Laplacian matrix $\Delta_{\rm ext} = D_{\rm ext}^2 = I$. -/
def exteriorLaplacianMat : Mat8 :=
  exteriorDiracMat * exteriorDiracMat

/-- 🏆 THEOREM: Exterior Hodge Laplacian evaluates to identity $I_8$. -/
theorem exteriorLaplacianMat_eq_one : exteriorLaplacianMat = 1 := by
  dsimp [exteriorLaplacianMat, exteriorDiracMat]
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, Matrix.add_apply, eps0Mat, iota0Mat, Fin.sum_univ_eight]
  )

/-- An explicit DAG Hodge datum consisting of nilpotent $d$ and adjoint $\delta$. -/
structure DAGHodgeDatum where
  d : Mat8
  delta : Mat8
  d_sq : d * d = 0
  delta_sq : delta * delta = 0

/-- The discrete Dirac operator $D = d + \delta$. -/
def DAGHodgeDatum.dirac (H : DAGHodgeDatum) : Mat8 :=
  H.d + H.delta

/-- The discrete Hodge Laplacian $\Delta = D^2$. -/
def DAGHodgeDatum.laplacian (H : DAGHodgeDatum) : Mat8 :=
  H.dirac * H.dirac

/-- An explicit intertwiner matrix $F$ commuting with the boundary operators. -/
structure DAGSplitOctonionIntertwiner (H : DAGHodgeDatum) where
  F : Mat8
  intertwine_d : F * H.d = eps0Mat * F
  intertwine_delta : F * H.delta = iota0Mat * F

/-- 🏆 THEOREM 1: The intertwiner intertwines the full Hodge–Dirac operator:
    $F \circ D_{\rm DAG} = D_{\rm ext} \circ F$. -/
theorem intertwiner_dirac {H : DAGHodgeDatum} (I : DAGSplitOctonionIntertwiner H) :
    I.F * H.dirac = exteriorDiracMat * I.F := by
  have hd := I.intertwine_d
  have hdelta := I.intertwine_delta
  dsimp [DAGHodgeDatum.dirac, exteriorDiracMat]
  rw [Matrix.mul_add, Matrix.add_mul, hd, hdelta]

/-- 🏆 THEOREM 2: The intertwiner intertwines the Hodge Laplacian:
    $F \circ \Delta_{\rm DAG} = \Delta_{\rm ext} \circ F$. -/
theorem intertwiner_laplacian {H : DAGHodgeDatum} (I : DAGSplitOctonionIntertwiner H) :
    I.F * H.laplacian = exteriorLaplacianMat * I.F := by
  have hdirac := intertwiner_dirac I
  dsimp [DAGHodgeDatum.laplacian, exteriorLaplacianMat]
  calc I.F * (H.dirac * H.dirac)
    _ = (I.F * H.dirac) * H.dirac := by rw [Matrix.mul_assoc]
    _ = (exteriorDiracMat * I.F) * H.dirac := by rw [hdirac]
    _ = exteriorDiracMat * (I.F * H.dirac) := by rw [← Matrix.mul_assoc]
    _ = exteriorDiracMat * (exteriorDiracMat * I.F) := by rw [hdirac]
    _ = (exteriorDiracMat * exteriorDiracMat) * I.F := by rw [Matrix.mul_assoc]

/-- Canonical realization: The standard exterior Hodge complex is its own canonical intertwiner. -/
def canonicalExteriorHodgeDatum : DAGHodgeDatum where
  d := eps0Mat
  delta := iota0Mat
  d_sq := eps0Mat_sq
  delta_sq := iota0Mat_sq

def canonicalIdentityIntertwiner : DAGSplitOctonionIntertwiner canonicalExteriorHodgeDatum where
  F := 1
  intertwine_d := by
    dsimp [canonicalExteriorHodgeDatum]
    simp
  intertwine_delta := by
    dsimp [canonicalExteriorHodgeDatum]
    simp

@[simp] theorem canonicalExteriorHodgeDatum_laplacian_eq_one :
    canonicalExteriorHodgeDatum.laplacian = 1 := by
  dsimp [DAGHodgeDatum.laplacian, DAGHodgeDatum.dirac,
    canonicalExteriorHodgeDatum]
  exact exteriorLaplacianMat_eq_one

end InfoGeometry.Canonical.SplitOctonionDAGHodgeIntertwinerBridge
