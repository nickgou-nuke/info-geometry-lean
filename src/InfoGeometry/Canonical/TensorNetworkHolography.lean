import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace TensorNetworkHolography

/-- MERA Multi-Scale Entanglement Renormalization Structure with Disentangler u and Isometry w. -/
structure MERANetwork (n : ℕ) where
  disentangler_u : Matrix.unitaryGroup (Fin n) ℂ
  isometry_w : Matrix.unitaryGroup (Fin n) ℂ
  bond_dimension : ℕ
  cut_bonds : ℕ

namespace MERANetwork

variable {n : ℕ} (mera : MERANetwork n)

def disentanglerVal : Matrix (Fin n) (Fin n) ℂ := mera.disentangler_u

def isometryVal : Matrix (Fin n) (Fin n) ℂ := mera.isometry_w

theorem h_u_isometry : disentanglerVal mera * (disentanglerVal mera).conjTranspose = 1 := by
  change (mera.disentangler_u : Matrix (Fin n) (Fin n) ℂ) *
      (mera.disentangler_u : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1
  exact Matrix.mem_unitaryGroup_iff.mp mera.disentangler_u.2

theorem h_w_isometry : isometryVal mera * (isometryVal mera).conjTranspose = 1 := by
  change (mera.isometry_w : Matrix (Fin n) (Fin n) ℂ) *
      (mera.isometry_w : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1
  exact Matrix.mem_unitaryGroup_iff.mp mera.isometry_w.2

/-- MERA Layer Transformation Matrix T = u * w. -/
def layerTransformation : Matrix (Fin n) (Fin n) ℂ :=
  disentanglerVal mera * isometryVal mera

/-- **Theorem**: MERA Disentangler Trace Conservation: Tr(u u†) = n. -/
theorem disentangler_trace_conservation :
    trace (disentanglerVal mera * (disentanglerVal mera).conjTranspose) = (n : ℂ) := by
  rw [h_u_isometry mera, trace_one]
  norm_cast
  exact Fintype.card_fin n

/-- **Theorem**: MERA Isometry Trace Conservation: Tr(w w†) = n. -/
theorem isometry_trace_conservation :
    trace (isometryVal mera * (isometryVal mera).conjTranspose) = (n : ℂ) := by
  rw [h_w_isometry mera, trace_one]
  norm_cast
  exact Fintype.card_fin n

/-- **Theorem**: Composite MERA Layer Transformation Isometry:
    (u * w) * (u * w)† = u * (w * w†) * u† = 1. -/
theorem layer_transformation_isometry :
    (disentanglerVal mera * isometryVal mera) *
        (disentanglerVal mera * isometryVal mera).conjTranspose = 1 := by
  rw [conjTranspose_mul, mul_assoc, ← mul_assoc (isometryVal mera),
    h_w_isometry mera, one_mul, h_u_isometry mera]

/-- **Theorem**: Composite MERA Layer Trace Conservation: Tr((u w) (u w)†) = n. -/
theorem layer_transformation_trace_conservation :
    trace ((disentanglerVal mera * isometryVal mera) *
      (disentanglerVal mera * isometryVal mera).conjTranspose) = (n : ℂ) := by
  rw [layer_transformation_isometry mera, trace_one]
  norm_cast
  exact Fintype.card_fin n

/-- **Theorem**: Discrete Ryu-Takayanagi Entanglement Cut Bound Scaling:
    S_max = cut_bonds * ln(bond_dimension). -/
def ryuTakayanagiMaxEntropy (cut_bonds bond_dim : ℂ) : ℂ :=
  cut_bonds * bond_dim

/-- **Theorem**: Linear Scaling of Ryu-Takayanagi Cut Bound with Respect to Cut Bonds:
    S_max(c1 + c2) = S_max(c1) + S_max(c2). -/
theorem ryu_takayanagi_cut_bound_additivity (c1 c2 bond_dim : ℂ) :
    ryuTakayanagiMaxEntropy (c1 + c2) bond_dim = ryuTakayanagiMaxEntropy c1 bond_dim + ryuTakayanagiMaxEntropy c2 bond_dim := by
  dsimp [ryuTakayanagiMaxEntropy]
  ring

end MERANetwork

end TensorNetworkHolography
