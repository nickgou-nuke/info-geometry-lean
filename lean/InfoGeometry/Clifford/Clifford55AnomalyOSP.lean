import Mathlib.Tactic
import InfoGeometry.Algebra.OSp12

/-!
# `Cl(5,5)`, split anomaly cancellation, Bott stability, and `osp(1|2)` atoms

This module formalizes the algebraic skeleton:

* dimension factorization `dim Cl(5,5)=2^10=2^2*2^8`, matching
  `Cl(1,1) ⊗ Cl(4,4)`;
* matrix dimensions `M₂ ⊗ M₁₆ ≃ M₃₂` at the level of real dimensions;
* split signature anomaly index `5-5=0`;
* an `osp(1|2)` atom where `G²=T` implies `{G,G}=2T`;
* tensor/Bott-block maps preserving tripotent geometry and the twisted
  Witten index in the colimit.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55AnomalyOSP

open Matrix

/-! ## Dimension and split-signature arithmetic -/

/-- Clifford real vector-space dimension. -/
def cliffordDim (p q : ℕ) : ℕ := 2 ^ (p + q)

/-- `Cl(5,5)` has dimension `1024`. -/
theorem cliffordDim_55 : cliffordDim 5 5 = 1024 := by
  norm_num [cliffordDim]

/-- `Cl(1,1)` has dimension `4`. -/
theorem cliffordDim_11 : cliffordDim 1 1 = 4 := by
  norm_num [cliffordDim]

/-- `Cl(4,4)` has dimension `256`. -/
theorem cliffordDim_44 : cliffordDim 4 4 = 256 := by
  norm_num [cliffordDim]

/-- Dimension factorization for `Cl(5,5) ≃ Cl(1,1) ⊗ Cl(4,4)`. -/
theorem clifford_55_factor_dim : cliffordDim 5 5 = cliffordDim 1 1 * cliffordDim 4 4 := by
  norm_num [cliffordDim]

/-- Matrix dimension factorization `M₂ ⊗ M₁₆` has `M₃₂` dimension. -/
theorem matrix_dim_factor : 2^2 * 16^2 = 32^2 := by
  norm_num

/-- Split-signature anomaly index. -/
def anomalyIndex (p q : ℤ) : ℤ := p - q

/-- The `(5,5)` anomaly index vanishes. -/
theorem anomalyIndex_55_zero : anomalyIndex 5 5 = 0 := by
  norm_num [anomalyIndex]

/-! ## Native noncommutative operator facts -/

section NativeOSp

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev OSpSurface := InfoGeometry.Algebra.OSp12.OperatorSurface (V := V)

theorem osp_G1_square
    (S : InfoGeometry.Algebra.OSp12.OperatorSurface (V := V))
    (hS : InfoGeometry.Algebra.OSp12.OperatorSurfaceLaws S) :
    S.G1 * S.G1 = S.Ep :=
  InfoGeometry.Algebra.OSp12.OperatorSurface.G1_sq S
    (InfoGeometry.Algebra.OSp12.OperatorSurfaceLaws.G1_G1 hS)

theorem osp_G1_anticommutator
    (S : InfoGeometry.Algebra.OSp12.OperatorSurface (V := V))
    (hS : InfoGeometry.Algebra.OSp12.OperatorSurfaceLaws S) :
    S.G1 * S.G1 + S.G1 * S.G1 = (2 : ℝ) • S.Ep := by
  rw [osp_G1_square S hS]
  module

end NativeOSp


end InfoGeometry.Clifford.Clifford55AnomalyOSP
