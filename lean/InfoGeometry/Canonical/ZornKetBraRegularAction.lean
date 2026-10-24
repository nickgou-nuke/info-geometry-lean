/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornPolarKetBra

/-! Regular multiplication acts on the ket directly and on the split-polar bra
through its adjoint. No Leibniz rule for Zorn regular multiplication is assumed. -/
namespace InfoGeometry.Canonical.ZornKetBraRegularAction
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarKetBra ZornPolarOperatorAdjoint
open ZornRealRegularMultiplicationSpectralBridge

theorem operator_mul_ketBra (T : Module.End ℝ ZornCoord) (U V : ZornCoord) :
    T * ketBra U V = ketBra (T U) V := by
  apply LinearMap.ext
  intro W
  simp [ketBra]

theorem ketBra_mul_of_adjoint (T S : Module.End ℝ ZornCoord)
    (h : LinearMap.IsAdjointPair polarForm polarForm T S) (U V : ZornCoord) :
    ketBra U V * T = ketBra U (S V) := by
  apply LinearMap.ext
  intro W
  change polarPair V (T W) • U = polarPair (S V) W • U
  rw [polarPair_symm V, polarPair_symm (S V)]
  exact congrArg (fun a : ℝ => a • U) (h W V)

theorem leftRegular_ketBra_commutator (X U V : ZornCoord) :
    leftRegular X * ketBra U V - ketBra U V * leftRegular X =
      ketBra (zornMul X U) V - ketBra U (zornMul (zornConj X) V) := by
  rw [operator_mul_ketBra, ketBra_mul_of_adjoint _ _ (leftRegular_adjoint X)]
  rfl

theorem rightRegular_ketBra_commutator (X U V : ZornCoord) :
    rightRegular X * ketBra U V - ketBra U V * rightRegular X =
      ketBra (zornMul U X) V - ketBra U (zornMul V (zornConj X)) := by
  rw [operator_mul_ketBra, ketBra_mul_of_adjoint _ _ (rightRegular_adjoint X)]
  rfl

end InfoGeometry.Canonical.ZornKetBraRegularAction
