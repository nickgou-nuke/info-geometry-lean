/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Noninjectivity of the native seven-generator real Clifford action

The full Clifford algebra has dimension 128;
the endomorphisms of the native eight-dimensional Zorn module have dimension
64. This does not contradict injectivity of the imaginary generator map.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryAction

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-- The full Clifford algebra on the native imaginary hyperplane has dimension 128. -/
theorem leftClifford_finrank :
    Module.finrank ℝ (CliffordAlgebra leftCliffordQuadratic) = 128 := by
  let : FiniteDimensional ℝ Imaginary :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_imaginary]; norm_num)
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let b : Module.Basis (Fin 7) ℝ Imaginary :=
    Module.finBasisOfFinrankEq ℝ Imaginary finrank_imaginary
  rw [(CliffordAlgebra.equivExterior leftCliffordQuadratic).finrank_eq,
    Module.finrank_eq_card_basis b.ExteriorAlgebra]
  norm_num [Fintype.card_finset]

/-- The actual real endomorphism target has dimension 64. -/
theorem canonicalZornEnd_finrank :
    Module.finrank ℝ (Module.End ℝ CanonicalZorn) = 64 := by
  let : FiniteDimensional ℝ CanonicalZorn :=
    FiniteDimensional.of_finrank_eq_succ canonicalZorn_finrank
  rw [Module.finrank_linearMap, canonicalZorn_finrank]

/-- The native seven-generator Clifford representation is not an embedding. -/
theorem splitOctonionLeftCliffordRepresentation_not_injective :
    ¬ Function.Injective splitOctonionLeftCliffordRepresentation := by
  let : FiniteDimensional ℝ CanonicalZorn :=
    FiniteDimensional.of_finrank_eq_succ canonicalZorn_finrank
  intro hinj
  have hdim := LinearMap.finrank_le_finrank_of_injective
    (f := splitOctonionLeftCliffordRepresentation.toLinearMap) hinj
  rw [leftClifford_finrank, canonicalZornEnd_finrank] at hdim
  norm_num at hdim

/-- The dimension obstruction has a quantitative form: at least 64 independent
directions in the full Clifford algebra lie in the kernel of its represented
operator action. This is the rank-nullity alternative to injectivity. -/
theorem splitOctonionLeftCliffordRepresentation_kernel_finrank_ge :
    64 ≤ Module.finrank ℝ
      (LinearMap.ker splitOctonionLeftCliffordRepresentation.toLinearMap) := by
  let : FiniteDimensional ℝ CanonicalZorn :=
    FiniteDimensional.of_finrank_eq_succ canonicalZorn_finrank
  let : FiniteDimensional ℝ (CliffordAlgebra leftCliffordQuadratic) :=
    FiniteDimensional.of_finrank_eq_succ leftClifford_finrank
  have htotal := LinearMap.finrank_range_add_finrank_ker
    splitOctonionLeftCliffordRepresentation.toLinearMap
  have hrange : Module.finrank ℝ
      splitOctonionLeftCliffordRepresentation.toLinearMap.range ≤
      Module.finrank ℝ (Module.End ℝ CanonicalZorn) :=
    Submodule.finrank_le _
  rw [leftClifford_finrank] at htotal
  rw [canonicalZornEnd_finrank] at hrange
  omega

end InfoGeometry.Lie.SplitOctonionImaginaryAction
