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

Uncompiled sandbox candidate. The full Clifford algebra has dimension 128;
the endomorphisms of the native eight-dimensional Zorn module have dimension
64. This does not contradict injectivity of the imaginary generator map.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryAction

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-- The full Clifford algebra on the native imaginary hyperplane has dimension 128. -/
theorem leftClifford_finrank :
    Module.finrank ℝ (CliffordAlgebra leftCliffordQuadratic) = 128 := by
  letI : FiniteDimensional ℝ Imaginary :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_imaginary]; norm_num)
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let b : Module.Basis (Fin 7) ℝ Imaginary :=
    Module.finBasisOfFinrankEq ℝ Imaginary finrank_imaginary
  rw [(CliffordAlgebra.equivExterior leftCliffordQuadratic).finrank_eq,
    Module.finrank_eq_card_basis b.ExteriorAlgebra]
  norm_num [Fintype.card_finset]

/-- The actual real endomorphism target has dimension 64. -/
theorem canonicalZornEnd_finrank :
    Module.finrank ℝ (Module.End ℝ CanonicalZorn) = 64 := by
  letI : FiniteDimensional ℝ CanonicalZorn :=
    FiniteDimensional.of_finrank_eq_succ canonicalZorn_finrank
  rw [Module.finrank_linearMap, canonicalZorn_finrank]

/-- The native seven-generator Clifford representation is not an embedding. -/
theorem splitOctonionLeftCliffordRepresentation_not_injective :
    ¬ Function.Injective splitOctonionLeftCliffordRepresentation := by
  letI : FiniteDimensional ℝ CanonicalZorn :=
    FiniteDimensional.of_finrank_eq_succ canonicalZorn_finrank
  intro hinj
  have hdim := LinearMap.finrank_le_finrank_of_injective
    (f := splitOctonionLeftCliffordRepresentation.toLinearMap) hinj
  rw [leftClifford_finrank, canonicalZornEnd_finrank] at hdim
  norm_num at hdim

end InfoGeometry.Lie.SplitOctonionImaginaryAction
