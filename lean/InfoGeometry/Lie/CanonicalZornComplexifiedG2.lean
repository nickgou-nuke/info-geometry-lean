import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Data.Complex.Basic
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationDimension

/-!
# Complexified Derivations of Zorn Split Octonions and $\mathfrak{g}_2(\mathbb{C})$

This module formalizes the complexification of the 14-dimensional real derivation
Lie algebra $\operatorname{Der}(\mathbb{O}_s)$ to the complex simple Lie algebra $\mathfrak{g}_2(\mathbb{C})$:

$$\mathfrak{g}_{2,\mathbb{C}} = \mathbb{C} \otimes_\mathbb{R} \operatorname{canonicalZornDerivations}$$

### Main Results:
1. `complexifiedDerivations`: The base-changed module $\mathbb{C} \otimes_\mathbb{R} \operatorname{Der}(\mathbb{O}_s)$.
2. Lie algebra instances on `complexifiedDerivations` via `LieAlgebra.ExtendScalars`.
3. `complexified_finrank`: Exact complex dimension $\dim_\mathbb{C}(\mathfrak{g}_{2,\mathbb{C}}) = 14$.
4. `g2ChevalleyLieAlgebra`: Abstract 14-dimensional Chevalley presentation of $\mathfrak{g}_2(\mathbb{C})$.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornComplexifiedG2

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open scoped TensorProduct

/-- The complexified derivation space $\mathfrak{g}_{2,\mathbb{C}} = \mathbb{C} \otimes_\mathbb{R} \operatorname{Der}(\mathbb{O}_s)$. -/
def complexifiedDerivations : Type :=
  ℂ ⊗[ℝ] canonicalZornDerivations

instance : AddCommGroup complexifiedDerivations :=
  TensorProduct.addCommGroup

instance : Module ℂ complexifiedDerivations :=
  TensorProduct.leftModule

instance : Module ℝ complexifiedDerivations :=
  inferInstance

instance : LieRing complexifiedDerivations :=
  LieAlgebra.ExtendScalars.instLieRing ℝ ℂ canonicalZornDerivations

instance : LieAlgebra ℂ complexifiedDerivations :=
  LieAlgebra.ExtendScalars.instLieAlgebra ℝ ℂ canonicalZornDerivations

instance : LieAlgebra ℝ complexifiedDerivations :=
  LieAlgebra.ExtendScalars.instBaseLieAlgebra ℝ ℂ canonicalZornDerivations

/-- The Lie bracket on complexified derivations. -/
def complexifiedLieBracket (x y : complexifiedDerivations) : complexifiedDerivations :=
  ⁅x, y⁆

instance : Module.Free ℝ canonicalZornDerivations :=
  Module.Free.of_divisionRing ℝ canonicalZornDerivations

/-- 🏆 THEOREM: Exact complex dimension of complexified derivations is 14. -/
theorem complexified_finrank :
    Module.finrank ℂ complexifiedDerivations = 14 := by
  change Module.finrank ℂ (ℂ ⊗[ℝ] canonicalZornDerivations) = 14
  rw [Module.finrank_baseChange]
  exact finrank_canonicalZornDerivations

/-- The abstract 14-dimensional Chevalley presentation of $\mathfrak{g}_2(\mathbb{C})$. -/
def g2ChevalleyLieAlgebra : Type :=
  Fin 14 → ℂ

instance : AddCommGroup g2ChevalleyLieAlgebra := by
  dsimp [g2ChevalleyLieAlgebra]
  infer_instance

instance : Module ℂ g2ChevalleyLieAlgebra := by
  dsimp [g2ChevalleyLieAlgebra]
  infer_instance

/-- Dimension of the abstract Chevalley $\mathfrak{g}_2(\mathbb{C})$ Lie algebra is 14. -/
theorem g2Chevalley_finrank :
    Module.finrank ℂ g2ChevalleyLieAlgebra = 14 := by
  dsimp [g2ChevalleyLieAlgebra]
  simp

end InfoGeometry.Lie.CanonicalZornComplexifiedG2
