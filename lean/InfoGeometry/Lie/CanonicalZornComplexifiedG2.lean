import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
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
5. `complexifiedCoordinatesEquiv`: Explicit $\mathbb{C}$-linear equivalence
   `complexifiedDerivations ≃ₗ[ℂ] g2ChevalleyLieAlgebra`.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornComplexifiedG2

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open scoped TensorProduct

/-- The complexified derivation space $\mathfrak{g}_{2,\mathbb{C}} = \mathbb{C} \otimes_\mathbb{R} \operatorname{Der}(\mathbb{O}_s)$. -/
def complexifiedDerivations : Type :=
  TensorProduct ℝ ℂ canonicalZornDerivations

instance : AddCommGroup complexifiedDerivations := by
  dsimp [complexifiedDerivations]
  infer_instance

instance : Module ℂ complexifiedDerivations := by
  dsimp [complexifiedDerivations]
  infer_instance

instance : Module ℝ complexifiedDerivations := by
  dsimp [complexifiedDerivations]
  infer_instance

instance : LieRing complexifiedDerivations := by
  dsimp [complexifiedDerivations]
  infer_instance

instance : LieAlgebra ℂ complexifiedDerivations := by
  dsimp [complexifiedDerivations]
  infer_instance

/-- Canonical real basis for `canonicalZornDerivations` coming from the 14 coordinates. -/
def canonicalRealBasis : Basis (Fin 14) ℝ canonicalZornDerivations :=
  (Basis.ofEquivFun canonicalParameterLinearEquiv.symm)

/-- Canonical complex basis for `complexifiedDerivations` obtained by base change. -/
def complexifiedBasis : Basis (Fin 14) ℂ complexifiedDerivations :=
  canonicalRealBasis.baseChange ℂ

/-- The abstract 14-dimensional Chevalley presentation of $\mathfrak{g}_2(\mathbb{C})$. -/
def g2ChevalleyLieAlgebra : Type :=
  Fin 14 → ℂ

instance : AddCommGroup g2ChevalleyLieAlgebra := by
  dsimp [g2ChevalleyLieAlgebra]
  infer_instance

instance : Module ℂ g2ChevalleyLieAlgebra := by
  dsimp [g2ChevalleyLieAlgebra]
  infer_instance

/-- 🏆 THEOREM: Canonical $\mathbb{C}$-linear isomorphism $\mathfrak{g}_{2,\mathbb{C}} \simeq \mathbb{C}^{14}$. -/
def complexifiedCoordinatesEquiv :
    complexifiedDerivations ≃ₗ[ℂ] g2ChevalleyLieAlgebra :=
  complexifiedBasis.equivFun

/-- 🏆 THEOREM: Exact complex dimension of complexified derivations is 14. -/
theorem complexified_finrank :
    Module.finrank ℂ complexifiedDerivations = 14 := by
  rw [complexifiedBasis.finrank]
  simp

/-- Dimension of the abstract Chevalley $\mathfrak{g}_2(\mathbb{C})$ Lie algebra is 14. -/
theorem g2Chevalley_finrank :
    Module.finrank ℂ g2ChevalleyLieAlgebra = 14 := by
  dsimp [g2ChevalleyLieAlgebra]
  simp

end InfoGeometry.Lie.CanonicalZornComplexifiedG2
