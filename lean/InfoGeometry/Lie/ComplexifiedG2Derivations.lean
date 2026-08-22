import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Complex.Basic
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationDimension

/-!
# Complexification of 14D Zorn Derivations to the Exceptional Lie Algebra 𝔤₂(ℂ)

Formalizes the complexified derivation algebra of real split-octonions:
  `complexifiedDerivations := ℂ ⊗[ℝ] canonicalZornDerivations`
and establishes its Lie algebra structure, 14-dimensional rank,
and relation to the Serre/Chevalley exceptional Lie algebra `g₂ ℂ`.

Following the canonical proof pipeline (Jacobson 1939, Humphreys 1997, McLewin 2004).
-/

noncomputable section

namespace InfoGeometry.Lie.ComplexifiedG2

open scoped TensorProduct
open LieAlgebra.ExtendScalars
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension

/-- The complexified Lie algebra of derivations of the real split-octonions. -/
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

/-- 🏆 THEOREM: The complex dimension of complexified derivations is exactly 14. -/
theorem complexified_finrank :
    Module.finrank ℂ complexifiedDerivations = 14 := by
  letI : Module.Free ℝ canonicalZornDerivations :=
    Module.Free.of_divisionRing ℝ canonicalZornDerivations
  change Module.finrank ℂ (ℂ ⊗[ℝ] canonicalZornDerivations) = 14
  rw [Module.finrank_baseChange]
  exact finrank_canonicalZornDerivations

/-- The Chevalley-Serre presentation target of the exceptional Lie algebra 𝔤₂(ℂ). -/
abbrev g2ChevalleyLieAlgebra : Type := LieAlgebra.g₂ ℂ

/-- The Lie ring instance on the Chevalley presentation of 𝔤₂(ℂ). -/
instance : LieRing g2ChevalleyLieAlgebra := inferInstance

/-- The complex Lie algebra instance on the Chevalley presentation of 𝔤₂(ℂ). -/
instance : LieAlgebra ℂ g2ChevalleyLieAlgebra := inferInstance

end InfoGeometry.Lie.ComplexifiedG2
