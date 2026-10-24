/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceModularBridge
import InfoGeometry.Canonical.PeirceWeylExamples
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Integral modular shears: actual SL(2,Z) generation and trace identities

The source uses the negative of Mathlib's standard S. We transport Mathlib's
existing generation theorem instead of inferring generation from power laws.
The presentation map is proved surjective; injectivity is not asserted here.
-/
namespace InfoGeometry.Canonical.IntegralModularShears

open Matrix
open scoped MatrixGroups
open InfoGeometry.Canonical.PeirceWeylExamples
open InfoGeometry.Core.ParabolicShearRelations
open InfoGeometry.Core.ParabolicModularRepresentation
open InfoGeometry.Core.PeirceWeylUnits
open InfoGeometry.Core.PeirceDensityIntertwining
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

/-- Source convention `[[0,1],[-1,0]]`, opposite Mathlib's standard S. -/
def S : SL(2, ℤ) := ModularGroup.S⁻¹

/-- Native integral unit-determinant upper shear. -/
def T : SL(2, ℤ) := ModularGroup.T

/-- Native lower shear with negative off-diagonal entry. -/
def L : SL(2, ℤ) := S * T * S⁻¹

/-- The ordered double shear is S T inverse, not the supported third root. -/
def U : SL(2, ℤ) := S * T⁻¹

/-- These are native special-linear matrices, not unbundled determinant claims. -/
theorem matrix_values :
    (S : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] ∧
    (T : Matrix (Fin 2) (Fin 2) ℤ) = 1 + d₂ ∧
    (L : Matrix (Fin 2) (Fin 2) ℤ) = 1 - b₂ ∧
    (U : Matrix (Fin 2) (Fin 2) ℤ) = doubleShear d₂ b₂ ∧
    (U : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 1] := by decide

theorem concrete_factorizations : T * L = U ∧ T * L * T = S := by decide

/-- The two signs and product orders in the source are distinguished exactly. -/
theorem corrected_third_root :
    thirdRoot d₂ b₂ = ((S * T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ∧
    thirdRoot d₂ b₂ ≠ ((S * T⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ∧
    doubleShear d₂ b₂ ^ 2 = !![-1, 1; -1, 0] := by decide

theorem integral_modular_relations : S ^ 4 = 1 ∧ S ^ 2 = U ^ 3 := by decide

/-- Least positive power certificates: exact orders four and six in this integral model. -/
theorem exact_integral_orders :
    S ^ 4 = 1 ∧ (∀ n : Fin 3, S ^ (n.val + 1) ≠ 1) ∧
    U ^ 6 = 1 ∧ (∀ n : Fin 5, U ^ (n.val + 1) ≠ 1) ∧
    (U ^ 2) ^ 3 = 1 ∧ U ^ 2 ≠ 1 ∧ (U ^ 2) ^ 2 ≠ 1 := by decide

/-- Generation is transported from Mathlib's established S,T theorem. -/
theorem integral_generators : Subgroup.closure ({S, U} : Set (SL(2, ℤ))) = ⊤ := by
  let H := Subgroup.closure ({S, U} : Set (SL(2, ℤ)))
  have hs : S ∈ H := Subgroup.subset_closure (by simp)
  have hu : U ∈ H := Subgroup.subset_closure (by simp)
  have hstd : ModularGroup.S ∈ H := by
    have hh := H.inv_mem hs
    simpa only [S, inv_inv] using hh
  have ht : ModularGroup.T ∈ H := by
    have hh := H.mul_mem (H.inv_mem hu) hs
    simpa [U, T, mul_assoc] using hh
  have hle : Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set (SL(2, ℤ))) ≤ H := by
    apply Subgroup.closure_le.mpr
    intro g hg
    rcases hg with rfl | hg
    · exact hstd
    · rcases hg with rfl
      exact ht
  rw [SpecialLinearGroup.SL2Z_generators] at hle
  exact le_antisymm le_top hle

/-- The relation quotient maps to the actual native integral modular group. -/
def integralRepresentation : ModularRelationsGroup →* SL(2, ℤ) :=
  ofRelations S U integral_modular_relations.1 integral_modular_relations.2

/-- All integral determinant-one matrices occur in this representation. -/
theorem integralRepresentation_surjective : Function.Surjective integralRepresentation := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← integral_generators]
  apply Subgroup.closure_le.mpr
  intro g hg
  rcases hg with rfl | hg
  · exact ⟨PresentedGroup.of false, by simp [integralRepresentation]⟩
  · rcases hg with rfl
    exact ⟨PresentedGroup.of true, by simp [integralRepresentation]⟩

/-- Concrete traces in the source's sign convention. -/
theorem modular_traces :
    Matrix.trace (S : Matrix (Fin 2) (Fin 2) ℤ) = 0 ∧
    Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℤ) = 1 ∧
    Matrix.trace ((U ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -1 ∧
    Matrix.trace ((U ^ 3 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -2 := by decide

/-- The existing weighted boundary law instantiated with the actual matrix trace. -/
theorem matrix_trace_boundary (u v : ℤ) (Y : Matrix (Fin 2) (Fin 2) ℤ) :
    u * Matrix.trace (density d₂ b₂ u v * (d₂ * Y)) =
      v * Matrix.trace (density d₂ b₂ u v * (Y * d₂)) ∧
    v * Matrix.trace (density d₂ b₂ u v * (b₂ * Y)) =
      u * Matrix.trace (density d₂ b₂ u v * (Y * b₂)) := by
  exact density_trace_boundary integral_pair.1 integral_pair.2
    (Matrix.traceLinearMap (Fin 2) ℤ ℤ) (fun x y => Matrix.trace_mul_comm x y) u v Y

/-- Actual unit-conjugacy invariance, distinct from the weighted boundary identities. -/
theorem trace_unit_conjugation (g : (Matrix (Fin 2) (Fin 2) ℤ)ˣ)
    (X : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℤ) * X * ↑g⁻¹) = Matrix.trace X := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, g.inv_val, one_mul]

/-- The universal power law does not force a primitive root: the zero pair collapses it. -/
theorem zero_pair_collapse :
    doubleShear (0 : ℤ) 0 = 1 ∧ tripleShear (0 : ℤ) 0 = 1 := by decide

/-- Proper support makes the ambient Phi-six defect nonzero. -/
theorem proper_support_defect :
    doubleShear d₃ b₃ ^ 2 - doubleShear d₃ b₃ + 1 = harmonicSupport d₃ b₃ ∧
    harmonicSupport d₃ b₃ ≠ 0 ∧ doubleShear d₃ b₃ ^ 6 = 1 := by decide

/-- The common sign is central relative to generated shears, not in the ambient algebra. -/
theorem sign_not_ambient_central :
    supportSign d₃ b₃ * Matrix.stdBasisMatrix 0 2 1 ≠
      Matrix.stdBasisMatrix 0 2 1 * supportSign d₃ b₃ := by decide

#check @InfoGeometry.Core.ParabolicModularRepresentation.representation
#check @InfoGeometry.Canonical.PeirceModularBridge.tripleUnit_eq_weylUnit
#check @integral_generators
#check @integralRepresentation_surjective
#check @matrix_trace_boundary

end InfoGeometry.Canonical.IntegralModularShears
