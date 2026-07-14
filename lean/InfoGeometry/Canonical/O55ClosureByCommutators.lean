import InfoGeometry.Clifford.ConformalGeneratorLemmas55

/-!
# InfoGeometry.Canonical.O55ClosureByCommutators

Conservative capstone for the repo-native `O(5,5)` closure story.

The point of this file is not to assert a finished global classification theorem,
but to package the actual construction pattern already proved in the repository:

1. start from the null generators `u₅, v₅, u₄, v₄`,
2. when noncommuting pairs appear, adjoin their commutator generators
   `D₅ = 1/2 [u₅,v₅]`, `D₄ = 1/2 [u₄,v₄]`,
3. combine them into `D = D₅ + D₄`,
4. form the reflection/complex-structure lane `J₅ = u₅ - v₅`,
   `J₄ = u₄ - v₄`, `J = J₅ J₄`,
5. record the resulting closure/action laws.

This is the honest step-by-step commutator-growth surface currently present in
`ConformalGeneratorLemmas55.lean`.

**Relationship to sibling capstones:**

This file covers the **O(5,5) / TKK generator corridor** in `Cl(5,5)`:
null generators → dilation → complex structure → adjoint closure.

For the **abstract TKK five-grading + affine `sl₂` + Pin(5,5) reflections** story,
see the sibling capstone:
`InfoGeometry.Canonical.TKKFiveGradePin55AffineCapstone`.

Together, these two files form the complete kernel-checked TKK / Pin(5,5) packet:
- `O55ClosureByCommutators`: the Cl(5,5) null-generator closure chain
- `TKKFiveGradePin55AffineCapstone`: the abstract TKK weights, affine ladder, and orbit trichotomy
-/

noncomputable section

namespace O55ClosureByCommutators

open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Clifford.ClNN

/-- The primitive null-generator packet. -/
theorem null_generator_packet :
    u5 * u5 = 0 ∧
    v5 * v5 = 0 ∧
    u4 * u4 = 0 ∧
    v4 * v4 = 0 ∧
    u5 * v5 + v5 * u5 = 1 ∧
    u4 * v4 + v4 * u4 = 1 := by
  exact ⟨u5_sq, v5_sq, u4_sq, v4_sq, u5_v5_add_v5_u5, u4_v4_add_v4_u4⟩

/-- The commutator-adjoined dilation generators. -/
theorem dilation_generator_def_packet :
    D5 = (1 / 2 : ℝ) • (u5 * v5 - v5 * u5) ∧
    D4 = (1 / 2 : ℝ) • (u4 * v4 - v4 * u4) ∧
    D = D5 + D4 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The reflection/complex-structure generator packet. -/
theorem J_generator_def_packet :
    J5 = u5 - v5 ∧
    J4 = u4 - v4 ∧
    J = J5 * J4 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The resulting square laws for the `J`-lane. -/
theorem J_square_packet :
    J5 * J5 = -1 ∧
    J4 * J4 = -1 ∧
    J * J = -1 := by
  exact ⟨J5_sq, J4_sq, J_sq⟩

/-- The first closure step: `D` acts by adjoint weight on the primitive generators. -/
theorem adjoint_closure_packet :
    D * u5 - u5 * D = u5 ∧
    D * u4 - u4 * D = u4 := by
  exact ⟨adD_u5, adD_u4⟩

/-- The `θ`-reflection exchanges the primitive null generators and flips each
commutator-grown dilation generator. -/
theorem theta_reflection_packet :
    thetaOp u5 = v5 ∧
    thetaOp v5 = u5 ∧
    thetaOp u4 = v4 ∧
    thetaOp v4 = u4 ∧
    thetaOp D5 = -D5 ∧
    thetaOp D4 = -D4 ∧
    thetaOp D = -D := by
  exact ⟨theta_u5, theta_v5, theta_u4, theta_v4, theta_D5, theta_D4, theta_D⟩

/-- `θ` is involutive on the ambient `Cl(5,5)` carrier. -/
theorem theta_involution_packet (x : Alg 5) :
    thetaOp (thetaOp x) = x := by
  exact theta_inv x

/-- The repo-native `O(5,5)` closure-by-commutators packet. -/
theorem o55_closure_by_commutators_capstone :
    (u5 * u5 = 0
      ∧ v5 * v5 = 0
      ∧ u4 * u4 = 0
      ∧ v4 * v4 = 0
      ∧ u5 * v5 + v5 * u5 = 1
      ∧ u4 * v4 + v4 * u4 = 1)
    ∧ (D5 = (1 / 2 : ℝ) • (u5 * v5 - v5 * u5)
      ∧ D4 = (1 / 2 : ℝ) • (u4 * v4 - v4 * u4)
      ∧ D = D5 + D4)
    ∧ (J5 = u5 - v5
      ∧ J4 = u4 - v4
      ∧ J = J5 * J4)
    ∧ (J5 * J5 = -1
      ∧ J4 * J4 = -1
      ∧ J * J = -1)
    ∧ (D * u5 - u5 * D = u5
      ∧ D * u4 - u4 * D = u4)
    ∧ (thetaOp u5 = v5
      ∧ thetaOp v5 = u5
      ∧ thetaOp u4 = v4
      ∧ thetaOp v4 = u4
      ∧ thetaOp D5 = -D5
      ∧ thetaOp D4 = -D4
      ∧ thetaOp D = -D)
    ∧ (∀ x : Alg 5, thetaOp (thetaOp x) = x) := by
  exact ⟨null_generator_packet, dilation_generator_def_packet, J_generator_def_packet,
    J_square_packet, adjoint_closure_packet, theta_reflection_packet, theta_involution_packet⟩

end O55ClosureByCommutators
