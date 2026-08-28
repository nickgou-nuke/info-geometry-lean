import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure

/-!
# Five-Graded Freudenthal-TKK Lie Homogeneous Jacobi Closure

This module establishes the core homogeneous Jacobi identities for the 5-graded Lie bracket
on `FiveGradedCarrier D`.

## Mathematical Structure:
1. `fiveJacobiator D u v w`: the trilinear Jacobiator
   $[u, [v, w]] + [v, [w, u]] + [w, [u, v]]$.
2. Cyclic symmetry:
   `fiveJacobiator_cyclic_left`, `fiveJacobiator_cyclic_right`.
3. Homogeneous Orbit Closures:
   - $(-1, -1, +1)$ lane: `jacobi_chargeMinus_chargeMinus_chargePlus`
   - $(+1, +1, -1)$ lane: `jacobi_chargePlus_chargePlus_chargeMinus`
   - $(0, 0, 0)$ lane: `jacobi_zero_zero_zero`

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The Jacobiator for three elements in the 5-graded carrier. -/
def fiveJacobiator (u v w : FiveGradedCarrier D) : FiveGradedCarrier D :=
  fiveGradedBracket D u (fiveGradedBracket D v w) +
  fiveGradedBracket D v (fiveGradedBracket D w u) +
  fiveGradedBracket D w (fiveGradedBracket D u v)

/-! ## 1. Cyclic Symmetries of the Jacobiator -/

theorem fiveJacobiator_cyclic_left (u v w : FiveGradedCarrier D) :
    fiveJacobiator D v w u = fiveJacobiator D u v w := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveJacobiator, FiveGradedCarrier.instAdd]
  · ring
  · ext <;> abel
  · abel
  · ring
  · ext <;> abel
  · ring

theorem fiveJacobiator_cyclic_right (u v w : FiveGradedCarrier D) :
    fiveJacobiator D w u v = fiveJacobiator D u v w := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveJacobiator, FiveGradedCarrier.instAdd]
  · ring
  · ext <;> abel
  · abel
  · ring
  · ext <;> abel
  · ring

/-! ## 2. Core Homogeneous Orbit Closures -/

/-- 🏆 Orbit 7 [(-1, -1, +1)]: The charge-minus charge-plus Jacobiator vanishes identically. -/
theorem jacobi_chargeMinus_chargeMinus_chargePlus (x y z : FreudenthalCharge J) :
    fiveJacobiator D (injChargeMinus D x) (injChargeMinus D y) (injChargePlus D z) = 0 := by
  dsimp [fiveJacobiator]
  exact fiveGraded_minus_minus_plus_jacobi D x y z

/-- 🏆 Orbit 7-dual [(+1, +1, -1)]: The charge-plus charge-minus Jacobiator vanishes identically. -/
theorem jacobi_chargePlus_chargePlus_chargeMinus (x y z : FreudenthalCharge J) :
    fiveJacobiator D (injChargePlus D x) (injChargePlus D y) (injChargeMinus D z) = 0 := by
  dsimp [fiveJacobiator]
  exact fiveGraded_plus_plus_minus_jacobi D x y z

@[simp] theorem fiveGradedBracket_sympZero_sympZero (T₁ T₂ : SymplecticTKKZero D) :
    fiveGradedBracket D (injSympZero D T₁) (injSympZero D T₂) = injSympZero D ⁅T₁, T₂⁆ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injSympZero] <;>
    simp

/-- 🏆 Orbit 12 [(0, 0, 0)]: The zero-grade subalgebra satisfies the Jacobi identity. -/
theorem jacobi_zero_zero_zero (T₁ T₂ T₃ : SymplecticTKKZero D) :
    fiveJacobiator D (injSympZero D T₁) (injSympZero D T₂) (injSympZero D T₃) = 0 := by
  dsimp [fiveJacobiator]
  rw [fiveGradedBracket_sympZero_sympZero,
      fiveGradedBracket_sympZero_sympZero,
      fiveGradedBracket_sympZero_sympZero,
      fiveGradedBracket_sympZero_sympZero,
      fiveGradedBracket_sympZero_sympZero,
      fiveGradedBracket_sympZero_sympZero]
  apply FiveGradedCarrier.ext <;>
    dsimp [injSympZero] <;>
    simp only [lie_jacobi, add_zero]

end InfoGeometry.Exceptional.Freudenthal
