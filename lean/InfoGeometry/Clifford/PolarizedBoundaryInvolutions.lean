import InfoGeometry.Clifford.PolarizedMinkowski55

/-!
# Three source involutions and a genuine fundamental symmetry

Swapping two real vector slots is not, by definition, Tomita conjugation.
An origin-fixing linear involution is not a freely acting Klein-bottle deck
transformation. The source's vector sign flip is a quadratic isometry, but
it is not a fundamental symmetry: its polarized form is not positive.

A distinct fundamental symmetry is constructed and positivity is proved.
The source swap has determinant minus one in an explicit full coordinate
basis, so the complete quadratic isometry group cannot be called SO(5,5).
-/

noncomputable section

namespace InfoGeometry.Clifford.PolarizedBoundaryInvolutions

open scoped BigOperators
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.PolarizedMinkowski55

/-- Exchange the two five-dimensional slots. -/
def pairSwap : Boundary55 ≃ₗ[ℝ] Boundary55 where
  toFun z := (z.2, z.1)
  invFun z := (z.2, z.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reverse both four-vector slots, leaving the two scalar slots unchanged. -/
def vectorFlip : Boundary55 ≃ₗ[ℝ] Boundary55 where
  toFun z := ((z.1.1, -z.1.2), (z.2.1, -z.2.2))
  invFun z := ((z.1.1, -z.1.2), (z.2.1, -z.2.2))
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by ext <;> simp [add_comm]
  map_smul' r z := by simp

/-- The source's composite, without an unproved topological interpretation. -/
def mixedSwap : Boundary55 ≃ₗ[ℝ] Boundary55 := vectorFlip.trans pairSwap

@[simp] theorem pairSwap_sq (z : Boundary55) : pairSwap (pairSwap z) = z := rfl

@[simp] theorem vectorFlip_sq (z : Boundary55) : vectorFlip (vectorFlip z) = z := by
  simp [vectorFlip]

theorem swap_flip_commute (z : Boundary55) :
    pairSwap (vectorFlip z) = vectorFlip (pairSwap z) := rfl

@[simp] theorem mixedSwap_sq (z : Boundary55) : mixedSwap (mixedSwap z) = z := by
  simp [mixedSwap, pairSwap, vectorFlip]

theorem pairSwap_preserves (z : Boundary55) :
    boundaryQuadratic (pairSwap z) = boundaryQuadratic z := by
  simp [pairSwap, Fin.sum_univ_three]
  ring

theorem vectorFlip_preserves (z : Boundary55) :
    boundaryQuadratic (vectorFlip z) = boundaryQuadratic z := by
  simp [vectorFlip]

theorem mixedSwap_preserves (z : Boundary55) :
    boundaryQuadratic (mixedSwap z) = boundaryQuadratic z := by
  change boundaryQuadratic (pairSwap (vectorFlip z)) = _
  rw [pairSwap_preserves, vectorFlip_preserves]

def pairSwapIsometry : boundaryQuadratic.IsometryEquiv boundaryQuadratic where
  toLinearEquiv := pairSwap
  map_app' := pairSwap_preserves

def vectorFlipIsometry : boundaryQuadratic.IsometryEquiv boundaryQuadratic where
  toLinearEquiv := vectorFlip
  map_app' := vectorFlip_preserves

def mixedSwapIsometry : boundaryQuadratic.IsometryEquiv boundaryQuadratic where
  toLinearEquiv := mixedSwap
  map_app' := mixedSwap_preserves

/-- A concrete negative direction fixed by the source's proposed fundamental symmetry. -/
theorem vectorFlip_not_positive :
    QuadraticMap.polar boundaryQuadratic (alphaRay - betaRay)
      (vectorFlip (alphaRay - betaRay)) = -2 := by
  norm_num [QuadraticMap.polar, alphaRay, betaRay, vectorFlip]

/-- Unlike the source sign flip, this involution induces a positive polar pairing. -/
def fundamentalSymmetry : Boundary55 ≃ₗ[ℝ] Boundary55 where
  toFun z :=
    ((z.2.1, (-z.2.2.1, z.2.2.2)), (z.1.1, (-z.1.2.1, z.1.2.2)))
  invFun z :=
    ((z.2.1, (-z.2.2.1, z.2.2.2)), (z.1.1, (-z.1.2.1, z.1.2.2)))
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by ext <;> simp [add_comm]
  map_smul' r z := by simp

@[simp] theorem fundamentalSymmetry_sq (z : Boundary55) :
    fundamentalSymmetry (fundamentalSymmetry z) = z := by simp [fundamentalSymmetry]

/-- In the native diagonal frame it fixes positives and negates negatives. -/
theorem fundamentalSymmetry_diagonal (z : Boundary55) :
    diagonalEquiv (fundamentalSymmetry z) =
      ((diagonalEquiv z).1, -(diagonalEquiv z).2) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [diagonalEquiv, fundamentalSymmetry] <;> ring

theorem fundamentalSymmetry_preserves (z : Boundary55) :
    boundaryQuadratic (fundamentalSymmetry z) = boundaryQuadratic z := by
  simp [fundamentalSymmetry, Fin.sum_univ_three]
  ring

/-- The induced scalar expression is a positive sum of all ten coordinate squares. -/
theorem fundamentalSymmetry_polar (z : Boundary55) :
    QuadraticMap.polar boundaryQuadratic z (fundamentalSymmetry z) =
      z.1.1^2 + z.2.1^2 + z.1.2.1^2 + z.2.2.1^2 +
        (∑ i : Fin 3, z.1.2.2 i ^ 2) + (∑ i : Fin 3, z.2.2.2 i ^ 2) := by
  simp [QuadraticMap.polar, fundamentalSymmetry, Fin.sum_univ_three]
  ring

/-- Positive definiteness is proved on the actual carrier, not assumed in a record. -/
theorem fundamentalSymmetry_positive (z : Boundary55) (hz : z ≠ 0) :
    0 < QuadraticMap.polar boundaryQuadratic z (fundamentalSymmetry z) := by
  rw [fundamentalSymmetry_polar]
  simp only [Fin.sum_univ_three]
  by_contra hn
  have hle := not_lt.mp hn
  apply hz
  rcases z with ⟨⟨a, t, u⟩, ⟨b, s, v⟩⟩
  dsimp at hle
  have ha := sq_nonneg a
  have hb := sq_nonneg b
  have ht := sq_nonneg t
  have hs := sq_nonneg s
  have hu0 := sq_nonneg (u 0)
  have hu1 := sq_nonneg (u 1)
  have hu2 := sq_nonneg (u 2)
  have hv0 := sq_nonneg (v 0)
  have hv1 := sq_nonneg (v 1)
  have hv2 := sq_nonneg (v 2)
  ext i <;> (try fin_cases i) <;> simp <;> nlinarith

/-- Full explicit diagonal coordinates for a genuine determinant calculation. -/
def flat55 : V55 ≃ₗ[ℝ] (Fin 10 → ℝ) where
  toFun z := ![z.1 0, z.1 1, z.1 2, z.1 3, z.1 4,
    z.2 0, z.2 1, z.2 2, z.2 3, z.2 4]
  invFun x := (![x 0, x 1, x 2, x 3, x 4], ![x 5, x 6, x 7, x 8, x 9])
  left_inv z := by apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by funext i; fin_cases i <;> rfl
  map_add' z w := by funext i; fin_cases i <;> rfl
  map_smul' r z := by funext i; fin_cases i <;> rfl

/-- Matrix of the source swap after the proved diagonal coordinate equivalence. -/
def pairSwapMatrix : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.diagonal ![1, -1, 1, 1, 1, -1, 1, -1, -1, -1]

/-- The displayed matrix represents the actual swap, not an unrelated diagonal matrix. -/
theorem pairSwap_matrix_action (z : Boundary55) :
    flat55 (diagonalEquiv (pairSwap z)) =
      Matrix.mulVec pairSwapMatrix (flat55 (diagonalEquiv z)) := by
  funext i
  fin_cases i <;>
    simp [pairSwapMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal,
      flat55, diagonalEquiv, pairSwap] <;> ring

/-- The isometry is orientation reversing, excluding the claimed full SO stabilizer. -/
theorem pairSwapMatrix_det : Matrix.det pairSwapMatrix = -1 := by
  norm_num [pairSwapMatrix, Matrix.det_diagonal, Fin.prod_univ_succ]

/-- The source composite fixes the origin and therefore is not a free deck action. -/
theorem mixedSwap_fixed_point : ∃ z : Boundary55, mixedSwap z = z := ⟨0, map_zero _⟩

/-- Its square-one law lifts functorially to the actual Clifford algebra. -/
def mixedSwapClifford : CliffordAlgebra boundaryQuadratic ≃ₐ[ℝ]
    CliffordAlgebra boundaryQuadratic := CliffordAlgebra.equivOfIsometry mixedSwapIsometry

@[simp] theorem mixedSwapClifford_ι (z : Boundary55) :
    mixedSwapClifford (CliffordAlgebra.ι boundaryQuadratic z) =
      CliffordAlgebra.ι boundaryQuadratic (mixedSwap z) := by
  exact CliffordAlgebra.map_apply_ι _ _

theorem mixedSwapClifford_sq (x : CliffordAlgebra boundaryQuadratic) :
    mixedSwapClifford (mixedSwapClifford x) = x := by
  have h : mixedSwapClifford.toAlgHom.comp mixedSwapClifford.toAlgHom =
      AlgHom.id ℝ (CliffordAlgebra boundaryQuadratic) := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro z
    change mixedSwapClifford (mixedSwapClifford (CliffordAlgebra.ι boundaryQuadratic z)) = _
    simp
  exact DFunLike.congr_fun h x

end InfoGeometry.Clifford.PolarizedBoundaryInvolutions
