import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Quaternion Representation of Cl(1,1)

This module provides an explicit algebra equivalence `Cl(1,1) ≃ₐ[ℝ] Mat₂(ℝ)`
by composing two isomorphisms:
1. `Cl(1,1) ≃ₐ[ℝ] ℍ[ℝ, 1, 0, -1]` (Clifford algebra to split quaternions)
2. `ℍ[ℝ, 1, 0, -1] ≃ₐ[ℝ] Mat₂(ℝ)` (Split quaternions to 2x2 matrices)
-/

open scoped Matrix

namespace Cl11Quaternion

/-- `Mat₂ R` as `2×2` matrices over `R`. -/
abbrev Mat₂ (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- The quadratic form `x^2 - y^2` on `ℝ × ℝ` (this is the usual `Cl(1,1)` form). -/
noncomputable abbrev Q11 : QuadraticForm ℝ (ℝ × ℝ) :=
  CliffordAlgebraQuaternion.Q (R := ℝ) (1 : ℝ) (-1 : ℝ)

/-- A convenient name for `Cl(1,1)` as a Clifford algebra. -/
abbrev Cl11 : Type := CliffordAlgebra (Q11)

-- The “split quaternion” parameters matching `Q11` via `CliffordAlgebraQuaternion.equiv`.
open scoped Quaternion
abbrev Hsplit : Type := ℍ[ℝ, 1, 0, -1]

-- Concrete matrices satisfying i^2 = 1, j^2 = -1, and ij = -ji.
def iM : Mat₂ ℝ := !![ (1:ℝ), 0; 0, (-1:ℝ) ]
def jM : Mat₂ ℝ := !![ (0:ℝ), 1; (-1 : ℝ), 0 ]
def kM : Mat₂ ℝ := iM * jM

@[simp] lemma kM_eq : kM = !![(0:ℝ), 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [kM, iM, jM, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

/-- A quaternionic basis inside `Mat₂(ℝ)` for parameters `(1,0,-1)`. -/
def matBasis : QuaternionAlgebra.Basis (Mat₂ ℝ) (1 : ℝ) (0 : ℝ) (-1 : ℝ) :=
by
  refine
    { i := iM
      j := jM
      k := kM
      i_mul_i := ?_
      j_mul_j := ?_
      i_mul_j := rfl
      j_mul_i := ?_ }
  · -- iM*iM = 1
    ext a b; fin_cases a <;> fin_cases b <;>
      (simp [iM, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  · -- jM*jM = -1
    ext a b; fin_cases a <;> fin_cases b <;>
      (simp [jM, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  · -- jM*iM = -kM
    ext a b; fin_cases a <;> fin_cases b <;>
      (simp [jM, iM, kM_eq, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

/-- The `ℝ`-algebra hom `ℍ[ℝ,1,0,-1] →ₐ[ℝ] Mat₂(ℝ)` induced by `matBasis`. -/
def toMatrix : Hsplit →ₐ[ℝ] Mat₂ ℝ :=
  (matBasis).liftHom

/-- Explicit entrywise formula for `toMatrix`. -/
lemma toMatrix_apply (q : Hsplit) :
    toMatrix q
      = !![ q.re + q.imI,        q.imJ + q.imK
          ; -q.imJ + q.imK,      q.re - q.imI ] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [toMatrix, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
      matBasis, iM, jM, kM, Algebra.algebraMap_eq_smul_one]; try ring)

/-- A candidate inverse map `Mat₂(ℝ) → ℍ[ℝ,1,0,-1]` (solve for the coordinates). -/
noncomputable def ofMatrix (A : Mat₂ ℝ) : Hsplit :=
{ re  := (A 0 0 + A 1 1) / 2
  imI := (A 0 0 - A 1 1) / 2
  imJ := (A 0 1 - A 1 0) / 2
  imK := (A 0 1 + A 1 0) / 2 }

lemma ofMatrix_toMatrix (q : Hsplit) : ofMatrix (toMatrix q) = q := by
  ext <;> (simp [ofMatrix, toMatrix_apply]; try linarith)

lemma toMatrix_ofMatrix (A : Mat₂ ℝ) : toMatrix (ofMatrix A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [ofMatrix, toMatrix_apply]; try linarith)

/-- The algebra isomorphism `ℍ[ℝ,1,0,-1] ≃ₐ[ℝ] Mat₂(ℝ)`. -/
noncomputable def quatEquivMat : Hsplit ≃ₐ[ℝ] Mat₂ ℝ :=
by
  classical
  refine AlgEquiv.ofBijective toMatrix ?_
  have hL : Function.LeftInverse ofMatrix toMatrix := ofMatrix_toMatrix
  have hR : Function.RightInverse ofMatrix toMatrix := toMatrix_ofMatrix
  exact ⟨hL.injective, hR.surjective⟩

/-- The algebra isomorphism `Cl(1,1) ≃ Mat₂(ℝ)`.

Here `Cl(1,1)` is `CliffordAlgebra (x^2 - y^2)` on `ℝ × ℝ`. -/
noncomputable def cliffordEquivMat : Cl11 ≃ₐ[ℝ] Mat₂ ℝ :=
  (CliffordAlgebraQuaternion.equiv (R := ℝ) (c₁ := (1 : ℝ)) (c₂ := (-1 : ℝ))).trans
    quatEquivMat

end Cl11Quaternion
