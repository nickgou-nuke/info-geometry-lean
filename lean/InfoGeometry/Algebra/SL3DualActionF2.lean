import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SplitCayleyF2
import InfoGeometry.Algebra.SplitCayleyF2FiniteVerification
import InfoGeometry.Algebra.SplitCayleyF2AddMulAutomorphism

/-! The carrier-aligned dual matrix interface for the `SL₃` action on Zorn
matrices.  It records the row-vector convention from Lopatin--Zubkov §1.3:
`u ↦ u g` and `v ↦ v g⁻ᵀ`.  The inverse-transpose relation is data to be
proved for each concrete matrix; it is not inferred from a name or comment.
-/

namespace InfoGeometry.Algebra.SplitCayleyF2

structure SL3DualPair where
  g : Mat3
  h : Mat3
  right_inverse : g * h.transpose = 1
  left_inverse : h * g.transpose = 1

def rowAction (g : Mat3) (u : Vec3) : Vec3 :=
  fun i => ∑ j, u j * g j i

def dualAction (h : Mat3) (v : Vec3) : Vec3 :=
  fun i => ∑ j, v j * h j i

def zornAction (p : SL3DualPair) (x : Cayley) : Cayley :=
  { α := x.α
    u := rowAction p.g x.u
    v := dualAction p.h x.v
    β := x.β }

theorem rowAction_cyclic : rowAction cyclicMatrix = cyclic := by
  funext u i
  fin_cases i <;> simp [rowAction, cyclicMatrix, cyclic, Fin.sum_univ_succ]

theorem dualAction_cyclic : dualAction cyclicMatrix = cyclic := by
  funext v i
  fin_cases i <;> simp [dualAction, cyclicMatrix, cyclic, Fin.sum_univ_succ]

theorem rowAction_shear : rowAction shearMatrix = shearU := by
  funext u i
  fin_cases i <;> simp [rowAction, shearMatrix, shearU, Fin.sum_univ_succ]

def dualShearMatrix : Mat3 :=
  !![1, 1, 0; 0, 1, 0; 0, 0, 1]

theorem dualAction_shear : dualAction dualShearMatrix = shearV := by
  funext v i
  fin_cases i <;> simp [dualAction, dualShearMatrix, shearV, Fin.sum_univ_succ] <;> ring

def cyclicSL3DualPair : SL3DualPair :=
  { g := cyclicMatrix
    h := cyclicMatrix
    right_inverse := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cyclicMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
    left_inverse := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cyclicMatrix, Matrix.mul_apply, Fin.sum_univ_succ] }

theorem cyclicSL3DualPair_rowAction :
    rowAction cyclicSL3DualPair.g = cyclic := by
  exact rowAction_cyclic

theorem cyclicSL3DualPair_dualAction :
    dualAction cyclicSL3DualPair.h = cyclic := by
  exact dualAction_cyclic

def shearSL3DualPair : SL3DualPair :=
  { g := shearMatrix
    h := dualShearMatrix
    right_inverse := by
      have htwo : (1 : Scalar) + 1 = 0 := by decide
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [shearMatrix, dualShearMatrix, Matrix.mul_apply, Fin.sum_univ_succ, htwo]
    left_inverse := by
      have htwo : (1 : Scalar) + 1 = 0 := by decide
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [shearMatrix, dualShearMatrix, Matrix.mul_apply, Fin.sum_univ_succ, htwo] }

theorem shearSL3DualPair_rowAction :
    rowAction shearSL3DualPair.g = shearU := by
  exact rowAction_shear

theorem shearSL3DualPair_dualAction :
    dualAction shearSL3DualPair.h = shearV := by
  exact dualAction_shear

theorem zornAction_cyclic (x : Cayley) :
    zornAction cyclicSL3DualPair x = cyclicAction x := by
  cases x
  simp [zornAction, cyclicSL3DualPair, rowAction_cyclic,
    dualAction_cyclic, cyclicAction]

theorem zornAction_shear (x : Cayley) :
    zornAction shearSL3DualPair x = shearAction x := by
  cases x
  simp [zornAction, shearSL3DualPair, rowAction_shear,
    dualAction_shear, shearAction]

theorem zornAction_cyclic_mul (x y : Cayley) :
    zornAction cyclicSL3DualPair (x * y) =
      zornAction cyclicSL3DualPair x * zornAction cyclicSL3DualPair y := by
  rw [zornAction_cyclic, zornAction_cyclic, zornAction_cyclic,
    cyclicAction_mul]

theorem zornAction_shear_mul (x y : Cayley) :
    zornAction shearSL3DualPair (x * y) =
      zornAction shearSL3DualPair x * zornAction shearSL3DualPair y := by
  rw [zornAction_shear, zornAction_shear, zornAction_shear,
    shearAction_mul]

theorem zornAction_cyclic_one :
    zornAction cyclicSL3DualPair (1 : Cayley) = 1 := by
  rw [zornAction_cyclic, cyclicAction_one]

theorem zornAction_shear_one :
    zornAction shearSL3DualPair (1 : Cayley) = 1 := by
  rw [zornAction_shear, shearAction_one]

theorem cyclicAction_add (x y : Cayley) :
    cyclicAction (add x y) = add (cyclicAction x) (cyclicAction y) := by
  rcases x with ⟨xa, xu, xv, xb⟩
  rcases y with ⟨ya, yu, yv, yb⟩
  simp only [cyclicAction, add, cyclic]
  apply Cayley.ext <;> try rfl
  all_goals funext i <;> fin_cases i <;> simp <;> ring

theorem shearAction_add (x y : Cayley) :
    shearAction (add x y) = add (shearAction x) (shearAction y) := by
  rcases x with ⟨xa, xu, xv, xb⟩
  rcases y with ⟨ya, yu, yv, yb⟩
  simp only [shearAction, add, shearU, shearV]
  apply Cayley.ext <;> try rfl
  all_goals funext i <;> fin_cases i <;> simp <;> ring

theorem cyclicAction_zero : cyclicAction (zero : Cayley) = zero := by
  rfl

theorem shearAction_zero : shearAction (zero : Cayley) = zero := by
  rfl

noncomputable def cyclicAddMulAutomorphism : AddMulAutomorphism where
  toEquiv := cyclicAutomorphism.toEquiv
  map_zero' := cyclicAction_zero
  map_add' := cyclicAction_add
  map_mul' := cyclicAction_mul
  map_one' := cyclicAction_one

noncomputable def shearAddMulAutomorphism : AddMulAutomorphism where
  toEquiv := shearAutomorphism.toEquiv
  map_zero' := shearAction_zero
  map_add' := shearAction_add
  map_mul' := shearAction_mul
  map_one' := shearAction_one

end InfoGeometry.Algebra.SplitCayleyF2
