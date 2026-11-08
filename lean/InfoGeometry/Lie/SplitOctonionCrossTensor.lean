import Mathlib.LinearAlgebra.Determinant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Physics.ZornMatrixSU3.Vector3
import InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita

/-!
# The native Zorn cross product as an alternating volume tensor

This owner does not introduce a second cross-product structure.  It reads the
`Fin 3` operation from `Canonical.ZornMatrix` against the existing scalar
triple-product determinant.  Thus the tensorial interpretation is a theorem
about the native Zorn coordinates, not a wrapper or an assumed interface.
-/

namespace InfoGeometry.Lie.SplitOctonionCrossTensor

open InfoGeometry.Canonical
open InfoGeometry.Physics.ZornMatrixSU3
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita

/-! The determinant is the native Mathlib determinant of the matrix whose
rows are the three vectors.  Keeping this definition local to the tensor
owner avoids importing any unrelated physics-side determinant alias. -/
def det3 (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) : ℝ :=
  u 0 * v 1 * w 2 + u 1 * v 2 * w 0 + u 2 * v 0 * w 1 -
    u 0 * v 2 * w 1 - u 1 * v 0 * w 2 - u 2 * v 1 * w 0

theorem nativeCross_eq_mathlib_cross (u v : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.cross u v =
      InfoGeometry.Physics.ZornMatrixSU3.crossProduct u v := by
  funext i
  fin_cases i <;>
    simp [ZornMatrix.cross,
      InfoGeometry.Physics.ZornMatrixSU3.crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

theorem nativeCross_add_left (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.cross (u + v) w =
      ZornMatrix.cross u w + ZornMatrix.cross v w := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem nativeCross_add_right (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.cross u (v + w) =
      ZornMatrix.cross u v + ZornMatrix.cross u w := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem nativeCross_smul_left (r : ℝ) (u v : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.cross (r • u) v = r • ZornMatrix.cross u v := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross] <;>
    ring

theorem nativeCross_smul_right (r : ℝ) (u v : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.cross u (r • v) = r • ZornMatrix.cross u v := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross] <;>
    ring

theorem nativeCross_self (u : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.cross u u = 0 := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross] <;>
    ring

noncomputable def nativeCrossExteriorAlternating :
    InfoGeometry.Algebra.FiniteSpin.Vec3R [⋀^Fin 2]→ₗ[ℝ] InfoGeometry.Algebra.FiniteSpin.Vec3R := by
  classical
  let f : MultilinearMap ℝ (fun _ : Fin 2 => InfoGeometry.Algebra.FiniteSpin.Vec3R) InfoGeometry.Algebra.FiniteSpin.Vec3R :=
    { toFun := fun v => ZornMatrix.cross (v 0) (v 1)
      map_update_add' := by
        intro _ v i x y
        fin_cases i
        · simpa [Function.update] using nativeCross_add_left x y (v 1)
        · simpa [Function.update] using nativeCross_add_right (v 0) x y
      map_update_smul' := by
        intro _ v i r x
        fin_cases i
        · simpa [Function.update] using nativeCross_smul_left r x (v 1)
        · simpa [Function.update] using nativeCross_smul_right r (v 0) x }
  exact AlternatingMap.mk f (by
    intro v i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · dsimp [f]
      change ZornMatrix.cross (v 0) (v 1) = 0
      have h : v 0 = v 1 := by simpa using hij
      rw [h]
      exact nativeCross_self (v 1)
    · dsimp [f]
      change ZornMatrix.cross (v 0) (v 1) = 0
      have h : v 1 = v 0 := by simpa using hij
      rw [h]
      exact nativeCross_self (v 0)
    · exact (hne rfl).elim)

noncomputable def nativeCrossExteriorMap :
    (⋀[ℝ]^2 InfoGeometry.Algebra.FiniteSpin.Vec3R) →ₗ[ℝ] InfoGeometry.Algebra.FiniteSpin.Vec3R :=
  exteriorPower.alternatingMapLinearEquiv nativeCrossExteriorAlternating

theorem nativeCrossExteriorMap_ιMulti (u v : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeCrossExteriorMap
        (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      ZornMatrix.cross u v := by
  change exteriorPower.alternatingMapLinearEquiv nativeCrossExteriorAlternating
      (exteriorPower.ιMulti ℝ 2 ![u, v]) = _
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    nativeCrossExteriorAlternating ![u, v]

/-- The native cross channel is the contraction of the coordinate
Levi--Civita tensor.  The imported `leviCivita3` is the alternating tensor
owner; this theorem only reads it back in the native Zorn coordinates. -/
theorem nativeCross_eq_leviCivita3 (u v : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.cross u v = fun k =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        (leviCivita3 k i j : ℝ) * u i * v j := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross, leviCivita3, Fin.sum_univ_succ] <;>
    ring

/-- The scalar triple product formed from the native Zorn dot and cross. -/
def nativeScalarTriple (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) : ℝ :=
  ZornMatrix.dot u (ZornMatrix.cross v w)

/-- The native scalar triple product is the full Levi--Civita contraction of
three coordinate vectors. -/
theorem nativeScalarTriple_eq_leviCivita3 (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple u v w =
      ∑ k : Fin 3, u k *
        (∑ i : Fin 3, ∑ j : Fin 3,
          (leviCivita3 k i j : ℝ) * v i * w j) := by
  rw [nativeScalarTriple, nativeCross_eq_leviCivita3]
  simp [ZornMatrix.dot, Fin.sum_univ_three]

theorem nativeScalarTriple_eq_det3 (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple u v w = det3 u v w := by
  simp [nativeScalarTriple, ZornMatrix.dot, ZornMatrix.cross, det3]
  ring

/-- The matrix whose columns are three vectors in the standard basis. -/
private def vectorColumns3 (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if j = 0 then u i else if j = 1 then v i else w i

/-- The coordinate determinant of three vectors is the determinant of their
column matrix. -/
private theorem det3_eq_vectorColumns3_det (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    det3 u v w = (vectorColumns3 u v w).det := by
  simp [det3, vectorColumns3, Matrix.det_fin_three]
  ring

/-- Applying a linear map to all three entries scales the oriented volume by
the determinant of that map. -/
theorem nativeScalarTriple_map (A : Matrix (Fin 3) (Fin 3) ℝ)
    (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple (A.mulVec u) (A.mulVec v) (A.mulVec w) =
      A.det * nativeScalarTriple u v w := by
  rw [nativeScalarTriple_eq_det3, nativeScalarTriple_eq_det3]
  rw [det3_eq_vectorColumns3_det, det3_eq_vectorColumns3_det]
  have hcolumns :
      vectorColumns3 (A.mulVec u) (A.mulVec v) (A.mulVec w) =
        A * vectorColumns3 u v w := by
    ext i j
    fin_cases j <;>
      simp [vectorColumns3, Matrix.mul_apply, Matrix.mulVec, _root_.dotProduct,
        Fin.sum_univ_succ]
  rw [hcolumns, Matrix.det_mul]

theorem nativeScalarTriple_cyclic (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple u v w = nativeScalarTriple v w u := by
  rw [nativeScalarTriple_eq_det3, nativeScalarTriple_eq_det3]
  simp [det3]
  ring

theorem nativeScalarTriple_swap (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple u v w = -nativeScalarTriple u w v := by
  rw [nativeScalarTriple_eq_det3, nativeScalarTriple_eq_det3]
  simp [det3]
  ring

theorem nativeScalarTriple_swap_left (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple u v w = -nativeScalarTriple v u w := by
  calc
    nativeScalarTriple u v w = nativeScalarTriple v w u :=
      nativeScalarTriple_cyclic u v w
    _ = -nativeScalarTriple v u w :=
      nativeScalarTriple_swap v w u

theorem nativeScalarTriple_self_left (u w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple u u w = 0 := by
  rw [nativeScalarTriple_eq_det3]
  simp [det3]
  ring

theorem nativeScalarTriple_self_right (u v : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeScalarTriple u v v = 0 := by
  rw [nativeScalarTriple_eq_det3]
  simp [det3]
  ring

/-- The native cross channel is orthogonal to its first input. -/
theorem nativeCross_left_orthogonal (v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.dot v (ZornMatrix.cross v w) = 0 := by
  exact nativeScalarTriple_self_left v w

/-- The native cross channel is orthogonal to its second input. -/
theorem nativeCross_right_orthogonal (v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.dot w (ZornMatrix.cross v w) = 0 := by
  change nativeScalarTriple w v w = 0
  rw [nativeScalarTriple_swap]
  simp [nativeScalarTriple_self_left]

theorem nativeScalarTriple_cross_cyclic (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.dot (ZornMatrix.cross u v) w =
      ZornMatrix.dot u (ZornMatrix.cross v w) := by
  simp [ZornMatrix.dot, ZornMatrix.cross]
  ring

/-- Swapping the two arguments of the cross channel reverses the scalar
triple pairing. -/
theorem nativeScalarTriple_cross_swap (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    ZornMatrix.dot (ZornMatrix.cross u v) w =
      -ZornMatrix.dot (ZornMatrix.cross u w) v := by
  calc
    ZornMatrix.dot (ZornMatrix.cross u v) w =
        nativeScalarTriple u v w :=
      (nativeScalarTriple_cross_cyclic u v w).trans rfl
    _ = -nativeScalarTriple u w v := nativeScalarTriple_swap u v w
    _ = -ZornMatrix.dot (ZornMatrix.cross u w) v := by
      change -ZornMatrix.dot u (ZornMatrix.cross w v) =
        -ZornMatrix.dot (ZornMatrix.cross u w) v
      rw [nativeScalarTriple_cross_cyclic u w v]

/-- The native cross product is uniquely recovered from its dot pairings. -/
theorem nativeCross_eq_of_dot_eq (u v x : InfoGeometry.Algebra.FiniteSpin.Vec3R)
    (h : ∀ w, ZornMatrix.dot w x = ZornMatrix.dot w (ZornMatrix.cross u v)) :
    x = ZornMatrix.cross u v := by
  funext i
  have hi := h (Pi.single i 1)
  fin_cases i <;>
    simpa [ZornMatrix.dot, ZornMatrix.cross, Pi.single_apply] using hi

theorem nativeDot_eq_det3_iff_eq_cross (x v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    (∀ u : InfoGeometry.Algebra.FiniteSpin.Vec3R, ZornMatrix.dot u x = det3 u v w) ↔
      x = ZornMatrix.cross v w := by
  constructor
  · intro h
    apply nativeCross_eq_of_dot_eq v w x
    intro u
    exact (h u).trans (nativeScalarTriple_eq_det3 u v w).symm
  · rintro rfl u
    exact nativeScalarTriple_eq_det3 u v w

/-! ## Literal Mathlib alternating-map layer -/

/-- The standard basis determinant is the native alternating volume form. -/
noncomputable def nativeVolumeForm : InfoGeometry.Algebra.FiniteSpin.Vec3R [⋀^Fin 3]→ₗ[ℝ] ℝ :=
  (Pi.basisFun ℝ (Fin 3)).det

@[simp] theorem nativeVolumeForm_apply (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeVolumeForm ![u, v, w] = det3 u v w := by
  rw [nativeVolumeForm, Pi.basisFun_det_apply]
  simp [det3, Matrix.det_fin_three]
  ring

@[simp] theorem nativeVolumeForm_apply_eq_scalarTriple (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeVolumeForm ![u, v, w] = nativeScalarTriple u v w := by
  rw [nativeVolumeForm_apply, nativeScalarTriple_eq_det3]

/-- The cross product is uniquely recovered from the literal alternating
volume map, without mentioning the coordinate determinant in the statement.
This is the finite-dimensional metric/orientation characterization of the
native Zorn cross channel. -/
theorem nativeDot_eq_nativeVolumeForm_iff_eq_cross (x v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    (∀ u : InfoGeometry.Algebra.FiniteSpin.Vec3R,
      ZornMatrix.dot u x = nativeVolumeForm ![u, v, w]) ↔
      x = ZornMatrix.cross v w := by
  rw [show (∀ u : InfoGeometry.Algebra.FiniteSpin.Vec3R,
      ZornMatrix.dot u x = nativeVolumeForm ![u, v, w]) ↔
      (∀ u : InfoGeometry.Algebra.FiniteSpin.Vec3R, ZornMatrix.dot u x = det3 u v w) by
    constructor
    · intro h u
      have hu := h u
      rw [nativeVolumeForm_apply] at hu
      exact hu
    · intro h u
      rw [nativeVolumeForm_apply]
      exact h u]
  exact nativeDot_eq_det3_iff_eq_cross x v w

theorem nativeVolumeForm_ne_zero : nativeVolumeForm ≠ 0 := by
  exact (Pi.basisFun ℝ (Fin 3)).det_ne_zero

theorem nativeVolumeForm_eq_zero_of_eq
    (u : Fin 3 → InfoGeometry.Algebra.FiniteSpin.Vec3R) {i j : Fin 3} (h : u i = u j) (hij : i ≠ j) :
    nativeVolumeForm u = 0 :=
  nativeVolumeForm.map_eq_zero_of_eq u h hij

/-- The exterior-power linear readout induced by the native volume form. -/
noncomputable def nativeVolumeExteriorMap :
    (⋀[ℝ]^3 InfoGeometry.Algebra.FiniteSpin.Vec3R) →ₗ[ℝ] ℝ :=
  exteriorPower.alternatingMapLinearEquiv nativeVolumeForm

theorem nativeVolumeExteriorMap_ιMulti (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeVolumeExteriorMap (exteriorPower.ιMulti ℝ 3 ![u, v, w]) =
      nativeVolumeForm ![u, v, w] := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    nativeVolumeForm ![u, v, w]

theorem nativeVolumeExteriorMap_ιMulti_eq_scalarTriple (u v w : InfoGeometry.Algebra.FiniteSpin.Vec3R) :
    nativeVolumeExteriorMap (exteriorPower.ιMulti ℝ 3 ![u, v, w]) =
      nativeScalarTriple u v w := by
  rw [nativeVolumeExteriorMap_ιMulti, nativeVolumeForm_apply_eq_scalarTriple]

end InfoGeometry.Lie.SplitOctonionCrossTensor
