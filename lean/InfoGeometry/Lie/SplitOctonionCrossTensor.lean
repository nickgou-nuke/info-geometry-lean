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

abbrev Vec3 := InfoGeometry.Algebra.FiniteSpin.Vec3R

/-! The determinant is the native Mathlib determinant of the matrix whose
rows are the three vectors.  Keeping this definition local to the tensor
owner avoids importing any unrelated physics-side determinant alias. -/
def det3 (u v w : Vec3) : ℝ :=
  u 0 * v 1 * w 2 + u 1 * v 2 * w 0 + u 2 * v 0 * w 1 -
    u 0 * v 2 * w 1 - u 1 * v 0 * w 2 - u 2 * v 1 * w 0

theorem nativeCross_eq_mathlib_cross (u v : Vec3) :
    ZornMatrix.cross u v =
      InfoGeometry.Physics.ZornMatrixSU3.crossProduct u v := by
  funext i
  fin_cases i <;>
    simp [ZornMatrix.cross,
      InfoGeometry.Physics.ZornMatrixSU3.crossProduct,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

theorem nativeCross_add_left (u v w : Vec3) :
    ZornMatrix.cross (u + v) w =
      ZornMatrix.cross u w + ZornMatrix.cross v w := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem nativeCross_add_right (u v w : Vec3) :
    ZornMatrix.cross u (v + w) =
      ZornMatrix.cross u v + ZornMatrix.cross u w := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem nativeCross_smul_left (r : ℝ) (u v : Vec3) :
    ZornMatrix.cross (r • u) v = r • ZornMatrix.cross u v := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem nativeCross_smul_right (r : ℝ) (u v : Vec3) :
    ZornMatrix.cross u (r • v) = r • ZornMatrix.cross u v := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem nativeCross_self (u : Vec3) :
    ZornMatrix.cross u u = 0 := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

noncomputable def nativeCrossExteriorAlternating :
    Vec3 [⋀^Fin 2]→ₗ[ℝ] Vec3 := by
  classical
  let f : MultilinearMap ℝ (fun _ : Fin 2 => Vec3) Vec3 :=
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
    (⋀[ℝ]^2 Vec3) →ₗ[ℝ] Vec3 :=
  exteriorPower.alternatingMapLinearEquiv nativeCrossExteriorAlternating

theorem nativeCrossExteriorMap_ιMulti (u v : Vec3) :
    nativeCrossExteriorMap
        (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      ZornMatrix.cross u v := by
  simpa [nativeCrossExteriorMap, nativeCrossExteriorAlternating] using
    (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
      nativeCrossExteriorAlternating ![u, v])

/-- The native cross channel is the contraction of the coordinate
Levi--Civita tensor.  The imported `leviCivita3` is the alternating tensor
owner; this theorem only reads it back in the native Zorn coordinates. -/
theorem nativeCross_eq_leviCivita3 (u v : Vec3) :
    ZornMatrix.cross u v = fun k =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        (leviCivita3 k i j : ℝ) * u i * v j := by
  funext k
  fin_cases k <;>
    simp [ZornMatrix.cross, leviCivita3, Fin.sum_univ_succ] <;>
    ring

/-- The scalar triple product formed from the native Zorn dot and cross. -/
def nativeScalarTriple (u v w : Vec3) : ℝ :=
  ZornMatrix.dot u (ZornMatrix.cross v w)

/-- The native scalar triple product is the full Levi--Civita contraction of
three coordinate vectors. -/
theorem nativeScalarTriple_eq_leviCivita3 (u v w : Vec3) :
    nativeScalarTriple u v w =
      ∑ k : Fin 3, u k *
        (∑ i : Fin 3, ∑ j : Fin 3,
          (leviCivita3 k i j : ℝ) * v i * w j) := by
  rw [nativeScalarTriple, nativeCross_eq_leviCivita3]
  simp [ZornMatrix.dot, Fin.sum_univ_three]

theorem nativeScalarTriple_eq_det3 (u v w : Vec3) :
    nativeScalarTriple u v w = det3 u v w := by
  simp [nativeScalarTriple, ZornMatrix.dot, ZornMatrix.cross, det3]
  ring

theorem nativeScalarTriple_cyclic (u v w : Vec3) :
    nativeScalarTriple u v w = nativeScalarTriple v w u := by
  rw [nativeScalarTriple_eq_det3, nativeScalarTriple_eq_det3]
  simp [det3]
  ring

theorem nativeScalarTriple_swap (u v w : Vec3) :
    nativeScalarTriple u v w = -nativeScalarTriple u w v := by
  rw [nativeScalarTriple_eq_det3, nativeScalarTriple_eq_det3]
  simp [det3]
  ring

theorem nativeScalarTriple_swap_left (u v w : Vec3) :
    nativeScalarTriple u v w = -nativeScalarTriple v u w := by
  calc
    nativeScalarTriple u v w = nativeScalarTriple v w u :=
      nativeScalarTriple_cyclic u v w
    _ = -nativeScalarTriple v u w :=
      nativeScalarTriple_swap v w u

theorem nativeScalarTriple_self_left (u w : Vec3) :
    nativeScalarTriple u u w = 0 := by
  rw [nativeScalarTriple_eq_det3]
  simp [det3]
  ring

theorem nativeScalarTriple_self_right (u v : Vec3) :
    nativeScalarTriple u v v = 0 := by
  rw [nativeScalarTriple_eq_det3]
  simp [det3]
  ring

/-- The native cross channel is orthogonal to its first input. -/
theorem nativeCross_left_orthogonal (v w : Vec3) :
    ZornMatrix.dot v (ZornMatrix.cross v w) = 0 := by
  exact nativeScalarTriple_self_left v w

/-- The native cross channel is orthogonal to its second input. -/
theorem nativeCross_right_orthogonal (v w : Vec3) :
    ZornMatrix.dot w (ZornMatrix.cross v w) = 0 := by
  change nativeScalarTriple w v w = 0
  rw [nativeScalarTriple_swap]
  simp [nativeScalarTriple_self_left]

theorem nativeScalarTriple_cross_cyclic (u v w : Vec3) :
    ZornMatrix.dot (ZornMatrix.cross u v) w =
      ZornMatrix.dot u (ZornMatrix.cross v w) := by
  simp [ZornMatrix.dot, ZornMatrix.cross]
  ring

/-- Swapping the two arguments of the cross channel reverses the scalar
triple pairing. -/
theorem nativeScalarTriple_cross_swap (u v w : Vec3) :
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
theorem nativeCross_eq_of_dot_eq (u v x : Vec3)
    (h : ∀ w, ZornMatrix.dot w x = ZornMatrix.dot w (ZornMatrix.cross u v)) :
    x = ZornMatrix.cross u v := by
  funext i
  have hi := h (Pi.single i 1)
  fin_cases i <;>
    simpa [ZornMatrix.dot, ZornMatrix.cross, Pi.single_apply] using hi

theorem nativeDot_eq_det3_iff_eq_cross (x v w : Vec3) :
    (∀ u : Vec3, ZornMatrix.dot u x = det3 u v w) ↔
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
noncomputable def nativeVolumeForm : Vec3 [⋀^Fin 3]→ₗ[ℝ] ℝ :=
  (Pi.basisFun ℝ (Fin 3)).det

@[simp] theorem nativeVolumeForm_apply (u v w : Vec3) :
    nativeVolumeForm ![u, v, w] = det3 u v w := by
  rw [nativeVolumeForm, Pi.basisFun_det_apply]
  simp [det3, Matrix.det_fin_three]
  ring

@[simp] theorem nativeVolumeForm_apply_eq_scalarTriple (u v w : Vec3) :
    nativeVolumeForm ![u, v, w] = nativeScalarTriple u v w := by
  rw [nativeVolumeForm_apply, nativeScalarTriple_eq_det3]

/-- The cross product is uniquely recovered from the literal alternating
volume map, without mentioning the coordinate determinant in the statement.
This is the finite-dimensional metric/orientation characterization of the
native Zorn cross channel. -/
theorem nativeDot_eq_nativeVolumeForm_iff_eq_cross (x v w : Vec3) :
    (∀ u : Vec3,
      ZornMatrix.dot u x = nativeVolumeForm ![u, v, w]) ↔
      x = ZornMatrix.cross v w := by
  rw [show (∀ u : Vec3,
      ZornMatrix.dot u x = nativeVolumeForm ![u, v, w]) ↔
      (∀ u : Vec3, ZornMatrix.dot u x = det3 u v w) by
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
    (u : Fin 3 → Vec3) {i j : Fin 3} (h : u i = u j) (hij : i ≠ j) :
    nativeVolumeForm u = 0 :=
  nativeVolumeForm.map_eq_zero_of_eq u h hij

/-- The exterior-power linear readout induced by the native volume form. -/
noncomputable def nativeVolumeExteriorMap :
    (⋀[ℝ]^3 Vec3) →ₗ[ℝ] ℝ :=
  exteriorPower.alternatingMapLinearEquiv nativeVolumeForm

theorem nativeVolumeExteriorMap_ιMulti (u v w : Vec3) :
    nativeVolumeExteriorMap (exteriorPower.ιMulti ℝ 3 ![u, v, w]) =
      nativeVolumeForm ![u, v, w] := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    nativeVolumeForm ![u, v, w]

theorem nativeVolumeExteriorMap_ιMulti_eq_scalarTriple (u v w : Vec3) :
    nativeVolumeExteriorMap (exteriorPower.ιMulti ℝ 3 ![u, v, w]) =
      nativeScalarTriple u v w := by
  rw [nativeVolumeExteriorMap_ιMulti, nativeVolumeForm_apply_eq_scalarTriple]

end InfoGeometry.Lie.SplitOctonionCrossTensor
