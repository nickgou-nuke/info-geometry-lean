import InfoGeometry.Algebra.H3ZornRationalCoordinates
import InfoGeometry.Algebra.H3ZornCoordinateReadback

/-! The canonical coefficient embedding from the rational shadow into the real
split Albert carrier. -/

namespace InfoGeometry.Algebra

open H3Zorn

noncomputable def zornRatRealCast (X : ZornVectorMatrix ℚ) : ZornVectorMatrix ℝ :=
  ⟨algebraMap ℚ ℝ X.a, fun i => algebraMap ℚ ℝ (X.v i),
    fun i => algebraMap ℚ ℝ (X.w i), algebraMap ℚ ℝ X.b⟩

noncomputable def h3ZornRatRealCast (X : H3Zorn ℚ) : H3Zorn ℝ :=
  ⟨algebraMap ℚ ℝ X.α₁, algebraMap ℚ ℝ X.α₂, algebraMap ℚ ℝ X.α₃,
    zornRatRealCast X.a, zornRatRealCast X.b, zornRatRealCast X.c⟩

@[simp] theorem h3ZornRatRealCast_zero :
    h3ZornRatRealCast (0 : H3Zorn ℚ) = 0 := by
  apply H3Zorn.ext_h3 <;>
    simp [h3ZornRatRealCast, zornRatRealCast, H3Zorn.zero_readback,
      ZornVectorMatrix.zero]

@[simp] theorem h3ZornRatRealCast_one :
    h3ZornRatRealCast (1 : H3Zorn ℚ) = 1 := by
  apply H3Zorn.ext_h3 <;>
    simp [h3ZornRatRealCast, zornRatRealCast, H3Zorn.one_readback,
      ZornVectorMatrix.zero]

theorem zornRatRealCast_add (X Y : ZornVectorMatrix ℚ) :
    zornRatRealCast (X + Y) = zornRatRealCast X + zornRatRealCast Y := by
  apply ZornVectorMatrix.ext
  · simp [zornRatRealCast, ZornVectorMatrix.add, map_add]
  · funext i; simp [zornRatRealCast, ZornVectorMatrix.add, map_add]
  · funext i; simp [zornRatRealCast, ZornVectorMatrix.add, map_add]
  · simp [zornRatRealCast, ZornVectorMatrix.add, map_add]

theorem h3ZornRatRealCast_add (X Y : H3Zorn ℚ) :
    h3ZornRatRealCast (X + Y) =
      h3ZornRatRealCast X + h3ZornRatRealCast Y := by
  apply H3Zorn.ext_h3 <;>
    simp [h3ZornRatRealCast, zornRatRealCast, H3Zorn.add_readback,
      ZornVectorMatrix.add, map_add]

theorem zornRatRealCast_conj (X : ZornVectorMatrix ℚ) :
    zornRatRealCast (ZornVectorMatrix.conj X) =
      ZornVectorMatrix.conj (zornRatRealCast X) := by
  apply ZornVectorMatrix.ext
  · simp [zornRatRealCast, ZornVectorMatrix.conj]
  · funext i
    simp [zornRatRealCast, ZornVectorMatrix.conj]
  · funext i
    simp [zornRatRealCast, ZornVectorMatrix.conj]
  · simp [zornRatRealCast, ZornVectorMatrix.conj]

theorem zornRatRealCast_neg (X : ZornVectorMatrix ℚ) :
    zornRatRealCast (-X) = -zornRatRealCast X := by
  apply ZornVectorMatrix.ext <;>
    simp [zornRatRealCast, ZornVectorMatrix.neg, map_neg]

theorem h3ZornRatRealCast_neg (X : H3Zorn ℚ) :
    h3ZornRatRealCast (-X) = -h3ZornRatRealCast X := by
  apply H3Zorn.ext_h3
  · simp [h3ZornRatRealCast, H3Zorn.neg_readback, map_neg]
  · simp [h3ZornRatRealCast, H3Zorn.neg_readback, map_neg]
  · simp [h3ZornRatRealCast, H3Zorn.neg_readback, map_neg]
  · simpa [h3ZornRatRealCast, H3Zorn.neg_readback] using zornRatRealCast_neg X.a
  · simpa [h3ZornRatRealCast, H3Zorn.neg_readback] using zornRatRealCast_neg X.b
  · simpa [h3ZornRatRealCast, H3Zorn.neg_readback] using zornRatRealCast_neg X.c

theorem zornRatRealCast_mul (X Y : ZornVectorMatrix ℚ) :
    zornRatRealCast (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.mul (zornRatRealCast X) (zornRatRealCast Y) := by
  apply ZornVectorMatrix.ext
  · simp [zornRatRealCast, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, map_add, map_sub, map_mul]
  · funext i
    fin_cases i <;>
      simp [zornRatRealCast, ZornVectorMatrix.mul, ZornVec3.dot,
        ZornVec3.cross, map_add, map_sub, map_mul]
  · funext i
    fin_cases i <;>
      simp [zornRatRealCast, ZornVectorMatrix.mul, ZornVec3.dot,
        ZornVec3.cross, map_add, map_sub, map_mul]
  · simp [zornRatRealCast, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, map_add, map_sub, map_mul]

theorem zornRatRealCast_trace (X : ZornVectorMatrix ℚ) :
    (algebraMap ℚ ℝ) (ZornVectorMatrix.trace X) =
      ZornVectorMatrix.trace (zornRatRealCast X) := by
  simp [ZornVectorMatrix.trace, zornRatRealCast, map_add]

theorem zornRatRealCast_norm (X : ZornVectorMatrix ℚ) :
    (algebraMap ℚ ℝ) (ZornVectorMatrix.norm X) =
      ZornVectorMatrix.norm (zornRatRealCast X) := by
  simp [ZornVectorMatrix.norm, zornRatRealCast, ZornVec3.dot,
    map_sub, map_mul]

theorem zornRatRealCast_smul (q : ℚ) (X : ZornVectorMatrix ℚ) :
    zornRatRealCast (q • X) =
      (algebraMap ℚ ℝ q) • zornRatRealCast X := by
  apply ZornVectorMatrix.ext
  · simp [zornRatRealCast, ZornVectorMatrix.smul, map_mul]
  · funext i
    fin_cases i <;> simp [zornRatRealCast, ZornVectorMatrix.smul, map_mul]
  · funext i
    fin_cases i <;> simp [zornRatRealCast, ZornVectorMatrix.smul, map_mul]
  · simp [zornRatRealCast, ZornVectorMatrix.smul, map_mul]

theorem zornRatRealCast_trace_mul_conj (X Y : ZornVectorMatrix ℚ) :
    (algebraMap ℚ ℝ) (ZornVectorMatrix.trace (X.mul Y.conj)) =
      ZornVectorMatrix.trace ((zornRatRealCast X).mul (zornRatRealCast Y).conj) := by
  calc
    (algebraMap ℚ ℝ) (ZornVectorMatrix.trace (X.mul Y.conj)) =
        ZornVectorMatrix.trace (zornRatRealCast (X.mul Y.conj)) :=
      zornRatRealCast_trace (X.mul Y.conj)
    _ = ZornVectorMatrix.trace ((zornRatRealCast X).mul (zornRatRealCast Y).conj) := by
      rw [zornRatRealCast_mul, zornRatRealCast_conj]

theorem zornRatRealCast_add_neg_smul_mul (U V W : ZornVectorMatrix ℚ) (q : ℚ) :
    zornRatRealCast ((U.mul V).add (-(q • W))) =
      ZornVectorMatrix.add
        ((zornRatRealCast U).mul (zornRatRealCast V))
        (-((algebraMap ℚ ℝ q) • zornRatRealCast W)) := by
  apply ZornVectorMatrix.ext
  · simp [zornRatRealCast, ZornVectorMatrix.add, ZornVectorMatrix.mul,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVec3.dot,
      ZornVec3.cross, map_add, map_sub, map_mul]
  · funext i
    fin_cases i <;>
      simp [zornRatRealCast, ZornVectorMatrix.add, ZornVectorMatrix.mul,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVec3.dot,
        ZornVec3.cross, map_add, map_sub, map_mul]
  · funext i
    fin_cases i <;>
      simp [zornRatRealCast, ZornVectorMatrix.add, ZornVectorMatrix.mul,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVec3.dot,
        ZornVec3.cross, map_add, map_sub, map_mul]
  · simp [zornRatRealCast, ZornVectorMatrix.add, ZornVectorMatrix.mul,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVec3.dot,
      ZornVec3.cross, map_add, map_sub, map_mul]

theorem h3ZornRatRealCast_smul (q : ℚ) (X : H3Zorn ℚ) :
    h3ZornRatRealCast (q • X) =
      (algebraMap ℚ ℝ q) • h3ZornRatRealCast X := by
  apply H3Zorn.ext_h3 <;>
    simp [h3ZornRatRealCast, zornRatRealCast, H3Zorn.smul_readback,
      ZornVectorMatrix.smul, map_mul]

theorem h3ZornRatRealCast_sub (X Y : H3Zorn ℚ) :
    h3ZornRatRealCast (X - Y) =
      h3ZornRatRealCast X - h3ZornRatRealCast Y := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [h3ZornRatRealCast_add]
  rw [h3ZornRatRealCast_neg]

theorem h3ZornRatRealCast_adjointQuad (X : H3Zorn ℚ) :
    h3ZornRatRealCast (H3Zorn.adjointQuad X) =
      H3Zorn.adjointQuad (h3ZornRatRealCast X) := by
  apply H3Zorn.ext_h3
  · simp [H3ZornCoordinateReadback.adjointQuad_α₁, h3ZornRatRealCast, zornRatRealCast,
      zornRatRealCast_norm, ZornVectorMatrix.norm, ZornVec3.dot, map_sub, map_mul] <;>
      push_cast <;> exact_mod_cast rfl
  · simp [H3ZornCoordinateReadback.adjointQuad_α₂, h3ZornRatRealCast, zornRatRealCast,
      zornRatRealCast_norm,
      ZornVectorMatrix.sub, ZornVectorMatrix.norm, ZornVec3.dot, map_sub, map_mul] <;>
      push_cast <;> exact_mod_cast rfl
  · simp [H3ZornCoordinateReadback.adjointQuad_α₃, h3ZornRatRealCast, zornRatRealCast,
      zornRatRealCast_norm,
      ZornVectorMatrix.sub, ZornVectorMatrix.norm, ZornVec3.dot, map_sub, map_mul] <;>
      push_cast <;> exact_mod_cast rfl
  · simpa [H3Zorn.adjointQuad, h3ZornRatRealCast,
      zornRatRealCast_conj, ZornVectorMatrix.sub, ZornVectorMatrix.smul] using
    (zornRatRealCast_add_neg_smul_mul X.c.conj X.b.conj X.a X.α₃)
  · simpa [H3Zorn.adjointQuad, h3ZornRatRealCast,
      zornRatRealCast_conj, ZornVectorMatrix.sub, ZornVectorMatrix.smul] using
    (zornRatRealCast_add_neg_smul_mul X.a.conj X.c.conj X.b X.α₁)
  · simpa [H3Zorn.adjointQuad, h3ZornRatRealCast,
      zornRatRealCast_conj, ZornVectorMatrix.sub, ZornVectorMatrix.smul] using
    (zornRatRealCast_add_neg_smul_mul X.b.conj X.a.conj X.c X.α₂)

theorem h3ZornRatRealCast_crossProduct (X Y : H3Zorn ℚ) :
    h3ZornRatRealCast (H3Zorn.crossProduct X Y) =
      H3Zorn.crossProduct (h3ZornRatRealCast X) (h3ZornRatRealCast Y) := by
  simp [H3Zorn.crossProduct, h3ZornRatRealCast_add,
    h3ZornRatRealCast_adjointQuad, h3ZornRatRealCast_sub]

theorem h3ZornRatRealCast_traceBilin (X Y : H3Zorn ℚ) :
    (algebraMap ℚ ℝ) (H3Zorn.traceBilin X Y) =
      H3Zorn.traceBilin (h3ZornRatRealCast X) (h3ZornRatRealCast Y) := by
  simp only [H3Zorn.traceBilin, h3ZornRatRealCast, map_add, map_mul]
  rw [zornRatRealCast_trace_mul_conj X.a Y.a,
    zornRatRealCast_trace_mul_conj X.b Y.b,
    zornRatRealCast_trace_mul_conj X.c Y.c]

theorem h3ZornRatRealCast_T (X Y Z : H3Zorn ℚ) :
    h3ZornRatRealCast (H3Zorn.T X Y Z) =
      H3Zorn.T (h3ZornRatRealCast X)
        (h3ZornRatRealCast Y) (h3ZornRatRealCast Z) := by
  rw [H3Zorn.T_outer_formula, H3Zorn.T_outer_formula]
  simp only [h3ZornRatRealCast_sub, h3ZornRatRealCast_add,
    h3ZornRatRealCast_smul, h3ZornRatRealCast_crossProduct,
    h3ZornRatRealCast_traceBilin, map_sub, map_add, map_mul]

theorem h3ZornRatRealCast_cubicJordanMul (X Y : H3Zorn ℚ) :
    h3ZornRatRealCast (cubicJordanMul X Y) =
      cubicJordanMul (h3ZornRatRealCast X) (h3ZornRatRealCast Y) := by
  simp [cubicJordanMul, h3ZornRatRealCast_T, h3ZornRatRealCast_one,
    h3ZornRatRealCast_smul, map_inv₀]

theorem h3ZornRatRealCast_cubicJordanInnerAction
    (A B X : H3Zorn ℚ) :
    h3ZornRatRealCast (cubicJordanInnerAction A B X) =
      cubicJordanInnerAction (h3ZornRatRealCast A)
        (h3ZornRatRealCast B) (h3ZornRatRealCast X) := by
  simp [cubicJordanInnerAction, h3ZornRatRealCast_cubicJordanMul,
    h3ZornRatRealCast_sub]

theorem h3ZornRatRealCast_coordinate (X : H3Zorn ℚ) (j : Fin 27) :
    (algebraMap ℚ ℝ) (h3ZornCoordinateR X j) =
      h3ZornCoordinateR (h3ZornRatRealCast X) j := by
  fin_cases j <;>
    simp [h3ZornCoordinateR, h3ZornRatRealCast, zornRatRealCast,
      map_zero, map_one]

theorem h3ZornRatRealCast_innerAction_coordinate
    (A B X : H3Zorn ℚ) (j : Fin 27) :
    (algebraMap ℚ ℝ)
        (h3ZornCoordinateR (cubicJordanInnerAction A B X) j) =
      h3ZornCoordinateR
        (cubicJordanInnerAction (h3ZornRatRealCast A)
          (h3ZornRatRealCast B) (h3ZornRatRealCast X)) j := by
  calc
    (algebraMap ℚ ℝ)
        (h3ZornCoordinateR (cubicJordanInnerAction A B X) j) =
      h3ZornCoordinateR
        (h3ZornRatRealCast (cubicJordanInnerAction A B X)) j :=
          h3ZornRatRealCast_coordinate _ _
    _ = _ := by rw [h3ZornRatRealCast_cubicJordanInnerAction]

end InfoGeometry.Algebra
