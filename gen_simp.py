with open("lean/InfoGeometry/Algebra/RealSplitOctSimp.lean", "w") as f:
    f.write("""import InfoGeometry.Algebra.RealSplitAlbert

namespace InfoGeometry.Algebra.RealSplitOct

@[simp] lemma add_a (X Y : RealSplitOct) : (X + Y).a = X.a + Y.a := rfl
@[simp] lemma add_b (X Y : RealSplitOct) : (X + Y).b = X.b + Y.b := rfl
@[simp] lemma add_x0 (X Y : RealSplitOct) : (X + Y).x0 = X.x0 + Y.x0 := rfl
@[simp] lemma add_x1 (X Y : RealSplitOct) : (X + Y).x1 = X.x1 + Y.x1 := rfl
@[simp] lemma add_x2 (X Y : RealSplitOct) : (X + Y).x2 = X.x2 + Y.x2 := rfl
@[simp] lemma add_y0 (X Y : RealSplitOct) : (X + Y).y0 = X.y0 + Y.y0 := rfl
@[simp] lemma add_y1 (X Y : RealSplitOct) : (X + Y).y1 = X.y1 + Y.y1 := rfl
@[simp] lemma add_y2 (X Y : RealSplitOct) : (X + Y).y2 = X.y2 + Y.y2 := rfl

@[simp] lemma sub_a (X Y : RealSplitOct) : (X - Y).a = X.a - Y.a := rfl
@[simp] lemma sub_b (X Y : RealSplitOct) : (X - Y).b = X.b - Y.b := rfl
@[simp] lemma sub_x0 (X Y : RealSplitOct) : (X - Y).x0 = X.x0 - Y.x0 := rfl
@[simp] lemma sub_x1 (X Y : RealSplitOct) : (X - Y).x1 = X.x1 - Y.x1 := rfl
@[simp] lemma sub_x2 (X Y : RealSplitOct) : (X - Y).x2 = X.x2 - Y.x2 := rfl
@[simp] lemma sub_y0 (X Y : RealSplitOct) : (X - Y).y0 = X.y0 - Y.y0 := rfl
@[simp] lemma sub_y1 (X Y : RealSplitOct) : (X - Y).y1 = X.y1 - Y.y1 := rfl
@[simp] lemma sub_y2 (X Y : RealSplitOct) : (X - Y).y2 = X.y2 - Y.y2 := rfl

@[simp] lemma smul_a_tc (r : ℝ) (X : RealSplitOct) : (r • X).a = r * X.a := rfl
@[simp] lemma smul_b_tc (r : ℝ) (X : RealSplitOct) : (r • X).b = r * X.b := rfl
@[simp] lemma smul_x0_tc (r : ℝ) (X : RealSplitOct) : (r • X).x0 = r * X.x0 := rfl
@[simp] lemma smul_x1_tc (r : ℝ) (X : RealSplitOct) : (r • X).x1 = r * X.x1 := rfl
@[simp] lemma smul_x2_tc (r : ℝ) (X : RealSplitOct) : (r • X).x2 = r * X.x2 := rfl
@[simp] lemma smul_y0_tc (r : ℝ) (X : RealSplitOct) : (r • X).y0 = r * X.y0 := rfl
@[simp] lemma smul_y1_tc (r : ℝ) (X : RealSplitOct) : (r • X).y1 = r * X.y1 := rfl
@[simp] lemma smul_y2_tc (r : ℝ) (X : RealSplitOct) : (r • X).y2 = r * X.y2 := rfl

@[simp] lemma smul_a (r : ℝ) (X : RealSplitOct) : (smul r X).a = r * X.a := rfl
@[simp] lemma smul_b (r : ℝ) (X : RealSplitOct) : (smul r X).b = r * X.b := rfl
@[simp] lemma smul_x0 (r : ℝ) (X : RealSplitOct) : (smul r X).x0 = r * X.x0 := rfl
@[simp] lemma smul_x1 (r : ℝ) (X : RealSplitOct) : (smul r X).x1 = r * X.x1 := rfl
@[simp] lemma smul_x2 (r : ℝ) (X : RealSplitOct) : (smul r X).x2 = r * X.x2 := rfl
@[simp] lemma smul_y0 (r : ℝ) (X : RealSplitOct) : (smul r X).y0 = r * X.y0 := rfl
@[simp] lemma smul_y1 (r : ℝ) (X : RealSplitOct) : (smul r X).y1 = r * X.y1 := rfl
@[simp] lemma smul_y2 (r : ℝ) (X : RealSplitOct) : (smul r X).y2 = r * X.y2 := rfl


@[simp] lemma conj_a (X : RealSplitOct) : X.conj.a = X.b := rfl
@[simp] lemma conj_b (X : RealSplitOct) : X.conj.b = X.a := rfl
@[simp] lemma conj_x0 (X : RealSplitOct) : X.conj.x0 = -X.x0 := rfl
@[simp] lemma conj_x1 (X : RealSplitOct) : X.conj.x1 = -X.x1 := rfl
@[simp] lemma conj_x2 (X : RealSplitOct) : X.conj.x2 = -X.x2 := rfl
@[simp] lemma conj_y0 (X : RealSplitOct) : X.conj.y0 = -X.y0 := rfl
@[simp] lemma conj_y1 (X : RealSplitOct) : X.conj.y1 = -X.y1 := rfl
@[simp] lemma conj_y2 (X : RealSplitOct) : X.conj.y2 = -X.y2 := rfl

@[simp] lemma zero_a : (0 : RealSplitOct).a = 0 := rfl
@[simp] lemma zero_b : (0 : RealSplitOct).b = 0 := rfl
@[simp] lemma zero_x0 : (0 : RealSplitOct).x0 = 0 := rfl
@[simp] lemma zero_x1 : (0 : RealSplitOct).x1 = 0 := rfl
@[simp] lemma zero_x2 : (0 : RealSplitOct).x2 = 0 := rfl
@[simp] lemma zero_y0 : (0 : RealSplitOct).y0 = 0 := rfl
@[simp] lemma zero_y1 : (0 : RealSplitOct).y1 = 0 := rfl
@[simp] lemma zero_y2 : (0 : RealSplitOct).y2 = 0 := rfl

@[simp] lemma mul_a (X Y : RealSplitOct) : (X.mul Y).a = X.a * Y.a + (X.x0 * Y.y0 + X.x1 * Y.y1 + X.x2 * Y.y2) := rfl
@[simp] lemma mul_b (X Y : RealSplitOct) : (X.mul Y).b = X.b * Y.b + (X.y0 * Y.x0 + X.y1 * Y.x1 + X.y2 * Y.x2) := rfl
@[simp] lemma mul_x0 (X Y : RealSplitOct) : (X.mul Y).x0 = X.a * Y.x0 + Y.b * X.x0 - (X.y1 * Y.y2 - X.y2 * Y.y1) := rfl
@[simp] lemma mul_x1 (X Y : RealSplitOct) : (X.mul Y).x1 = X.a * Y.x1 + Y.b * X.x1 - (X.y2 * Y.y0 - X.y0 * Y.y2) := rfl
@[simp] lemma mul_x2 (X Y : RealSplitOct) : (X.mul Y).x2 = X.a * Y.x2 + Y.b * X.x2 - (X.y0 * Y.y1 - X.y1 * Y.y0) := rfl
@[simp] lemma mul_y0 (X Y : RealSplitOct) : (X.mul Y).y0 = Y.a * X.y0 + X.b * Y.y0 + (X.x1 * Y.x2 - X.x2 * Y.x1) := rfl
@[simp] lemma mul_y1 (X Y : RealSplitOct) : (X.mul Y).y1 = Y.a * X.y1 + X.b * Y.y1 + (X.x2 * Y.x0 - X.x0 * Y.x2) := rfl
@[simp] lemma mul_y2 (X Y : RealSplitOct) : (X.mul Y).y2 = Y.a * X.y2 + X.b * Y.y2 + (X.x0 * Y.x1 - X.x1 * Y.x0) := rfl

end InfoGeometry.Algebra.RealSplitOct
""")
