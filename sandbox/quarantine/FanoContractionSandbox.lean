import InfoGeometry.Clifford.FanoOctonionParavector

open InfoGeometry.Clifford.FanoOctonionParavector
open InfoGeometry.Clifford.OctonionParavectorBridge

set_option maxHeartbeats 1500000

noncomputable section

-- The raw coordinate Fano-plane cross product on `Fin 7 → ℝ` with corrected alternative signs.
def fanoCrossRawSandbox (u v : R7) : R7 := ![
  (u 1 * v 2 - u 2 * v 1) + (u 3 * v 4 - u 4 * v 3) + (u 5 * v 6 - u 6 * v 5),
  (u 2 * v 0 - u 0 * v 2) - (u 3 * v 5 - u 5 * v 3) + (u 4 * v 6 - u 6 * v 4),
  (u 0 * v 1 - u 1 * v 0) + (u 3 * v 6 - u 6 * v 3) + (u 4 * v 5 - u 5 * v 4),
  (u 4 * v 0 - u 0 * v 4) - (u 5 * v 1 - u 1 * v 5) + (u 6 * v 2 - u 2 * v 6),
  (u 0 * v 3 - u 3 * v 0) + (u 6 * v 1 - u 1 * v 6) + (u 5 * v 2 - u 2 * v 5),
  (u 6 * v 0 - u 0 * v 6) - (u 1 * v 3 - u 3 * v 1) + (u 2 * v 4 - u 4 * v 2),
  (u 0 * v 5 - u 5 * v 0) + (u 1 * v 4 - u 4 * v 1) + (u 2 * v 3 - u 3 * v 2)
]

theorem fanoCrossRawSandbox_add_left (u w v : R7) :
    fanoCrossRawSandbox (u + w) v = fanoCrossRawSandbox u v + fanoCrossRawSandbox w v := by
  ext k <;> fin_cases k <;> simp [fanoCrossRawSandbox] <;> ring

theorem fanoCrossRawSandbox_smul_left (a : ℝ) (u v : R7) :
    fanoCrossRawSandbox (a • u) v = a • fanoCrossRawSandbox u v := by
  ext k <;> fin_cases k <;> simp [fanoCrossRawSandbox] <;> ring

theorem fanoCrossRawSandbox_add_right (u v w : R7) :
    fanoCrossRawSandbox u (v + w) = fanoCrossRawSandbox u v + fanoCrossRawSandbox u w := by
  ext k <;> fin_cases k <;> simp [fanoCrossRawSandbox] <;> ring

theorem fanoCrossRawSandbox_smul_right (a : ℝ) (u v : R7) :
    fanoCrossRawSandbox u (a • v) = a • fanoCrossRawSandbox u v := by
  ext k <;> fin_cases k <;> simp [fanoCrossRawSandbox] <;> ring

/-- The Fano-plane cross product bundled as a bilinear map. -/
def fanoCrossSandbox : R7 →ₗ[ℝ] R7 →ₗ[ℝ] R7 :=
  LinearMap.mk₂ ℝ fanoCrossRawSandbox
    fanoCrossRawSandbox_add_left
    fanoCrossRawSandbox_smul_left
    fanoCrossRawSandbox_add_right
    fanoCrossRawSandbox_smul_right

theorem fanoCrossSandbox_self (u : R7) :
    fanoCrossSandbox u u = 0 := by
  ext k <;> fin_cases k <;> simp [fanoCrossSandbox, fanoCrossRawSandbox] <;> ring

theorem fanoCrossSandbox_anticomm (u v : R7) :
    fanoCrossSandbox v u = - fanoCrossSandbox u v := by
  ext k <;> fin_cases k <;> simp [fanoCrossSandbox, fanoCrossRawSandbox] <;> ring

/-- Concrete paravector data for the Fano-plane alternative octonions in the sandbox. -/
def fanoOctonionParavectorDataSandbox : OctonionParavectorData R7 where
  inner := dot7
  cross := fanoCrossSandbox
  inner_symm := dot7_symm
  cross_self := fanoCrossSandbox_self
  cross_anticomm := fanoCrossSandbox_anticomm

-- Concrete triangle of vecCons evaluation lemmas to resolve Fin 7 lookups
theorem cons_val_3_7 {α} (x : α) (u : Fin 6 → α) : Matrix.vecCons x u (3 : Fin 7) = u 2 := rfl
theorem cons_val_4_7 {α} (x : α) (u : Fin 6 → α) : Matrix.vecCons x u (4 : Fin 7) = u 3 := rfl
theorem cons_val_5_7 {α} (x : α) (u : Fin 6 → α) : Matrix.vecCons x u (5 : Fin 7) = u 4 := rfl
theorem cons_val_6_7 {α} (x : α) (u : Fin 6 → α) : Matrix.vecCons x u (6 : Fin 7) = u 5 := rfl

theorem cons_val_3_6 {α} (x : α) (u : Fin 5 → α) : Matrix.vecCons x u (3 : Fin 6) = u 2 := rfl
theorem cons_val_4_6 {α} (x : α) (u : Fin 5 → α) : Matrix.vecCons x u (4 : Fin 6) = u 3 := rfl
theorem cons_val_5_6 {α} (x : α) (u : Fin 5 → α) : Matrix.vecCons x u (5 : Fin 6) = u 4 := rfl

theorem cons_val_3_5 {α} (x : α) (u : Fin 4 → α) : Matrix.vecCons x u (3 : Fin 5) = u 2 := rfl
theorem cons_val_4_5 {α} (x : α) (u : Fin 4 → α) : Matrix.vecCons x u (4 : Fin 5) = u 3 := rfl

theorem cons_val_3_4 {α} (x : α) (u : Fin 3 → α) : Matrix.vecCons x u (3 : Fin 4) = u 2 := rfl

/-- Helper to expand Fin 7 sums. -/
theorem sum_univ_seven (f : Fin 7 → ℝ) :
    (∑ i : Fin 7, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp [Fin.sum_univ_succ]
  ring

@[simp] theorem fanoCrossSandbox_apply (u v : R7) : fanoCrossSandbox u v = fanoCrossRawSandbox u v := rfl
@[simp] theorem dot7_apply (u v : R7) : dot7 u v = ∑ i, u i * v i := rfl

theorem fanoCrossRawSandbox_self (u : R7) : fanoCrossRawSandbox u u = 0 := by
  ext k
  fin_cases k <;> simp [fanoCrossRawSandbox] <;> ring

abbrev OctonionFano := Paravector R7

def octMul (x y : OctonionFano) : OctonionFano :=
  paravectorMul fanoOctonionParavectorDataSandbox x y

/-! ## Left Alternativity modular components -/

theorem octonion_alt_left_fst (x y : OctonionFano) :
    (octMul (octMul x y) x).1 = (octMul x (octMul y x)).1 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_left_snd_0 (x y : OctonionFano) :
    (octMul (octMul x y) x).2 0 = (octMul x (octMul y x)).2 0 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_left_snd_1 (x y : OctonionFano) :
    (octMul (octMul x y) x).2 1 = (octMul x (octMul y x)).2 1 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_left_snd_2 (x y : OctonionFano) :
    (octMul (octMul x y) x).2 2 = (octMul x (octMul y x)).2 2 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_left_snd_3 (x y : OctonionFano) :
    (octMul (octMul x y) x).2 3 = (octMul x (octMul y x)).2 3 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_left_snd_4 (x y : OctonionFano) :
    (octMul (octMul x y) x).2 4 = (octMul x (octMul y x)).2 4 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_left_snd_5 (x y : OctonionFano) :
    (octMul (octMul x y) x).2 5 = (octMul x (octMul y x)).2 5 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_left_snd_6 (x y : OctonionFano) :
    (octMul (octMul x y) x).2 6 = (octMul x (octMul y x)).2 6 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_left (x y : OctonionFano) :
    octMul (octMul x y) x = octMul x (octMul y x) := by
  ext i
  · exact octonion_alt_left_fst x y
  · fin_cases i
    · exact octonion_alt_left_snd_0 x y
    · exact octonion_alt_left_snd_1 x y
    · exact octonion_alt_left_snd_2 x y
    · exact octonion_alt_left_snd_3 x y
    · exact octonion_alt_left_snd_4 x y
    · exact octonion_alt_left_snd_5 x y
    · exact octonion_alt_left_snd_6 x y

/-! ## Right Alternativity modular components -/

theorem octonion_alt_right_fst (x y : OctonionFano) :
    (octMul (octMul x x) y).1 = (octMul x (octMul x y)).1 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_right_snd_0 (x y : OctonionFano) :
    (octMul (octMul x x) y).2 0 = (octMul x (octMul x y)).2 0 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_right_snd_1 (x y : OctonionFano) :
    (octMul (octMul x x) y).2 1 = (octMul x (octMul x y)).2 1 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_right_snd_2 (x y : OctonionFano) :
    (octMul (octMul x x) y).2 2 = (octMul x (octMul x y)).2 2 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_right_snd_3 (x y : OctonionFano) :
    (octMul (octMul x x) y).2 3 = (octMul x (octMul x y)).2 3 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_right_snd_4 (x y : OctonionFano) :
    (octMul (octMul x x) y).2 4 = (octMul x (octMul x y)).2 4 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_right_snd_5 (x y : OctonionFano) :
    (octMul (octMul x x) y).2 5 = (octMul x (octMul x y)).2 5 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_right_snd_6 (x y : OctonionFano) :
    (octMul (octMul x x) y).2 6 = (octMul x (octMul x y)).2 6 := by
  simp only [octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven, fanoCrossSandbox_self, fanoCrossRawSandbox_self]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  norm_num
  ring

theorem octonion_alt_right (x y : OctonionFano) :
    octMul (octMul x x) y = octMul x (octMul x y) := by
  ext i
  · exact octonion_alt_right_fst x y
  · fin_cases i
    · exact octonion_alt_right_snd_0 x y
    · exact octonion_alt_right_snd_1 x y
    · exact octonion_alt_right_snd_2 x y
    · exact octonion_alt_right_snd_3 x y
    · exact octonion_alt_right_snd_4 x y
    · exact octonion_alt_right_snd_5 x y
    · exact octonion_alt_right_snd_6 x y

/-! ## Orthogonality, Lagrange Identity, and Norm Multiplicativity -/

/-- Paravector split-octonion quadratic norm. -/
def octNorm (x : OctonionFano) : ℝ :=
  x.1 * x.1 + dot7 x.2 x.2

theorem fanoCrossSandbox_orthogonal_left (u v : R7) :
    dot7 u (fanoCrossRawSandbox u v) = 0 := by
  simp only [dot7_apply, sum_univ_seven]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  ring

theorem fanoCrossSandbox_orthogonal_right (u v : R7) :
    dot7 v (fanoCrossRawSandbox u v) = 0 := by
  simp only [dot7_apply, sum_univ_seven]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  ring

theorem fanoCrossSandbox_lagrange (u v : R7) :
    dot7 (fanoCrossRawSandbox u v) (fanoCrossRawSandbox u v) = dot7 u u * dot7 v v - (dot7 u v)^2 := by
  simp only [dot7_apply, sum_univ_seven]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  ring

theorem octonion_norm_mul (x y : OctonionFano) :
    octNorm (octMul x y) = octNorm x * octNorm y := by
  simp only [octNorm, octMul, paravectorMul, fanoOctonionParavectorDataSandbox, fanoCrossSandbox_apply, dot7_apply, sum_univ_seven]
  simp only [fanoCrossRawSandbox, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    Function.comp_apply, smul_eq_mul,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    cons_val_3_7, cons_val_4_7, cons_val_5_7, cons_val_6_7,
    cons_val_3_6, cons_val_4_6, cons_val_5_6,
    cons_val_3_5, cons_val_4_5,
    cons_val_3_4]
  ring
