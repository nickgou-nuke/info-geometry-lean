import Mathlib

set_option autoImplicit false

namespace Audit.SuperTraceBerezinian

/--
A ℤ₂-graded 2×2 supermatrix with scalar entries (1|1)-dimensional case.
-/
structure SuperMatrix (R : Type*) [CommRing R] where
  a : R
  b : R
  c : R
  d : R

namespace SuperMatrix

variable {R : Type*} [CommRing R]

@[ext]
theorem ext' (M N : SuperMatrix R) (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  cases M; cases N; subst ha; subst hb; subst hc; subst hd; rfl

instance : Add (SuperMatrix R) := ⟨λ M N => ⟨M.a + N.a, M.b + N.b, M.c + N.c, M.d + N.d⟩⟩
instance : Zero (SuperMatrix R) := ⟨⟨0,0,0,0⟩⟩
instance : Neg (SuperMatrix R) := ⟨λ M => ⟨-M.a, -M.b, -M.c, -M.d⟩⟩

@[simp] theorem add_a (M N : SuperMatrix R) : (M + N).a = M.a + N.a := rfl
@[simp] theorem add_b (M N : SuperMatrix R) : (M + N).b = M.b + N.b := rfl
@[simp] theorem add_c (M N : SuperMatrix R) : (M + N).c = M.c + N.c := rfl
@[simp] theorem add_d (M N : SuperMatrix R) : (M + N).d = M.d + N.d := rfl
@[simp] theorem zero_a : (0 : SuperMatrix R).a = 0 := rfl
@[simp] theorem zero_b : (0 : SuperMatrix R).b = 0 := rfl
@[simp] theorem zero_c : (0 : SuperMatrix R).c = 0 := rfl
@[simp] theorem zero_d : (0 : SuperMatrix R).d = 0 := rfl
@[simp] theorem neg_a (M : SuperMatrix R) : (-M).a = -M.a := rfl
@[simp] theorem neg_b (M : SuperMatrix R) : (-M).b = -M.b := rfl
@[simp] theorem neg_c (M : SuperMatrix R) : (-M).c = -M.c := rfl
@[simp] theorem neg_d (M : SuperMatrix R) : (-M).d = -M.d := rfl

instance : AddCommGroup (SuperMatrix R) := {
  add := (· + ·)
  zero := 0
  neg := (-·)
  add_assoc := by intro M N P; ext <;> exact add_assoc _ _ _
  zero_add := by intro M; ext <;> exact zero_add _
  add_zero := by intro M; ext <;> exact add_zero _
  add_comm := by intro M N; ext <;> exact add_comm _ _
  neg_add_cancel := by intro M; ext <;> exact neg_add_cancel _
  sub_eq_add_neg := by intro M N; rfl
  nsmul := λ n M => ⟨n • M.a, n • M.b, n • M.c, n • M.d⟩
  nsmul_zero := by intro M; ext <;> exact AddMonoid.nsmul_zero _
  nsmul_succ := by intro n M; ext <;> exact AddMonoid.nsmul_succ n _
  zsmul := λ z M => ⟨z • M.a, z • M.b, z • M.c, z • M.d⟩
  zsmul_zero' := by intro M; ext <;> exact SubNegMonoid.zsmul_zero' _
  zsmul_succ' := by intro n M; ext <;> exact SubNegMonoid.zsmul_succ' n _
  zsmul_neg' := by intro n M; ext <;> exact SubNegMonoid.zsmul_neg' n _
}

@[simp] theorem sub_a (M N : SuperMatrix R) : (M - N).a = M.a - N.a := by
  change M.a + -N.a = M.a - N.a
  rw [sub_eq_add_neg]

@[simp] theorem sub_b (M N : SuperMatrix R) : (M - N).b = M.b - N.b := by
  change M.b + -N.b = M.b - N.b
  rw [sub_eq_add_neg]

@[simp] theorem sub_c (M N : SuperMatrix R) : (M - N).c = M.c - N.c := by
  change M.c + -N.c = M.c - N.c
  rw [sub_eq_add_neg]

@[simp] theorem sub_d (M N : SuperMatrix R) : (M - N).d = M.d - N.d := by
  change M.d + -N.d = M.d - N.d
  rw [sub_eq_add_neg]
@[simp] theorem smul_nat_a (n : ℕ) (M : SuperMatrix R) : (n • M).a = n • M.a := rfl
@[simp] theorem smul_nat_b (n : ℕ) (M : SuperMatrix R) : (n • M).b = n • M.b := rfl
@[simp] theorem smul_nat_c (n : ℕ) (M : SuperMatrix R) : (n • M).c = n • M.c := rfl
@[simp] theorem smul_nat_d (n : ℕ) (M : SuperMatrix R) : (n • M).d = n • M.d := rfl
@[simp] theorem smul_int_a (z : ℤ) (M : SuperMatrix R) : (z • M).a = z • M.a := rfl

/-- Multiplication: ordinary 2×2 matrix product. -/
def mul (M N : SuperMatrix R) : SuperMatrix R :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d, M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

instance : Mul (SuperMatrix R) := ⟨mul⟩

@[simp] theorem mul_a (M N : SuperMatrix R) : (M * N).a = M.a * N.a + M.b * N.c := rfl
@[simp] theorem mul_b (M N : SuperMatrix R) : (M * N).b = M.a * N.b + M.b * N.d := rfl
@[simp] theorem mul_c (M N : SuperMatrix R) : (M * N).c = M.c * N.a + M.d * N.c := rfl
@[simp] theorem mul_d (M N : SuperMatrix R) : (M * N).d = M.c * N.b + M.d * N.d := rfl

instance : Inhabited (SuperMatrix R) := ⟨0⟩

/-- Supertrace: str(M) = a - d. -/
def supertrace (M : SuperMatrix R) : R := M.a - M.d

/-- Ordinary trace (ungraded). -/
def trace_ungraded (M : SuperMatrix R) : R := M.a + M.d

/-- Berezinian for GL(1|1): Ber[[a,b],[c,d]] = a/d. -/
noncomputable def berezinian {R : Type*} [Field R] (M : SuperMatrix R) : R := M.a / M.d

theorem supertrace_zero : supertrace (0 : SuperMatrix R) = 0 := by
  simp [supertrace]

theorem supertrace_neg (M : SuperMatrix R) : supertrace (-M) = -supertrace M := by
  simp [supertrace, add_comm, sub_eq_add_neg]

theorem supertrace_add (M N : SuperMatrix R) : supertrace (M + N) = supertrace M + supertrace N := by
  unfold supertrace; simp; ring

theorem berezinian_krein_J {R : Type*} [Field R] [CharZero R] : berezinian (⟨1, 0, 0, -1⟩ : SuperMatrix R) = -1 := by
  unfold berezinian; simp

theorem berezinian_one {R : Type*} [Field R] : berezinian (⟨1, 0, 0, 1⟩ : SuperMatrix R) = 1 := by
  unfold berezinian; simp

theorem supertrace_supercommutator_even (M N : SuperMatrix R) (hM : M.b = 0 ∧ M.c = 0) (hN : N.b = 0 ∧ N.c = 0) :
    supertrace (M * N - N * M) = 0 := by
  rcases hM with ⟨hbM, hcM⟩; rcases hN with ⟨hbN, hcN⟩
  unfold supertrace; simp [hbM, hcM, hbN, hcN]; ring

/-- Ordinary determinant of the underlying 2×2 matrix. -/
def det_ungraded (M : SuperMatrix R) : R := M.a * M.d - M.b * M.c

theorem det_ungraded_diag (a d : R) : det_ungraded (⟨a, 0, 0, d⟩ : SuperMatrix R) = a * d := by
  simp [det_ungraded]

theorem berezinian_diag {R : Type*} [Field R] (a d : R) : berezinian (⟨a, 0, 0, d⟩ : SuperMatrix R) = a / d := by
  simp [berezinian]

theorem berezinian_ratio_det_diag {R : Type*} [Field R] (a d : R) :
    berezinian (⟨a, 0, 0, d⟩ : SuperMatrix R) =
      det_ungraded (⟨a, 0, 0, 1⟩ : SuperMatrix R) / det_ungraded (⟨1, 0, 0, d⟩ : SuperMatrix R) := by
  simp [berezinian, det_ungraded]

/-- Diagonal exponential map of a `SuperMatrix ℝ`. -/
noncomputable def exp_diag (M : SuperMatrix ℝ) : SuperMatrix ℝ :=
  ⟨Real.exp M.a, 0, 0, Real.exp M.d⟩

theorem det_exp_diag (M : SuperMatrix ℝ) :
    det_ungraded (exp_diag M) = Real.exp (trace_ungraded M) := by
  unfold exp_diag det_ungraded trace_ungraded
  simp [Real.exp_add]

theorem berezinian_exp_diag (M : SuperMatrix ℝ) :
    berezinian (exp_diag M) = Real.exp (supertrace M) := by
  unfold exp_diag berezinian supertrace
  simp [Real.exp_sub]

theorem det_ungraded_mul_diag (a1 d1 a2 d2 : R) :
    det_ungraded (⟨a1, 0, 0, d1⟩ * ⟨a2, 0, 0, d2⟩ : SuperMatrix R) =
      det_ungraded (⟨a1, 0, 0, d1⟩ : SuperMatrix R) * det_ungraded (⟨a2, 0, 0, d2⟩ : SuperMatrix R) := by
  unfold det_ungraded
  simp; ring

theorem berezinian_mul_diag {R : Type*} [Field R] (a1 d1 a2 d2 : R) :
    berezinian (⟨a1, 0, 0, d1⟩ * ⟨a2, 0, 0, d2⟩ : SuperMatrix R) =
      berezinian (⟨a1, 0, 0, d1⟩ : SuperMatrix R) * berezinian (⟨a2, 0, 0, d2⟩ : SuperMatrix R) := by
  unfold berezinian
  simp [mul_div_mul_comm]

end SuperMatrix

end Audit.SuperTraceBerezinian
