import Mathlib

open Matrix

def M : Matrix (Fin 2) (Fin 2) ℕ :=
  !![1, 1; 1, 0]

def v_init : Fin 2 → ℕ := ![1, 0]

def af_dim (n : ℕ) : Fin 2 → ℕ :=
  Matrix.mulVec (M ^ n) v_init

lemma penrose_af_dimension (n : ℕ) : 
  af_dim n 0 = Nat.fib (n + 1) ∧ af_dim n 1 = Nat.fib n := by
  induction' n with n ih
  · exact ⟨rfl, rfl⟩
  · rcases ih with ⟨ih0, ih1⟩
    have h_pow : M ^ (n + 1) = M * M ^ n := pow_succ' M n
    have h_mulVec : af_dim (n + 1) = Matrix.mulVec M (af_dim n) := by
      calc af_dim (n + 1)
        = Matrix.mulVec (M ^ (n + 1)) v_init := rfl
      _ = Matrix.mulVec (M * M ^ n) v_init := by rw [h_pow]
      _ = Matrix.mulVec M (Matrix.mulVec (M ^ n) v_init) := by rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec M (af_dim n) := rfl
    constructor
    · calc af_dim (n + 1) 0
        = (Matrix.mulVec M (af_dim n)) 0 := by rw [h_mulVec]
      _ = M 0 0 * af_dim n 0 + M 0 1 * af_dim n 1 := rfl
      _ = 1 * af_dim n 0 + 1 * af_dim n 1 := rfl
      _ = af_dim n 0 + af_dim n 1 := by ring
      _ = Nat.fib (n + 1) + Nat.fib n := by rw [ih0, ih1]
      _ = Nat.fib n + Nat.fib (n + 1) := Nat.add_comm _ _
      _ = Nat.fib (n + 2) := (Nat.fib_add_two).symm
    · calc af_dim (n + 1) 1
        = (Matrix.mulVec M (af_dim n)) 1 := by rw [h_mulVec]
      _ = M 1 0 * af_dim n 0 + M 1 1 * af_dim n 1 := rfl
      _ = 1 * af_dim n 0 + 0 * af_dim n 1 := rfl
      _ = af_dim n 0 := by ring
      _ = Nat.fib (n + 1) := ih0
