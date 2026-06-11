import Mathlib

abbrev Vec5 : Type := ℂ × ℂ × ℂ × ℂ × ℂ
abbrev Mat4C : Type := Matrix (Fin 4) (Fin 4) ℂ
abbrev ProdMat4C : Type := Mat4C × Mat4C

variable (g1 g2 g3 g4 g5 : Mat4C)

noncomputable def gen : Vec5 →ₗ[ℂ] ProdMat4C where
  toFun v := (
    v.1 • g1 + v.2.1 • g2 + v.2.2.1 • g3 + v.2.2.2.1 • g4 + v.2.2.2.2 • g5,
    v.1 • g1 + v.2.1 • g2 + v.2.2.1 • g3 + v.2.2.2.1 • g4 - v.2.2.2.2 • g5
  )
  map_add' u v := by
    ext
    · simp [add_smul]; abel
    · simp [add_smul]; abel
  map_smul' c v := by
    ext
    · simp [mul_smul]
    · simp [mul_smul, smul_sub]
