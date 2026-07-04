import re

with open("lean/InfoGeometry/Categorical/MobiusGeometry.lean", "r") as f:
    content = f.read()

content = content.replace(
    "def translation_transform (b : ℂ) : MobiusTransform :=\n  { a := 1, b := b, c := 0, d := 1, det_ne_zero := by sorry }",
    "def translation_transform (b : ℂ) : MobiusTransform :=\n  { a := 1, b := b, c := 0, d := 1, det_ne_zero := by norm_num }"
)

content = content.replace(
    "def dilation_transform (a : ℂ) (ha : a ≠ 0) : MobiusTransform :=\n  { a := a, b := 0, c := 0, d := 1, det_ne_zero := by\n      sorry }",
    "def dilation_transform (a : ℂ) (ha : a ≠ 0) : MobiusTransform :=\n  { a := a, b := 0, c := 0, d := 1, det_ne_zero := by\n      dsimp; ring_nf; exact ha }"
)

content = content.replace(
    "def dilation_transform (a : ℂ) (ha : a ≠ 0) : MobiusTransform :=\n  { a := a, b := 0, c := 0, d := 1, det_ne_zero := by sorry }",
    "def dilation_transform (a : ℂ) (ha : a ≠ 0) : MobiusTransform :=\n  { a := a, b := 0, c := 0, d := 1, det_ne_zero := by\n      dsimp; ring_nf; exact ha }"
)

content = content.replace(
    "def inversion_transform : MobiusTransform :=\n  { a := 0, b := 1, c := 1, d := 0, det_ne_zero := by sorry }",
    "def inversion_transform : MobiusTransform :=\n  { a := 0, b := 1, c := 1, d := 0, det_ne_zero := by norm_num }"
)

content = content.replace(
    "def inv (M : MobiusTransform) : MobiusTransform :=\n  { a := M.d,\n    b := -M.b,\n    c := -M.c,\n    d := M.a,\n    det_ne_zero := by sorry }",
    "def inv (M : MobiusTransform) : MobiusTransform :=\n  { a := M.d,\n    b := -M.b,\n    c := -M.c,\n    d := M.a,\n    det_ne_zero := by\n      have h := M.det_ne_zero\n      dsimp\n      have h_ring : M.d * M.a - -M.b * -M.c = M.a * M.d - M.b * M.c := by ring\n      rw [h_ring]\n      exact h }"
)

content = content.replace(
    "def non_parabolic_matrix (k γ1 γ2 : ℂ) (hk : k ≠ 1) (hγ : γ1 ≠ γ2) : MobiusTransform :=\n  { a := γ1 - k * γ2,\n    b := (k - 1) * γ1 * γ2,\n    c := 1 - k,\n    d := k * γ1 - γ2,\n    det_ne_zero := by sorry }",
    "def non_parabolic_matrix (k γ1 γ2 : ℂ) (hk0 : k ≠ 0) (hk : k ≠ 1) (hγ : γ1 ≠ γ2) : MobiusTransform :=\n  { a := γ1 - k * γ2,\n    b := (k - 1) * γ1 * γ2,\n    c := 1 - k,\n    d := k * γ1 - γ2,\n    det_ne_zero := by\n      dsimp\n      have h_ring : (γ1 - k * γ2) * (k * γ1 - γ2) - (k - 1) * γ1 * γ2 * (1 - k) = k * (γ1 - γ2)^2 := by ring\n      rw [h_ring]\n      have h1 : (γ1 - γ2) ≠ 0 := sub_ne_zero.mpr hγ\n      have h2 : (γ1 - γ2)^2 ≠ 0 := pow_ne_zero 2 h1\n      exact mul_ne_zero hk0 h2 }"
)

content = content.replace(
    "def MobiusTransform.actCP1 (M : MobiusTransform) (p : CP1) : CP1 :=\n  { z1 := M.a * p.z1 + M.b * p.z2,\n    z2 := M.c * p.z1 + M.d * p.z2,\n    not_both_zero := by sorry }",
    "def MobiusTransform.actCP1 (M : MobiusTransform) (p : CP1) : CP1 :=\n  { z1 := M.a * p.z1 + M.b * p.z2,\n    z2 := M.c * p.z1 + M.d * p.z2,\n    not_both_zero := by\n      intro h\n      have hz1 : M.a * p.z1 + M.b * p.z2 = 0 := h.1\n      have hz2 : M.c * p.z1 + M.d * p.z2 = 0 := h.2\n      have hd1 : M.d * (M.a * p.z1 + M.b * p.z2) - M.b * (M.c * p.z1 + M.d * p.z2) = 0 := by rw [hz1, hz2]; ring\n      have hd1_ring : M.d * (M.a * p.z1 + M.b * p.z2) - M.b * (M.c * p.z1 + M.d * p.z2) = (M.a * M.d - M.b * M.c) * p.z1 := by ring\n      rw [hd1_ring] at hd1\n      have hp1 : p.z1 = 0 := by\n        cases mul_eq_zero.mp hd1 with\n        | inl hdet => exact (M.det_ne_zero hdet).elim\n        | inr hz1 => exact hz1\n      have hd2 : M.a * (M.c * p.z1 + M.d * p.z2) - M.c * (M.a * p.z1 + M.b * p.z2) = 0 := by rw [hz1, hz2]; ring\n      have hd2_ring : M.a * (M.c * p.z1 + M.d * p.z2) - M.c * (M.a * p.z1 + M.b * p.z2) = (M.a * M.d - M.b * M.c) * p.z2 := by ring\n      rw [hd2_ring] at hd2\n      have hp2 : p.z2 = 0 := by\n        cases mul_eq_zero.mp hd2 with\n        | inl hdet => exact (M.det_ne_zero hdet).elim\n        | inr hz2 => exact hz2\n      rcases p.not_both_zero with h1 | h2\n      · exact h1 hp1\n      · exact h2 hp2 }"
)

with open("lean/InfoGeometry/Categorical/MobiusGeometry.lean", "w") as f:
    f.write(content)
