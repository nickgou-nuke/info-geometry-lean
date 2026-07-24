import InfoGeometry.Algebra.H3ZornMcCrimmonLinearization

namespace InfoGeometry.Algebra.H3Zorn

private theorem vector_poly_top_coefficients
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ : H3Zorn ℝ)
    (h : ∀ r : ℝ, c₀ + r • c₁ + r ^ 2 • c₂ + r ^ 3 • c₃ +
      r ^ 4 • c₄ + r ^ 5 • c₅ + r ^ 6 • c₆ = 0) :
    c₃ = 0 ∧ c₄ = 0 ∧ c₅ = 0 ∧ c₆ = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  norm_num only [zero_smul, zero_pow, OfNat.ofNat, add_zero] at h0
  norm_num at h1 h2 h3 h4 h5 h6
  have combine (w₀ w₁ w₂ w₃ w₄ w₅ w₆ : ℝ) :
      w₀ • c₀ + w₁ • (c₀ + c₁ + c₂ + c₃ + c₄ + c₅ + c₆) +
        w₂ • (c₀ + 2 • c₁ + 4 • c₂ + 8 • c₃ + 16 • c₄ + 32 • c₅ + 64 • c₆) +
        w₃ • (c₀ + 3 • c₁ + 9 • c₂ + 27 • c₃ + 81 • c₄ + 243 • c₅ + 729 • c₆) +
        w₄ • (c₀ + 4 • c₁ + 16 • c₂ + 64 • c₃ + 256 • c₄ + 1024 • c₅ + 4096 • c₆) +
        w₅ • (c₀ + 5 • c₁ + 25 • c₂ + 125 • c₃ + 625 • c₄ + 3125 • c₅ + 15625 • c₆) +
        w₆ • (c₀ + 6 • c₁ + 36 • c₂ + 216 • c₃ + 1296 • c₄ + 7776 • c₅ + 46656 • c₆) = 0 := by
    have e0 := congrArg (fun W : H3Zorn ℝ => w₀ • W) h0
    have e1 := congrArg (fun W : H3Zorn ℝ => w₁ • W) h1
    have e2 := congrArg (fun W : H3Zorn ℝ => w₂ • W) h2
    have e3 := congrArg (fun W : H3Zorn ℝ => w₃ • W) h3
    have e4 := congrArg (fun W : H3Zorn ℝ => w₄ • W) h4
    have e5 := congrArg (fun W : H3Zorn ℝ => w₅ • W) h5
    have e6 := congrArg (fun W : H3Zorn ℝ => w₆ • W) h6
    have e01 := congrArg₂ (fun A B : H3Zorn ℝ => A + B) e0 e1
    have e012 := congrArg₂ (fun A B : H3Zorn ℝ => A + B) e01 e2
    have e0123 := congrArg₂ (fun A B : H3Zorn ℝ => A + B) e012 e3
    have e01234 := congrArg₂ (fun A B : H3Zorn ℝ => A + B) e0123 e4
    have e012345 := congrArg₂ (fun A B : H3Zorn ℝ => A + B) e01234 e5
    have e := congrArg₂ (fun A B : H3Zorn ℝ => A + B) e012345 e6
    convert e using 1 <;> module
  constructor
  · have e := combine (-49/48) (29/6) (-461/48) (31/3) (-307/48) (13/6) (-5/16)
    convert e using 1 <;> norm_num <;> module
  constructor
  · have e := combine (35/144) (-31/24) (137/48) (-121/36) (107/48) (-19/24) (17/144)
    convert e using 1 <;> norm_num <;> module
  constructor
  · have e := combine (-7/240) (1/6) (-19/48) (1/2) (-17/48) (2/15) (-1/48)
    convert e using 1 <;> norm_num <;> module
  · have e := combine (1/720) (-1/120) (1/48) (-1/36) (1/48) (-1/120) (1/720)
    convert e using 1 <;> norm_num <;> module

private theorem monic_cubic_annihilator
    (n₀ n₁ n₂ : ℝ) (d₀ d₁ d₂ d₃ : H3Zorn ℝ)
    (h : ∀ r : ℝ,
      (n₀ + r * n₁ + r ^ 2 * n₂ + r ^ 3) •
        (d₀ + r • d₁ + r ^ 2 • d₂ + r ^ 3 • d₃) = 0) :
    d₀ = 0 := by
  let c₀ := n₀ • d₀
  let c₁ := n₀ • d₁ + n₁ • d₀
  let c₂ := n₀ • d₂ + n₁ • d₁ + n₂ • d₀
  let c₃ := n₀ • d₃ + n₁ • d₂ + n₂ • d₁ + d₀
  let c₄ := n₁ • d₃ + n₂ • d₂ + d₁
  let c₅ := n₂ • d₃ + d₂
  let c₆ := d₃
  have hp (r : ℝ) :
      c₀ + r • c₁ + r ^ 2 • c₂ + r ^ 3 • c₃ + r ^ 4 • c₄ +
        r ^ 5 • c₅ + r ^ 6 • c₆ = 0 := by
    dsimp [c₀, c₁, c₂, c₃, c₄, c₅, c₆]
    calc
      _ = (n₀ + r * n₁ + r ^ 2 * n₂ + r ^ 3) •
          (d₀ + r • d₁ + r ^ 2 • d₂ + r ^ 3 • d₃) := by
            simp only [add_smul, smul_add, mul_smul]
            module
      _ = 0 := h r
  obtain ⟨hc₃, hc₄, hc₅, hc₆⟩ :=
    vector_poly_top_coefficients c₀ c₁ c₂ c₃ c₄ c₅ c₆ hp
  dsimp [c₆] at hc₆
  dsimp [c₅] at hc₅
  dsimp [c₄] at hc₄
  dsimp [c₃] at hc₃
  rw [hc₆] at hc₅ hc₄ hc₃
  change n₂ • (0 : H3Zorn ℝ) + d₂ = 0 at hc₅
  have hd₂ : d₂ = 0 := by simpa only [smul_zero, zero_add] using hc₅
  rw [hd₂] at hc₄ hc₃
  change n₁ • (0 : H3Zorn ℝ) + n₂ • (0 : H3Zorn ℝ) + d₁ = 0 at hc₄
  have hd₁ : d₁ = 0 := by simpa only [smul_zero, zero_add] using hc₄
  rw [hd₁] at hc₃
  change n₀ • (0 : H3Zorn ℝ) + n₁ • (0 : H3Zorn ℝ) + n₂ • (0 : H3Zorn ℝ) + d₀ = 0 at hc₃
  simpa only [smul_zero, zero_add] using hc₃

end InfoGeometry.Algebra.H3Zorn
