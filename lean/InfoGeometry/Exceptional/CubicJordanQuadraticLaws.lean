import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.Freudenthal

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

theorem degree_four_linear_coefficient
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : V}
    (h : ∀ t : ℝ,
      a₀ + t • a₁ + t ^ 2 • a₂ + t ^ 3 • a₃ + t ^ 4 • a₄ =
        b₀ + t • b₁ + t ^ 2 • b₂ + t ^ 3 • b₃ + t ^ 4 • b₄) :
    a₁ = b₁ := by
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  norm_num at h1 hm1 h2 hm2
  have ha := congrArg (fun w : V => (2 / 3 : ℝ) • w) h1
  have hb := congrArg (fun w : V => (2 / 3 : ℝ) • w) hm1
  have hc := congrArg (fun w : V => (1 / 12 : ℝ) • w) h2
  have hd := congrArg (fun w : V => (1 / 12 : ℝ) • w) hm2
  have hab := congrArg₂ (fun u v : V => u - v) ha hb
  have hdc := congrArg₂ (fun u v : V => u - v) hd hc
  have he := congrArg₂ (fun u v : V => u + v) hab hdc
  convert he using 1 <;> module

/--
The minimal polynomial law package needed for the first McCrimmon
linearization.  It is deliberately weaker than `CubicJordanLaws`: no
basepoint, trace-associativity, or polarized trilinear norm is required.
-/
structure CubicJordanQuadraticLaws
    (D : CubicJordanDatum J) where
  cross : J →ₗ[ℝ] J →ₗ[ℝ] J
  cross_eq_polarization : ∀ x y : J,
    cross x y =
      D.adjointQuad (x + y) - D.adjointQuad x - D.adjointQuad y
  adjoint_smul : ∀ (a : ℝ) (x : J),
    D.adjointQuad (a • x) = a ^ 2 • D.adjointQuad x
  norm_line : ∀ (r : ℝ) (x y : J),
    D.normCubic (x + r • y) =
      D.normCubic x +
        r * D.traceBilin (D.adjointQuad x) y +
        r ^ 2 * D.traceBilin (D.adjointQuad y) x +
        r ^ 3 * D.normCubic y
  adjoint_adjoint : ∀ x : J,
    D.adjointQuad (D.adjointQuad x) = D.normCubic x • x

theorem CubicJordanQuadraticLaws.cross_comm
    {D : CubicJordanDatum J} (L : CubicJordanQuadraticLaws D)
    (x y : J) : L.cross x y = L.cross y x := by
  rw [L.cross_eq_polarization, L.cross_eq_polarization, add_comm]
  abel

theorem CubicJordanQuadraticLaws.adjoint_add
    {D : CubicJordanDatum J} (L : CubicJordanQuadraticLaws D)
    (x y : J) :
    D.adjointQuad (x + y) =
      D.adjointQuad x + L.cross x y + D.adjointQuad y := by
  rw [L.cross_eq_polarization]
  abel

theorem CubicJordanQuadraticLaws.adjoint_line
    {D : CubicJordanDatum J} (L : CubicJordanQuadraticLaws D)
    (r : ℝ) (x y : J) :
    D.adjointQuad (x + r • y) =
      D.adjointQuad x + r • L.cross x y + r ^ 2 • D.adjointQuad y := by
  rw [L.adjoint_add]
  rw [map_smul, L.adjoint_smul]

private theorem CubicJordanQuadraticLaws.master_linearization
    {D : CubicJordanDatum J} (L : CubicJordanQuadraticLaws D)
    (r : ℝ) (x y : J) :
    D.adjointQuad (D.adjointQuad x) +
        r • L.cross (D.adjointQuad x) (L.cross x y) +
        r ^ 2 •
          (D.adjointQuad (L.cross x y) +
            L.cross (D.adjointQuad x) (D.adjointQuad y)) +
        r ^ 3 • L.cross (L.cross x y) (D.adjointQuad y) +
        r ^ 4 • D.adjointQuad (D.adjointQuad y) =
      D.normCubic x • x +
        r • (D.normCubic x • y +
          D.traceBilin (D.adjointQuad x) y • x) +
        r ^ 2 • (D.traceBilin (D.adjointQuad x) y • y +
          D.traceBilin (D.adjointQuad y) x • x) +
        r ^ 3 • (D.traceBilin (D.adjointQuad y) x • y +
          D.normCubic y • x) +
        r ^ 4 • (D.normCubic y • y) := by
  have h := L.adjoint_adjoint (x + r • y)
  rw [L.adjoint_line] at h
  rw [L.adjoint_add, L.adjoint_add, L.adjoint_smul, L.adjoint_smul] at h
  have hcross :
      L.cross (D.adjointQuad x + r • L.cross x y) =
        L.cross (D.adjointQuad x) + r • L.cross (L.cross x y) := by
    ext z
    simp
  rw [hcross] at h
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_smul] at h
  rw [L.norm_line] at h
  convert h using 1 <;>
    simp only [pow_succ, add_smul, smul_add, mul_smul] <;>
    module

theorem CubicJordanQuadraticLaws.adjoint_cross_linearization
    {D : CubicJordanDatum J} (L : CubicJordanQuadraticLaws D)
    (x y : J) :
    L.cross (D.adjointQuad x) (L.cross x y) =
      D.normCubic x • y +
        D.traceBilin (D.adjointQuad x) y • x := by
  have h1 := L.master_linearization (1 : ℝ) x y
  have hm1 := L.master_linearization (-1 : ℝ) x y
  have h2 := L.master_linearization (2 : ℝ) x y
  have hm2 := L.master_linearization (-2 : ℝ) x y
  rw [L.adjoint_adjoint x, L.adjoint_adjoint y] at h1 hm1 h2 hm2
  norm_num at h1 hm1 h2 hm2
  have ha := congrArg (fun w : J => (2 / 3 : ℝ) • w) h1
  have hb := congrArg (fun w : J => (2 / 3 : ℝ) • w) hm1
  have hc := congrArg (fun w : J => (1 / 12 : ℝ) • w) h2
  have hd := congrArg (fun w : J => (1 / 12 : ℝ) • w) hm2
  have hab := congrArg₂ (fun a b : J => a - b) ha hb
  have hdc := congrArg₂ (fun a b : J => a - b) hd hc
  have he := congrArg₂ (fun a b : J => a + b) hab hdc
  convert he using 1 <;> module

end InfoGeometry.Exceptional.Freudenthal
