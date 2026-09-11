import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# InfoGeometry.Clifford.HestenesCauchyRiemann

A small real-only owner surface for two related lanes:

- ordinary complex multiplication on `ℝ²`, with the Cauchy-Riemann equations
  expressed as the criterion for real-linearity to be induced by multiplication
  by a single complex scalar;
- a toy Hestenes-style even-spinor shadow where the same Cauchy-Riemann pattern
  is read as right multiplication by a distinguished bivector squaring to `-1`.

This module is intentionally algebraic.  It introduces no analytic axioms and no
scalar `Complex` import.  Analyticity appears only through explicit socket
structures carrying whichever expansion/partial-derivative data a downstream
owner chooses to provide.
-/

namespace InfoGeometry.Clifford.HestenesCauchyRiemann

set_option autoImplicit false

/-- Complex numbers modeled as a two-dimensional real vector space. -/
structure ComplexReal where
  re : ℝ
  im : ℝ

@[ext]
theorem complexReal_ext {z₁ z₂ : ComplexReal} (hre : z₁.re = z₂.re) (him : z₁.im = z₂.im) :
    z₁ = z₂ := by
  cases z₁
  cases z₂
  simp_all

/-- Standard complex multiplication in real coordinates. -/
def c_mul (z₁ z₂ : ComplexReal) : ComplexReal :=
  ⟨z₁.re * z₂.re - z₁.im * z₂.im, z₁.re * z₂.im + z₁.im * z₂.re⟩

/-- A real linear map on the tangent space of `ℂ ≃ ℝ²`. -/
structure RealLinearMap where
  ux : ℝ
  uy : ℝ
  vx : ℝ
  vy : ℝ

/-- The action of the real linear map on a complex-real tangent vector. -/
def applyMap (L : RealLinearMap) (z : ComplexReal) : ComplexReal :=
  ⟨L.ux * z.re + L.uy * z.im, L.vx * z.re + L.vy * z.im⟩

/-- Complex-linearity: the real map is multiplication by a single complex scalar. -/
def is_complex_linear (L : RealLinearMap) : Prop :=
  ∃ A : ComplexReal, ∀ z : ComplexReal, applyMap L z = c_mul A z

/-- The coordinate Cauchy-Riemann equations. -/
def satisfy_cauchy_riemann (L : RealLinearMap) : Prop :=
  L.ux = L.vy ∧ L.uy = -L.vx

theorem complex_linear_iff_cauchy_riemann (L : RealLinearMap) :
    is_complex_linear L ↔ satisfy_cauchy_riemann L := by
  constructor
  · rintro ⟨A, hA⟩
    have h1 : applyMap L ⟨1, 0⟩ = c_mul A ⟨1, 0⟩ := hA ⟨1, 0⟩
    have hI : applyMap L ⟨0, 1⟩ = c_mul A ⟨0, 1⟩ := hA ⟨0, 1⟩
    have h1re : L.ux = A.re := by
      simpa [applyMap, c_mul] using congrArg ComplexReal.re h1
    have h1im : L.vx = A.im := by
      simpa [applyMap, c_mul] using congrArg ComplexReal.im h1
    have hIre : L.uy = -A.im := by
      simpa [applyMap, c_mul] using congrArg ComplexReal.re hI
    have hIim : L.vy = A.re := by
      simpa [applyMap, c_mul] using congrArg ComplexReal.im hI
    constructor
    · linarith
    · linarith
  · rintro ⟨huxvy, huyvx⟩
    refine ⟨⟨L.ux, L.vx⟩, ?_⟩
    intro z
    ext <;> simp [applyMap, c_mul, huxvy, huyvx] <;> ring

/-- A real Hestenes-style even spinor shadow with four real coordinates. -/
@[ext]
structure HestenesSpinor where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

/-- Quaternion-style even-algebra multiplication on the toy spinor model. -/
def hMul (q₁ q₂ : HestenesSpinor) : HestenesSpinor :=
  ⟨q₁.a * q₂.a - q₁.b * q₂.b - q₁.c * q₂.c - q₁.d * q₂.d,
    q₁.a * q₂.b + q₁.b * q₂.a - q₁.c * q₂.d + q₁.d * q₂.c,
    q₁.a * q₂.c + q₁.c * q₂.a - q₁.d * q₂.b + q₁.b * q₂.d,
    q₁.a * q₂.d + q₁.d * q₂.a - q₁.b * q₂.c + q₁.c * q₂.b⟩

instance : Mul HestenesSpinor where
  mul := hMul

instance : Add HestenesSpinor where
  add q₁ q₂ := ⟨q₁.a + q₂.a, q₁.b + q₂.b, q₁.c + q₂.c, q₁.d + q₂.d⟩

instance : Zero HestenesSpinor where
  zero := ⟨0, 0, 0, 0⟩

instance : One HestenesSpinor where
  one := ⟨1, 0, 0, 0⟩

instance : Neg HestenesSpinor where
  neg q := ⟨-q.a, -q.b, -q.c, -q.d⟩

/-- Reversion/conjugation in the toy even-spinor model. -/
def reverse (q : HestenesSpinor) : HestenesSpinor :=
  ⟨q.a, -q.b, -q.c, -q.d⟩

/-- Quadratic norm readback. -/
def h_norm (q : HestenesSpinor) : ℝ :=
  q.a * q.a + q.b * q.b + q.c * q.c + q.d * q.d

/-- Krein-style scalar readback: the scalar part of `q₁ * reverse q₂`. -/
def krein_inner (q₁ q₂ : HestenesSpinor) : ℝ :=
  (q₁ * reverse q₂).a

/-- Distinguished bivector phase plane. -/
def bivector_i : HestenesSpinor :=
  ⟨0, 0, 0, 1⟩

theorem even_algebra_mul_assoc (q₁ q₂ q₃ : HestenesSpinor) :
    (q₁ * q₂) * q₃ = q₁ * (q₂ * q₃) := by
  change hMul (hMul q₁ q₂) q₃ = hMul q₁ (hMul q₂ q₃)
  cases q₁
  cases q₂
  cases q₃
  ext <;> simp [hMul] <;> ring

theorem spinor_mul_reverse (q : HestenesSpinor) :
    q * reverse q = ⟨h_norm q, 0, 0, 0⟩ := by
  change hMul q (reverse q) = ⟨h_norm q, 0, 0, 0⟩
  cases q
  ext <;> simp [hMul, reverse, h_norm] <;> ring

theorem bivector_i_squared : bivector_i * bivector_i = ⟨-1, 0, 0, 0⟩ := by
  change hMul bivector_i bivector_i = ⟨-1, 0, 0, 0⟩
  ext <;> simp [hMul, bivector_i]

theorem krein_inner_symmetry (q₁ q₂ : HestenesSpinor) :
    krein_inner q₁ q₂ = krein_inner q₂ q₁ := by
  change (hMul q₁ (reverse q₂)).a = (hMul q₂ (reverse q₁)).a
  cases q₁
  cases q₂
  simp [hMul, reverse]
  ring

/-- The two real directional derivatives used in the Hestenes CR socket. -/
structure HestenesPartialDerivs where
  dx : HestenesSpinor
  dy : HestenesSpinor

/-- Hestenes-style CR operator `∂x ψ + ∂y ψ · I`. -/
def hestenesCROperator (D : HestenesPartialDerivs) : HestenesSpinor :=
  D.dx + D.dy * bivector_i

/--
Hestenes-style CR law in unpacked real coordinates for the toy even-spinor lane.
This is the component form of the vanishing condition `hestenesCROperator D = 0`.
-/
def satisfy_hestenes_cr (D : HestenesPartialDerivs) : Prop :=
  D.dx.a = D.dy.d ∧ D.dx.d = -D.dy.a ∧ D.dx.b = -D.dy.c ∧ D.dx.c = D.dy.b

/-- Standard coordinate Cauchy-Riemann components. -/
structure StandardCRComponents where
  ux : ℝ
  uy : ℝ
  vx : ℝ
  vy : ℝ

/-- The classical CR equations in coordinate form. -/
def satisfy_standard_cr (C : StandardCRComponents) : Prop :=
  C.ux = C.vy ∧ C.uy = -C.vx

/--
Embed standard CR data into the toy Hestenes spinor model via the real-even lane
`u + v I` with `I = bivector_i`.
-/
def standardCRToHestenes (C : StandardCRComponents) : HestenesPartialDerivs :=
  ⟨⟨C.ux, 0, 0, C.vx⟩, ⟨C.uy, 0, 0, C.vy⟩⟩

theorem hestenes_cr_equivalence (C : StandardCRComponents) :
    satisfy_hestenes_cr (standardCRToHestenes C) ↔ satisfy_standard_cr C := by
  cases C with
  | mk ux uy vx vy =>
      constructor
      · intro h
        rcases h with ⟨h1, hrest⟩
        rcases hrest with ⟨h2, h3, h4⟩
        have h1' : ux = vy := by simpa [standardCRToHestenes] using h1
        have h2' : vx = -uy := by simpa [standardCRToHestenes] using h2
        constructor
        · exact h1'
        · linarith
      · rintro ⟨h1, h2⟩
        have h2' : vx = -uy := by linarith
        constructor
        · simpa [standardCRToHestenes] using h1
        constructor
        · simpa [standardCRToHestenes] using h2'
        constructor
        · norm_num [standardCRToHestenes]
        · norm_num [standardCRToHestenes]

/--
A Weierstrass-style analytic socket for a real-coordinate complex function.
No convergence theorem is asserted here; this is only the owner surface carrying
power-series data and the radius on which a downstream module may reason.
-/
structure WeierstrassAnalyticSocket (f : ComplexReal → ComplexReal) (z₀ : ComplexReal) where
  coeffs : ℕ → ComplexReal
  radius : ℝ
  radius_pos : 0 < radius
  seriesModel : ComplexReal → ComplexReal

namespace WeierstrassAnalyticSocket

/-- The analytic socket center is the index parameter supplied to the owner. -/
def center {f : ComplexReal → ComplexReal} {z₀ : ComplexReal}
    (_ : WeierstrassAnalyticSocket f z₀) : ComplexReal := z₀

/-- The analytic socket source is the function supplied to the owner. -/
def source {f : ComplexReal → ComplexReal} {z₀ : ComplexReal}
    (_ : WeierstrassAnalyticSocket f z₀) : ComplexReal → ComplexReal := f

end WeierstrassAnalyticSocket

/--
A Hestenes-style analytic socket: explicit partial-derivative data together with
an owned CR readback on the selected real phase plane.
-/
structure HestenesAnalyticSocket (ψ : ℝ → ℝ → HestenesSpinor) where
  partials : ℝ → ℝ → HestenesPartialDerivs
  hestenes_cr_law : ∀ x y : ℝ, satisfy_hestenes_cr (partials x y)

namespace HestenesAnalyticSocket

/-- The Hestenes analytic source is the function supplied to the owner. -/
def source {ψ : ℝ → ℝ → HestenesSpinor}
    (_ : HestenesAnalyticSocket ψ) : ℝ → ℝ → HestenesSpinor := ψ

end HestenesAnalyticSocket

end InfoGeometry.Clifford.HestenesCauchyRiemann
