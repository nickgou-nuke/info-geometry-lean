import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.ComplexRealHestenesFinite

Finite algebraic realification lanes for complex multiplication.

This file records only the theorem-safe finite core:

* a `2×2` real model of complex multiplication;
* the Cauchy--Riemann criterion for real linear maps.

It deliberately does **not** claim analytic completion, global holomorphy,
Morera/Cauchy/Weierstrass equivalence, or any topology/convergence result.
-/

noncomputable section

namespace InfoGeometry.Canonical.ComplexRealHestenesFinite

/-- Complex numbers modeled as a 2D real vector space. -/
structure ComplexReal where
  re : ℝ
  im : ℝ

@[ext]
theorem complex_ext {z1 z2 : ComplexReal} (hre : z1.re = z2.re)
    (him : z1.im = z2.im) : z1 = z2 := by
  cases z1
  cases z2
  simp_all

/-- Standard complex multiplication. -/
def c_mul (z1 z2 : ComplexReal) : ComplexReal :=
  ⟨z1.re * z2.re - z1.im * z2.im, z1.re * z2.im + z1.im * z2.re⟩

/-- A real linear map on the tangent space of `ℂ`. -/
structure RealLinearMap where
  ux : ℝ
  uy : ℝ
  vx : ℝ
  vy : ℝ

/-- The action of the real linear map on a complex number (tangent vector). -/
def apply (L : RealLinearMap) (z : ComplexReal) : ComplexReal :=
  ⟨L.ux * z.re + L.uy * z.im, L.vx * z.re + L.vy * z.im⟩

/-- Complex-linearity: the map acts strictly via complex multiplication by some scalar. -/
def is_complex_linear (L : RealLinearMap) : Prop :=
  ∃ A : ComplexReal, ∀ z : ComplexReal, apply L z = c_mul A z

/-- Cauchy--Riemann equations for the real matrix coefficients. -/
def satisfy_cauchy_riemann (L : RealLinearMap) : Prop :=
  L.ux = L.vy ∧ L.uy = -L.vx

/--
The algebraic equivalence of complex linearity and the Cauchy--Riemann equations.
-/
theorem complex_linear_iff_cauchy_riemann (L : RealLinearMap) :
    is_complex_linear L ↔ satisfy_cauchy_riemann L := by
  constructor
  · rintro ⟨A, hA⟩
    have h1 := hA ⟨1, 0⟩
    have h2 := hA ⟨0, 1⟩
    have h1re := congrArg ComplexReal.re h1
    have h1im := congrArg ComplexReal.im h1
    have h2re := congrArg ComplexReal.re h2
    have h2im := congrArg ComplexReal.im h2
    simp [apply, c_mul] at h1re h1im h2re h2im
    unfold satisfy_cauchy_riemann
    constructor <;> linarith
  · rintro ⟨hux, huy⟩
    refine ⟨⟨L.ux, L.vx⟩, ?_⟩
    intro z
    cases z with
    | mk z_re z_im =>
        ext <;> simp [apply, c_mul, hux, huy] <;> ring

/-- The Hestenes spinor represented in the even subalgebra of `Cl(3,0)`. -/
@[ext]
structure HestenesSpinor where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

end InfoGeometry.Canonical.ComplexRealHestenesFinite

