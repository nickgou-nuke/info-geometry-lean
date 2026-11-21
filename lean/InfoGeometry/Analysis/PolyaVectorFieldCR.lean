/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# Cauchy-Riemann ⇔ irrotational and solenoidal Pólya vector field

Pure-math core of Theorem 2.1 of "On Möbius Transformations as Pólya Vector
Fields from Lie Theory Viewpoint", stripped of all physical interpretation.

Write `f = u + i v` with `u v : ℝ × ℝ → ℝ`, and associate the planar field
`V_f = (u, -v)`. At a point `p`, write

* `ux = ∂ₓu`, `uy = ∂ᵧu`, `vx = ∂ₓv`, `vy = ∂ᵧv`

where each partial derivative is the `deriv` of the corresponding one-variable
coordinate section through `p`. Then

* `div V_f = ux - vy`
* `curl V_f = ∂ₓ(-v) - ∂ᵧu = -vx - uy`

and the Cauchy-Riemann pair `ux = vy ∧ uy = -vx` is equivalent to
`div V_f = 0 ∧ curl V_f = 0` by pure algebra.

All derivative data are explicit `HasDerivAt` hypotheses; the module uses only
kernel-checked proofs and contains no unproved placeholders. The divergence/curl
owners in
`InfoGeometry.Physics` are noncommutative-algebraic and are deliberately not
reused here: this module needs the ordinary planar calculus operators built
from `deriv` of coordinate sections.
-/

namespace InfoGeometry.Analysis.PolyaVectorFieldCR

/-- The Pólya vector field of `f = u + i v`: `V_f(p) = (u p, -v p)`. -/
def polyaField (u v : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun p => (u p, -v p)

/-- Planar divergence of `F = (F₁, F₂)` at `p`, as the sum of the coordinate
partial derivatives of `F₁` (in `x`) and `F₂` (in `y`). -/
noncomputable def divergence (F : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t : ℝ => (F (t, p.2)).1) p.1 +
    deriv (fun s : ℝ => (F (p.1, s)).2) p.2

/-- Scalar (2-dimensional) curl of `F = (F₁, F₂)` at `p`: `∂ₓF₂ - ∂ᵧF₁`. -/
noncomputable def curl (F : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t : ℝ => (F (t, p.2)).2) p.1 -
    deriv (fun s : ℝ => (F (p.1, s)).1) p.2

/-- The `y`-partial of the negated section is the negative of the `y`-partial.
`deriv.neg` is unconditional, so no hypotheses are needed. -/
lemma deriv_neg_section_y (v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    deriv (fun s : ℝ => -v (p.1, s)) p.2 =
      -deriv (fun s : ℝ => v (p.1, s)) p.2 := by
  change deriv (-(fun s : ℝ => v (p.1, s))) p.2 =
    -deriv (fun s : ℝ => v (p.1, s)) p.2
  exact deriv.neg

/-- The `x`-partial of the negated section is the negative of the `x`-partial. -/
lemma deriv_neg_section_x (v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    deriv (fun t : ℝ => -v (t, p.2)) p.1 =
      -deriv (fun t : ℝ => v (t, p.2)) p.1 := by
  change deriv (-(fun t : ℝ => v (t, p.2))) p.1 =
    -deriv (fun t : ℝ => v (t, p.2)) p.1
  exact deriv.neg

/-- Divergence of the Pólya field is `∂ₓu - ∂ᵧv`. -/
lemma divergence_polyaField (u v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) {ux vy : ℝ}
    (hux : HasDerivAt (fun t : ℝ => u (t, p.2)) ux p.1)
    (hvy : HasDerivAt (fun s : ℝ => v (p.1, s)) vy p.2) :
    divergence (polyaField u v) p = ux - vy := by
  unfold divergence
  have h₁ : deriv (fun t : ℝ => (polyaField u v (t, p.2)).1) p.1 = ux := by
    simpa [polyaField] using hux.deriv
  have h₂ : deriv (fun s : ℝ => (polyaField u v (p.1, s)).2) p.2 = -vy := by
    calc
      deriv (fun s : ℝ => (polyaField u v (p.1, s)).2) p.2 =
          deriv (fun s : ℝ => -v (p.1, s)) p.2 := by rfl
      _ = -deriv (fun s : ℝ => v (p.1, s)) p.2 := deriv_neg_section_y v p
      _ = -vy := by rw [hvy.deriv]
  rw [h₁, h₂]
  ring

/-- Curl of the Pólya field is `-(∂ₓv) - ∂ᵧu`. -/
lemma curl_polyaField (u v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) {vx uy : ℝ}
    (hvx : HasDerivAt (fun t : ℝ => v (t, p.2)) vx p.1)
    (huy : HasDerivAt (fun s : ℝ => u (p.1, s)) uy p.2) :
    curl (polyaField u v) p = -vx - uy := by
  unfold curl
  have h₁ : deriv (fun t : ℝ => (polyaField u v (t, p.2)).2) p.1 = -vx := by
    calc
      deriv (fun t : ℝ => (polyaField u v (t, p.2)).2) p.1 =
          deriv (fun t : ℝ => -v (t, p.2)) p.1 := by rfl
      _ = -deriv (fun t : ℝ => v (t, p.2)) p.1 := deriv_neg_section_x v p
      _ = -vx := by rw [hvx.deriv]
  have h₂ : deriv (fun s : ℝ => (polyaField u v (p.1, s)).1) p.2 = uy := by
    simpa [polyaField] using huy.deriv
  rw [h₁, h₂]

/-- The purely algebraic core: the Cauchy-Riemann equations are exactly the
vanishing of `ux - vy` and `-vx - uy`. -/
theorem cauchyRiemann_iff_zero_div_curl_scalar (ux uy vx vy : ℝ) :
    (ux = vy ∧ uy = -vx) ↔ (ux - vy = 0 ∧ -vx - uy = 0) := by
  constructor
  · rintro ⟨hxy, hyx⟩
    constructor <;> linarith
  · rintro ⟨hdiv, hcurl⟩
    constructor <;> linarith

/-- Forward direction: Cauchy-Riemann implies the Pólya field is both
divergence-free and curl-free. -/
theorem cauchyRiemann_implies_polya_irrotational_solenoidal
    (u v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) {ux uy vx vy : ℝ}
    (hux : HasDerivAt (fun t : ℝ => u (t, p.2)) ux p.1)
    (huy : HasDerivAt (fun s : ℝ => u (p.1, s)) uy p.2)
    (hvx : HasDerivAt (fun t : ℝ => v (t, p.2)) vx p.1)
    (hvy : HasDerivAt (fun s : ℝ => v (p.1, s)) vy p.2)
    (hcr : ux = vy ∧ uy = -vx) :
    divergence (polyaField u v) p = 0 ∧ curl (polyaField u v) p = 0 := by
  rw [divergence_polyaField u v p hux hvy, curl_polyaField u v p hvx huy]
  exact (cauchyRiemann_iff_zero_div_curl_scalar ux uy vx vy).1 hcr

/-- Converse direction, proved explicitly: a divergence-free and curl-free
Pólya field implies the Cauchy-Riemann equations. -/
theorem polya_irrotational_solenoidal_implies_cauchyRiemann
    (u v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) {ux uy vx vy : ℝ}
    (hux : HasDerivAt (fun t : ℝ => u (t, p.2)) ux p.1)
    (huy : HasDerivAt (fun s : ℝ => u (p.1, s)) uy p.2)
    (hvx : HasDerivAt (fun t : ℝ => v (t, p.2)) vx p.1)
    (hvy : HasDerivAt (fun s : ℝ => v (p.1, s)) vy p.2)
    (hpf : divergence (polyaField u v) p = 0 ∧ curl (polyaField u v) p = 0) :
    ux = vy ∧ uy = -vx := by
  rw [divergence_polyaField u v p hux hvy,
      curl_polyaField u v p hvx huy] at hpf
  exact (cauchyRiemann_iff_zero_div_curl_scalar ux uy vx vy).2 hpf

/-- Theorem 2.1 (algebraic core): Cauchy-Riemann is strictly equivalent to the
Pólya field being simultaneously divergence-free and curl-free. -/
theorem cauchyRiemann_iff_polya_irrotational_solenoidal
    (u v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) {ux uy vx vy : ℝ}
    (hux : HasDerivAt (fun t : ℝ => u (t, p.2)) ux p.1)
    (huy : HasDerivAt (fun s : ℝ => u (p.1, s)) uy p.2)
    (hvx : HasDerivAt (fun t : ℝ => v (t, p.2)) vx p.1)
    (hvy : HasDerivAt (fun s : ℝ => v (p.1, s)) vy p.2) :
    (ux = vy ∧ uy = -vx) ↔
      (divergence (polyaField u v) p = 0 ∧ curl (polyaField u v) p = 0) := by
  exact ⟨cauchyRiemann_implies_polya_irrotational_solenoidal
      u v p hux huy hvx hvy,
    polya_irrotational_solenoidal_implies_cauchyRiemann u v p hux huy hvx hvy⟩

/-! ### Connection to complex differentiability (mathlib Complex API)

Let `complexify u v : ℂ → ℂ` be `z ↦ u(z.re,z.im) + i·v(z.re,z.im)`. If this map
is real-differentiable at `z = ⟨p.1,p.2⟩`, then its real derivative along `1`
is `ux + i·vx` and along `I` is `uy + i·vy`. Mathlib's Cauchy-Riemann criterion
`differentiableAt_complex_iff_differentiableAt_real` therefore turns our CR pair
into complex differentiability, and conversely. -/

/-- The complex function `f = u + i v` assembled from real coordinate functions. -/
def complexify (u v : ℝ × ℝ → ℝ) : ℂ → ℂ :=
  fun z => Complex.mk (u (z.re, z.im)) (v (z.re, z.im))

/-- The real derivative of `complexify u v` in the `1` direction is `ux + i·vx`,
provided `complexify u v` is real-differentiable at the point. -/
lemma fderiv_complexify_one (u v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) {ux vx : ℝ}
    (hux : HasDerivAt (fun t : ℝ => u (t, p.2)) ux p.1)
    (hvx : HasDerivAt (fun t : ℝ => v (t, p.2)) vx p.1)
    (hR : DifferentiableAt ℝ (complexify u v) (Complex.mk p.1 p.2)) :
    fderiv ℝ (complexify u v) (Complex.mk p.1 p.2) 1 = Complex.mk ux vx := by
  let z : ℂ := Complex.mk p.1 p.2
  let f : ℂ → ℂ := complexify u v
  have hux0 : HasDerivAt (fun t : ℝ => u (p.1 + t, p.2)) ux 0 :=
    HasDerivAt.comp_const_add p.1 0 (by simpa using hux)
  have hvx0 : HasDerivAt (fun t : ℝ => v (p.1 + t, p.2)) vx 0 :=
    HasDerivAt.comp_const_add p.1 0 (by simpa using hvx)
  have huxC : HasDerivAt (fun t : ℝ => (u (p.1 + t, p.2) : ℂ)) (ux : ℂ) 0 :=
    hux0.ofReal_comp
  have hvxC : HasDerivAt (fun t : ℝ => (v (p.1 + t, p.2) : ℂ)) (vx : ℂ) 0 :=
    hvx0.ofReal_comp
  have hsum : HasDerivAt
      (fun t : ℝ => (u (p.1 + t, p.2) : ℂ) + (v (p.1 + t, p.2) : ℂ) * Complex.I)
      ((ux : ℂ) + (vx : ℂ) * Complex.I) 0 :=
    HasDerivAt.add huxC (HasDerivAt.mul_const hvxC Complex.I)
  have hsec : HasDerivAt (fun t : ℝ => f (z + (t : ℂ))) (Complex.mk ux vx) 0 := by
    convert hsum using 1
    · funext t
      apply Complex.ext <;> simp [f, z, complexify]
    · apply Complex.ext <;> simp
  have hline : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add z
  have hR' : HasFDerivAt f (fderiv ℝ f z) ((fun t : ℝ => z + (t : ℂ)) 0) := by
    simpa using hR.hasFDerivAt
  have hcompF := HasFDerivAt.comp (f := (fun t : ℝ => z + (t : ℂ)))
    0 hR' hline.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => f (z + (t : ℂ)))
      (fderiv ℝ f z 1) 0 := by
    simpa [Function.comp_def] using hcompF.hasDerivAt
  exact hcomp.deriv.symm.trans hsec.deriv

/-- The real derivative of `complexify u v` in the `I` direction is `uy + i·vy`,
provided `complexify u v` is real-differentiable at the point. -/
lemma fderiv_complexify_I (u v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) {uy vy : ℝ}
    (huy : HasDerivAt (fun s : ℝ => u (p.1, s)) uy p.2)
    (hvy : HasDerivAt (fun s : ℝ => v (p.1, s)) vy p.2)
    (hR : DifferentiableAt ℝ (complexify u v) (Complex.mk p.1 p.2)) :
    fderiv ℝ (complexify u v) (Complex.mk p.1 p.2) Complex.I = Complex.mk uy vy := by
  let z : ℂ := Complex.mk p.1 p.2
  let f : ℂ → ℂ := complexify u v
  have huy0 : HasDerivAt (fun t : ℝ => u (p.1, p.2 + t)) uy 0 :=
    HasDerivAt.comp_const_add p.2 0 (by simpa using huy)
  have hvy0 : HasDerivAt (fun t : ℝ => v (p.1, p.2 + t)) vy 0 :=
    HasDerivAt.comp_const_add p.2 0 (by simpa using hvy)
  have huyC : HasDerivAt (fun t : ℝ => (u (p.1, p.2 + t) : ℂ)) (uy : ℂ) 0 :=
    huy0.ofReal_comp
  have hvyC : HasDerivAt (fun t : ℝ => (v (p.1, p.2 + t) : ℂ)) (vy : ℂ) 0 :=
    hvy0.ofReal_comp
  have hsum : HasDerivAt
      (fun t : ℝ => (u (p.1, p.2 + t) : ℂ) + (v (p.1, p.2 + t) : ℂ) * Complex.I)
      ((uy : ℂ) + (vy : ℂ) * Complex.I) 0 :=
    HasDerivAt.add huyC (HasDerivAt.mul_const hvyC Complex.I)
  have hsec : HasDerivAt (fun t : ℝ => f (z + (t : ℂ) * Complex.I))
      (Complex.mk uy vy) 0 := by
    convert hsum using 1
    · funext t
      apply Complex.ext <;> simp [f, z, complexify]
    · apply Complex.ext <;> simp
  have hline : HasDerivAt (fun t : ℝ => z + (t : ℂ) * Complex.I) Complex.I 0 := by
    have hmul : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
      simpa using (HasDerivAt.mul_const (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))) Complex.I)
    simpa using hmul.const_add z
  have hR' : HasFDerivAt f (fderiv ℝ f z)
      ((fun t : ℝ => z + (t : ℂ) * Complex.I) 0) := by
    simpa using hR.hasFDerivAt
  have hcompF := HasFDerivAt.comp (f := (fun t : ℝ => z + (t : ℂ) * Complex.I))
    0 hR' hline.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => f (z + (t : ℂ) * Complex.I))
      (fderiv ℝ f z Complex.I) 0 := by
    simpa [Function.comp_def] using hcompF.hasDerivAt
  exact hcomp.deriv.symm.trans hsec.deriv

/-- Complex differentiability from the Cauchy-Riemann pair. Real
differentiability is an explicit hypothesis (existence of partials alone does
not imply real differentiability). -/
theorem complexDifferentiableAt_of_cauchyRiemann
    (u v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) {ux uy vx vy : ℝ}
    (hux : HasDerivAt (fun t : ℝ => u (t, p.2)) ux p.1)
    (huy : HasDerivAt (fun s : ℝ => u (p.1, s)) uy p.2)
    (hvx : HasDerivAt (fun t : ℝ => v (t, p.2)) vx p.1)
    (hvy : HasDerivAt (fun s : ℝ => v (p.1, s)) vy p.2)
    (hcr : ux = vy ∧ uy = -vx)
    (hR : DifferentiableAt ℝ (complexify u v) (Complex.mk p.1 p.2)) :
    DifferentiableAt ℂ (complexify u v) (Complex.mk p.1 p.2) := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  refine ⟨hR, ?_⟩
  rw [fderiv_complexify_I u v p huy hvy hR,
      fderiv_complexify_one u v p hux hvx hR]
  rw [smul_eq_mul, Complex.I_mul]
  rcases hcr with ⟨hxy, hyx⟩
  apply Complex.ext
  · simp [hyx]
  · simp [hxy]

/-- Converse: complex differentiability of `u + i v` forces the
Cauchy-Riemann pair. -/
theorem cauchyRiemann_of_complexDifferentiableAt
    (u v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) {ux uy vx vy : ℝ}
    (hux : HasDerivAt (fun t : ℝ => u (t, p.2)) ux p.1)
    (huy : HasDerivAt (fun s : ℝ => u (p.1, s)) uy p.2)
    (hvx : HasDerivAt (fun t : ℝ => v (t, p.2)) vx p.1)
    (hvy : HasDerivAt (fun s : ℝ => v (p.1, s)) vy p.2)
    (hC : DifferentiableAt ℂ (complexify u v) (Complex.mk p.1 p.2)) :
    ux = vy ∧ uy = -vx := by
  have hR : DifferentiableAt ℝ (complexify u v) (Complex.mk p.1 p.2) :=
    hC.restrictScalars ℝ
  have hCRf : fderiv ℝ (complexify u v) (Complex.mk p.1 p.2) Complex.I =
      Complex.I • fderiv ℝ (complexify u v) (Complex.mk p.1 p.2) 1 :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hC).2
  rw [fderiv_complexify_I u v p huy hvy hR,
      fderiv_complexify_one u v p hux hvx hR] at hCRf
  rw [smul_eq_mul, Complex.I_mul] at hCRf
  have hyx : uy = -vx := by
    simpa using congrArg Complex.re hCRf
  have hxy' : vy = ux := by
    simpa using congrArg Complex.im hCRf
  exact ⟨hxy'.symm, hyx⟩

end InfoGeometry.Analysis.PolyaVectorFieldCR
