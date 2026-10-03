import Mathlib
import InfoGeometry.Physics.BerryKeatingDilationSpectrum

/-!
# The dilation operator and its metaplectic half-shift

`InfoGeometry.Physics.BerryKeatingDilationSpectrum` proves, about a *scalar*
Mellin multiplier `M : ℂ → ℂ`, that

* `M s` is real exactly when `s.re = 1 / 2`,
* `M (1 - conj s) = conj (M s)`,
* formal symmetry `1 - c = conj c` forces `c.re = 1 / 2`.

That file never introduces the operator itself.  This module supplies the
missing operator level: the Weyl-symmetric dilation operator

    H f x = -i * (x * deriv f x + (1/2) * f x)

the power-law eigenfunctions `psi s x = exp (-s * log x)`, the pointwise
intertwining of their dilation and logarithmic derivatives, and the
energy-independence of the eigenfunction modulus on the critical line.

## What is proved here, precisely

* `hasDerivAt_phi` — on the log-coordinate plane waves `exp (−s u)`,
  `d/du (e^(−su)) = −s e^(−su)`.
* `dilationGen_psi_eq_deriv_phi` — at `x = exp u`, both pointwise generators
  have the same action on the corresponding Mellin mode.
* `Hd_psi` — the eigenfunction equation `H ψ_s = i (s − 1/2) ψ_s`, obtained from
  the chain rule and the derivative of `exp`.
* `Hd_psi_shift_split` — `H ψ_s = (−i x d/dx) ψ_s − (i/2) ψ_s`, isolating the
  metaplectic correction: the `1/2` in `½(xp + px)` contributes exactly `−i/2`.
* `psi_mul_conj` — `|ψ_s(x)|² = exp (−2 Re(s) log x)`.
* `critical_line_mul_conj` — on `Re s = 1/2` this is `exp(−log x) = 1/x`: the
  eigenfunction carries exactly the half-density weight and nothing else.
* `critical_line_modulus_independent_of_E` — hence on the critical line the
  modulus does not depend on the energy.  The `1/2` is what removes `E` from
  the modulus.
* `eigenvalue_im_eq_zero_iff` — the eigenvalue is real exactly on the critical
  line, derived here and matching the existing scalar theorem.

Note on scope.  A statement of the form `‖ψ‖ = 1` would be *false*: the modulus
is `x^(−Re s)`, which equals `1` only at `x = 1`.  Constant-modulus behaviour is
a statement about the scale-invariant measure `dx/x`, i.e. about a weighted `L²`
space, and no such space is formalized here.  What is proved is the
energy-independence of the modulus, which is the part that does not depend on
the choice of measure.
-/

namespace InfoGeometry.Physics.DilationMetaplectic

/-- The power-law eigenfunction `ψ_s = x^(−s)` on the positive half-line. -/
noncomputable def psi (s : ℂ) (x : ℝ) : ℂ := Complex.exp (-s * Complex.ofReal (Real.log x))

/-- The same function in log coordinates: `ψ_s(u) = exp(−s u)`. -/
noncomputable def phi (s : ℂ) (u : ℝ) : ℂ := Complex.exp (-s * u)

/-- The half-density change of coordinates from the positive half-line to log
coordinates. The factor `exp (u / 2)` is the square root of the Jacobian
`dx/du = exp u`. This is the unitary-coordinate candidate at the level of
functions; no `L²` space or operator-domain assertion is made here. -/
noncomputable def halfDensityLog (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.exp (u / 2) : ℂ) * f (Real.exp u)

/-- The dilation operator `H = −i (x d/dx + 1/2)`, the Weyl symmetrization of
`x d/dx`.  The `1/2` is the half-density (metaplectic) shift. -/
noncomputable def Hd (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -Complex.I * (x * deriv f x + (1 / 2) * f x)

/-- The shift-free dilation generator `x d/dx` on complex-valued functions. -/
noncomputable def dilationGen (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) * deriv f x

/-- The eigenvalue of `ψ_s`: `i (s − 1/2)`. -/
noncomputable def eigenvalue (s : ℂ) : ℂ := Complex.I * (s - 1 / 2)

/-! ### Dilation becomes translation in log coordinates -/

/-- **Scaling is momentum.**  On the log-coordinate plane waves `exp (−s u)` the
dilation generator is the translation generator, acting by the constant `−s`. -/
theorem hasDerivAt_phi (s : ℂ) (u : ℝ) :
    HasDerivAt (phi s) (-s * phi s u) u := by
  have hid : HasDerivAt (fun v : ℝ => (v : ℂ)) (1 : ℂ) u := by
    simpa using (hasDerivAt_id u).ofReal_comp
  have hc : HasDerivAt (fun v : ℝ => -s * (v : ℂ)) (-s) u := by
    simpa only [mul_one] using hid.const_mul (-s)
  have he := (Complex.hasDerivAt_exp (x := -s * (u : ℂ))).comp u hc
  change HasDerivAt (fun v : ℝ => Complex.exp (-s * (v : ℂ))) _ _
  simpa [phi, Function.comp_def, mul_comm] using he

theorem deriv_phi (s : ℂ) (u : ℝ) : deriv (phi s) u = -s * phi s u :=
  (hasDerivAt_phi s u).deriv

/-- Differentiating the half-density log-coordinate transform gives the
Jacobian-weighted sum of the original dilation derivative and its half-density
correction. -/
theorem deriv_halfDensityLog (f : ℝ → ℂ) (u : ℝ) (f' : ℂ)
    (hf : HasDerivAt f f' (Real.exp u)) :
    deriv (halfDensityLog f) u =
      (Real.exp (u / 2) : ℂ) *
        (f' * (Real.exp u : ℂ) + (1 / 2 : ℂ) * f (Real.exp u)) := by
  have hweightR : HasDerivAt (fun v : ℝ => Real.exp (v / 2))
      (Real.exp (u / 2) / 2) u := by
    convert (Real.hasDerivAt_exp (u / 2)).comp u
      ((hasDerivAt_id u).div_const 2) using 1
    ring
  have hweight : HasDerivAt (fun v : ℝ => (Real.exp (v / 2) : ℂ))
      ((Real.exp (u / 2) / 2 : ℝ) : ℂ) u := hweightR.ofReal_comp
  have harg : HasDerivAt (fun v : ℝ => Real.exp v) (Real.exp u) u :=
    Real.hasDerivAt_exp u
  have hcompose : HasDerivAt (fun v : ℝ => f (Real.exp v))
      (Real.exp u • f') u := hf.scomp u harg
  have hproduct := hweight.mul hcompose
  have hderiv := hproduct.deriv
  unfold halfDensityLog
  change deriv ((fun v : ℝ => (Real.exp (v / 2) : ℂ)) *
      (fun v => f (Real.exp v))) u = _
  rw [hderiv]
  rw [Complex.real_smul]
  push_cast
  ring

/-- The half-density log-coordinate transform intertwines the Weyl-symmetric
dilation generator `−i(x∂ₓ + 1/2)` with the translation generator `−i∂ᵤ`.
This is the corrected differential identity: plain composition with `exp` alone
does retain a `−i/2` term, while the Jacobian half-density cancels it. -/
theorem halfDensityLog_intertwines_H (f : ℝ → ℂ) (u : ℝ) (f' : ℂ)
    (hf : HasDerivAt f f' (Real.exp u)) :
    -Complex.I * deriv (halfDensityLog f) u =
      (Real.exp (u / 2) : ℂ) * Hd f (Real.exp u) := by
  rw [deriv_halfDensityLog f u f' hf]
  simp only [Hd, hf.deriv]
  push_cast
  ring

/-- Exponentiating the logarithmic coordinate recovers the positive-half-line
power mode. -/
theorem psi_exp_log (s : ℂ) (u : ℝ) : psi s (Real.exp u) = phi s u := by
  simp [psi, phi]

/-- The pointwise dilation generator acts on `ψ_s(x) = x^{-s}` by `−s`. -/
theorem dilationGen_psi (s : ℂ) :
    ∀ x, 0 < x → dilationGen (psi s) x = -s * psi s x := by
  intro x hx
  have hlog : HasDerivAt (Real.log : ℝ → ℝ) x⁻¹ x :=
    Real.hasDerivAt_log (ne_of_gt hx)
  have hlogC : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x : ℂ)⁻¹) x := by
    convert hlog.ofReal_comp using 1; simp
  have hc := hlogC.const_mul (-s)
  have he := (Complex.hasDerivAt_exp (x := -s * (Real.log x : ℂ))).comp x hc
  have hpsi : HasDerivAt (psi s) ((-s * x⁻¹) * psi s x) x := by
    change HasDerivAt (fun y : ℝ => Complex.exp (-s * (Real.log y : ℂ))) _ _
    simpa [psi, Function.comp_def, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using he
  rw [dilationGen, hpsi.deriv, Complex.ofReal_inv]
  field_simp [ne_of_gt hx]

/-- In logarithmic coordinates `x = exp u`, the dilation derivative on the
Mellin mode agrees pointwise with the derivative of its log-coordinate form. -/
theorem dilationGen_psi_eq_deriv_phi (s : ℂ) (u : ℝ) :
    dilationGen (psi s) (Real.exp u) = deriv (phi s) u := by
  rw [dilationGen_psi s (Real.exp u) (Real.exp_pos u), deriv_phi, psi_exp_log]

/-! ### The eigenvalue equation -/

/-- **The eigenvalue equation for the dilation operator.**  For every `s` and every
`x > 0`, `H ψ_s = i (s − 1/2) ψ_s`. -/
theorem Hd_psi (s : ℂ) :
    ∀ x, 0 < x → Hd (psi s) x = eigenvalue s * psi s x := by
  intro x hx
  rw [show Hd (psi s) x = -Complex.I *
      (dilationGen (psi s) x + (1 / 2) * psi s x) by rfl,
    dilationGen_psi s x hx]
  simp only [eigenvalue]
  ring

/-- **The metaplectic correction, isolated.**  `H` is the shift-free dilation
`−i x d/dx` minus the half-density term `i/2`: the `1/2` in `½(xp + px)`
contributes exactly `−i/2`. -/
theorem Hd_psi_shift_split (s : ℂ) :
    ∀ x, 0 < x →
      Hd (psi s) x
        = (-Complex.I * (x * deriv (psi s) x)) - (Complex.I / 2) * psi s x := by
  intro x _
  simp only [Hd]
  ring

/-! ### The critical line as a modulus statement -/

/-- The real part of the exponent appearing in `psi`: `Re(−s log x) = −Re(s) log x`. -/
theorem psi_exponent_re (s : ℂ) (x : ℝ) :
    (-s * Complex.ofReal (Real.log x)).re = -(s.re * Real.log x) := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re]
  ring

/-- **The squared modulus of the eigenfunction:**
`|ψ_s(x)|² = exp (−2 Re(s) log x)`. -/
theorem psi_mul_conj (s : ℂ) (x : ℝ) :
    psi s x * star (psi s x) = Real.exp (-2 * s.re * Real.log x) := by
  have hws : (-s * Complex.ofReal (Real.log x)) + star (-s * Complex.ofReal (Real.log x))
      = 2 * (-(s.re * Real.log x)) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.conj_re]
      ring_nf
    · simp [Complex.add_im, Complex.conj_im]
  have hstar (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
    simpa only [← Complex.star_def] using (Complex.exp_conj z).symm
  rw [psi, hstar, ← Complex.exp_add, hws]
  push_cast
  congr 1
  ring

/-- The real part of a point on the critical line is exactly `1/2`, for every
energy `t`. -/
theorem critical_re (t : ℝ) : ((1 / 2 : ℂ) + Complex.I * (t : ℂ)).re = 1 / 2 := by
  simp

/-- **On the critical line the eigenfunction carries exactly the half-density
weight** `x⁻¹`, with no residual dependence on the energy. -/
theorem critical_line_mul_conj (t : ℝ) {x : ℝ} (hx : 0 < x) :
    psi (1 / 2 + Complex.I * (t : ℂ)) x * star (psi (1 / 2 + Complex.I * (t : ℂ)) x)
      = Complex.ofReal x⁻¹ := by
  rw [psi_mul_conj, critical_re]
  rw [show -2 * (1 / 2) * Real.log x = -Real.log x by ring,
    Real.exp_neg, Real.exp_log hx]

/-- **The substantive claim of the critical line, in a form independent of the
choice of measure:** on `Re s = 1/2` the modulus of the eigenfunction does not
depend on the energy.  The half-shift is what removes `E` from `|ψ|`. -/
theorem critical_line_modulus_independent_of_E (t t' x : ℝ) :
    psi (1 / 2 + Complex.I * (t : ℂ)) x * star (psi (1 / 2 + Complex.I * (t : ℂ)) x)
      = psi (1 / 2 + Complex.I * (t' : ℂ)) x
          * star (psi (1 / 2 + Complex.I * (t' : ℂ)) x) := by
  rw [psi_mul_conj, psi_mul_conj, critical_re, critical_re]

/-- **The operator eigenvalue is literally the scalar Mellin multiplier.**

`eigenvalue` and `BerryKeatingDilation.mellinMultiplier` are the same function, so
the operator-level and scalar-level critical-line statements are one statement. This
is recorded as an equation rather than left implicit. -/
@[simp] theorem eigenvalue_eq_mellinMultiplier (s : ℂ) :
    eigenvalue s = InfoGeometry.Physics.BerryKeatingDilation.mellinMultiplier s := rfl

/-- **The eigenvalue is real exactly on the critical line.**

Derived directly from the eigenvalue equation by `Complex.mul_im`. An earlier draft
proved this by `simpa` against
`BerryKeatingDilation.mellinMultiplier_is_real_iff`; that is a wrapper, not a
theorem, since the two sides are definitionally equal by
`eigenvalue_eq_mellinMultiplier`. The direct derivation is kept instead. -/
theorem eigenvalue_im_eq_zero_iff (s : ℂ) :
    (eigenvalue s).im = 0 ↔ s.re = 1 / 2 := by
  simp only [eigenvalue, Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.sub_re]
  norm_num
  constructor <;> intro h <;> linarith

end InfoGeometry.Physics.DilationMetaplectic
