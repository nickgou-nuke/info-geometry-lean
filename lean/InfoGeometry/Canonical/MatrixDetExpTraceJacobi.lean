import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Jacobi-route support for `det (exp A) = exp (trace A)`

Mathlib currently lists the unrestricted matrix identity

`Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`

as a TODO.  This module supplies a canonical proof of that theorem from
mathlib-rooted components:

* the derivative of `t ↦ exp (t • A)`, on both sides;
* invertibility of the flow and the inverse `exp ((-t) • A)`;
* trace invariance under conjugation by the flow;
* the scalar constant-coefficient ODE uniqueness step.
* the determinant derivative at the identity, via mathlib's characteristic
  polynomial coefficient calculation.

The proof derives the determinant ODE at arbitrary time from the determinant
derivative at the identity and the exponential flow law, so it does not assume a
general Jacobi formula for arbitrary matrix paths.
-/

noncomputable section

namespace MatrixDetExpTraceJacobi

open scoped Matrix Matrix.Norms.Operator Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Constant matrix exponential flow `X(t) = exp (t A)`. -/
def matrixExpFlow (A : Matrix n n ℂ) (t : ℂ) : Matrix n n ℂ :=
  NormedSpace.exp (t • A)

/-- Right-hand derivative form for the constant matrix exponential flow. -/
theorem hasDerivAt_matrixExpFlow_right (A : Matrix n n ℂ) (t : ℂ) :
    HasDerivAt (matrixExpFlow A) (matrixExpFlow A t * A) t := by
  simpa [matrixExpFlow] using
    (hasDerivAt_exp_smul_const (x := A) (t := t))

/-- Left-hand derivative form for the constant matrix exponential flow. -/
theorem hasDerivAt_matrixExpFlow_left (A : Matrix n n ℂ) (t : ℂ) :
    HasDerivAt (matrixExpFlow A) (A * matrixExpFlow A t) t := by
  simpa [matrixExpFlow] using
    (hasDerivAt_exp_smul_const' (x := A) (t := t))

/-- Entrywise left-hand derivative form for the constant matrix exponential flow. -/
theorem hasDerivAt_matrixEntry_matrixExpFlow_left
    (A : Matrix n n ℂ) (t : ℂ) (i j : n) :
    HasDerivAt
      (fun z : ℂ => matrixExpFlow A z i j)
      ((A * matrixExpFlow A t) i j) t := by
  have h := (hasDerivAt_matrixExpFlow_left A t).hasFDerivAt
  have hi := (hasFDerivAt_apply (𝕜 := ℂ) i (matrixExpFlow A t)).comp t h
  have hij := (hasFDerivAt_apply (𝕜 := ℂ) j (matrixExpFlow A t i)).comp t hi
  convert hij.hasDerivAt using 1
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    have hspan := ContinuousLinearMap.toSpanSingleton_apply_one ℂ (A * matrixExpFlow A t)
    exact (congr_fun (congr_fun hspan i) j).symm

/-- The constant matrix exponential flow is invertible at every parameter. -/
theorem isUnit_matrixExpFlow (A : Matrix n n ℂ) (t : ℂ) :
    IsUnit (matrixExpFlow A t) := by
  simpa [matrixExpFlow] using Matrix.isUnit_exp (t • A)

/-- The inverse of the constant matrix exponential flow is the negative-time flow. -/
theorem matrixExpFlow_neg_eq_inv (A : Matrix n n ℂ) (t : ℂ) :
    matrixExpFlow A (-t) = (matrixExpFlow A t)⁻¹ := by
  simpa [matrixExpFlow] using Matrix.exp_neg (t • A)

/-- Right inverse identity for the constant matrix exponential flow. -/
theorem matrixExpFlow_mul_neg (A : Matrix n n ℂ) (t : ℂ) :
    matrixExpFlow A t * matrixExpFlow A (-t) = 1 := by
  have hcomm : Commute (t • A) ((-t) • A) := by
    rw [show (-t) • A = -(t • A) by simp]
    exact (Commute.refl (t • A)).neg_right
  have hExp :
      NormedSpace.exp (t • A + (-t) • A) =
        NormedSpace.exp (t • A) * NormedSpace.exp ((-t) • A) :=
    Matrix.exp_add_of_commute (t • A) ((-t) • A) hcomm
  have hzero : (t • A + (-t) • A : Matrix n n ℂ) = 0 := by
    rw [← add_smul]
    simp
  calc
    matrixExpFlow A t * matrixExpFlow A (-t)
        = NormedSpace.exp (t • A) * NormedSpace.exp ((-t) • A) := rfl
    _ = NormedSpace.exp (t • A + (-t) • A) := hExp.symm
    _ = 1 := by rw [hzero]; simp

/-- Left inverse identity for the constant matrix exponential flow. -/
theorem matrixExpFlow_neg_mul (A : Matrix n n ℂ) (t : ℂ) :
    matrixExpFlow A (-t) * matrixExpFlow A t = 1 := by
  have hcomm : Commute ((-t) • A) (t • A) := by
    rw [show (-t) • A = -(t • A) by simp]
    exact (Commute.refl (t • A)).neg_left
  have hExp :
      NormedSpace.exp ((-t) • A + t • A) =
        NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A) :=
    Matrix.exp_add_of_commute ((-t) • A) (t • A) hcomm
  have hzero : ((-t) • A + t • A : Matrix n n ℂ) = 0 := by
    rw [← add_smul]
    simp
  calc
    matrixExpFlow A (-t) * matrixExpFlow A t
        = NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A) := rfl
    _ = NormedSpace.exp ((-t) • A + t • A) := hExp.symm
    _ = 1 := by rw [hzero]; simp

/-- Trace is invariant under conjugation by the matrix exponential flow. -/
theorem trace_matrixExpFlow_inv_mul_mul
    (A B : Matrix n n ℂ) (t : ℂ) :
    Matrix.trace ((matrixExpFlow A t)⁻¹ * B * matrixExpFlow A t) =
      Matrix.trace B := by
  simpa using Matrix.trace_conj' (M := matrixExpFlow A t) (isUnit_matrixExpFlow A t) B

/-- The Liouville trace factor for the constant matrix exponential flow. -/
theorem trace_matrixExpFlow_inv_mul_A_mul_flow (A : Matrix n n ℂ) (t : ℂ) :
    Matrix.trace ((matrixExpFlow A t)⁻¹ * A * matrixExpFlow A t) =
      Matrix.trace A :=
  trace_matrixExpFlow_inv_mul_mul A A t

/--
Scalar constant-coefficient ODE uniqueness in the form needed by the Liouville
proof: if `f' = c f` and `f 0 = 1`, then `f t = exp (t c)`.

This is proved by differentiating `f t * exp (-(t c))` and using the mathlib
mean-value theorem consequence that a differentiable function with zero
derivative is constant.
-/
theorem eq_normed_exp_mul_of_hasDerivAt_eq_const_mul
    {c : ℂ} {f : ℂ → ℂ}
    (hf : ∀ t : ℂ, HasDerivAt f (c * f t) t)
    (h0 : f 0 = 1) :
    ∀ t : ℂ, f t = NormedSpace.exp (t * c) := by
  let g : ℂ → ℂ := fun t => f t * Complex.exp (-(t * c))
  have hg : ∀ t : ℂ, HasDerivAt g 0 t := by
    intro t
    have hlin : HasDerivAt (fun u : ℂ => -(u * c)) (-c) t := by
      simpa using ((hasDerivAt_id' t).mul_const c).neg
    have hexp :
        HasDerivAt
          (fun u : ℂ => Complex.exp (-(u * c)))
          (Complex.exp (-(t * c)) * (-c)) t :=
      hlin.cexp
    have hmul := (hf t).mul hexp
    have hzero_deriv :
        c * f t * Complex.exp (-(t * c)) +
            -(f t * (Complex.exp (-(t * c)) * c)) = 0 := by
      ring
    simpa [g, hzero_deriv] using hmul
  have hgdiff : Differentiable ℂ g := fun t => (hg t).differentiableAt
  have hgderiv : ∀ t : ℂ, deriv g t = 0 := fun t => (hg t).deriv
  intro t
  have hg_const : g t = 1 := by
    have h := is_const_of_deriv_eq_zero hgdiff hgderiv t 0
    simpa [g, h0] using h
  have hexp_cancel : Complex.exp (-(t * c)) * Complex.exp (t * c) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hcomplex : f t = Complex.exp (t * c) := by
    calc
      f t = f t * (Complex.exp (-(t * c)) * Complex.exp (t * c)) := by
        rw [hexp_cancel, mul_one]
      _ = (f t * Complex.exp (-(t * c))) * Complex.exp (t * c) := by ring
      _ = 1 * Complex.exp (t * c) := by
        change g t * Complex.exp (t * c) = 1 * Complex.exp (t * c)
        rw [hg_const]
      _ = Complex.exp (t * c) := by rw [one_mul]
  simpa [Complex.exp_eq_exp_ℂ] using hcomplex

/--
Derivative of the Leibniz determinant expansion along a differentiable matrix
path.

This is the raw determinant-calculus kernel behind Jacobi's formula.  It keeps
the derivative in the explicit permutation/product form supplied by
`Matrix.det_apply'`; the later Jacobi step is the algebraic compression of this
sum into `det X * trace (X⁻¹ * X')` at invertible `X`.
-/
theorem hasDerivAt_det_leibniz
    {X : ℂ → Matrix n n ℂ} {X' : Matrix n n ℂ} {t : ℂ}
    (hX : ∀ i j : n, HasDerivAt (fun z : ℂ => X z i j) (X' i j) t) :
    HasDerivAt
      (fun z : ℂ => Matrix.det (X z))
      (∑ σ : Equiv.Perm n,
        (Equiv.Perm.sign σ : ℂ) *
          ∑ i : n, (∏ j ∈ Finset.univ.erase i, X t (σ j) j) * X' (σ i) i) t := by
  have hsum :
      HasDerivAt
        (fun z : ℂ =>
          ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℂ) * ∏ i : n, X z (σ i) i)
        (∑ σ : Equiv.Perm n,
          (Equiv.Perm.sign σ : ℂ) *
            ∑ i : n, (∏ j ∈ Finset.univ.erase i, X t (σ j) j) * X' (σ i) i) t := by
    apply HasDerivAt.fun_sum
    intro σ _hσ
    have hprod :
        HasDerivAt
          (fun z : ℂ => ∏ i : n, X z (σ i) i)
          (∑ i : n, (∏ j ∈ Finset.univ.erase i, X t (σ j) j) * X' (σ i) i) t := by
      simpa [smul_eq_mul] using
        (HasDerivAt.fun_finset_prod (u := Finset.univ)
          (f := fun i z => X z (σ i) i)
          (f' := fun i => X' (σ i) i)
          (x := t)
          (fun i _hi => hX (σ i) i))
    simpa [Finset.mul_sum] using hprod.const_mul (Equiv.Perm.sign σ : ℂ)
  simpa [Matrix.det_apply'] using hsum

/--
Derivative of `det (exp (t A))` in the raw Leibniz form obtained by combining
`hasDerivAt_det_leibniz` with the matrix exponential flow derivative.

The final Jacobi/Liouville compression still remains to be proved separately.
-/
theorem hasDerivAt_det_matrixExpFlow_leibniz
    (A : Matrix n n ℂ) (t : ℂ) :
    HasDerivAt
      (fun z : ℂ => Matrix.det (matrixExpFlow A z))
      (∑ σ : Equiv.Perm n,
        (Equiv.Perm.sign σ : ℂ) *
          ∑ i : n,
            (∏ j ∈ Finset.univ.erase i, matrixExpFlow A t (σ j) j) *
              (A * matrixExpFlow A t) (σ i) i) t :=
  hasDerivAt_det_leibniz
    (X := matrixExpFlow A)
    (X' := A * matrixExpFlow A t)
    (t := t)
    (fun i j => hasDerivAt_matrixEntry_matrixExpFlow_left A t i j)

/--
Derivative at zero of the identity-line determinant
`z ↦ det (1 + z • M)`.

This imports the canonical mathlib characteristic-polynomial coefficient lemma
`Matrix.derivative_det_one_add_X_smul`; no Jacobi formula is assumed.
-/
theorem hasDerivAt_det_one_add_smul_zero (M : Matrix n n ℂ) :
    HasDerivAt (fun z : ℂ => Matrix.det (1 + z • M)) (Matrix.trace M) 0 := by
  let p : ℂ[X] := Matrix.det (1 + (Polynomial.X : ℂ[X]) • M.map Polynomial.C)
  have hpder : p.derivative.eval 0 = Matrix.trace M := by
    simpa [p] using Matrix.derivative_det_one_add_X_smul (R := ℂ) M
  have hp := Polynomial.hasDerivAt (p := p) (x := 0)
  rw [hpder] at hp
  convert hp using 1
  ext z
  simp [p, eval_det, ← Matrix.smul_eq_mul_diagonal]

/--
The raw Leibniz derivative of the determinant at the identity compresses to the
trace.  This is the identity-point Jacobi derivative, derived by comparing the
Leibniz derivative with mathlib's polynomial determinant expansion.
-/
theorem detLeibnizAtOne_eq_trace (M : Matrix n n ℂ) :
    (∑ σ : Equiv.Perm n,
      (Equiv.Perm.sign σ : ℂ) *
        ∑ i : n, (∏ j ∈ Finset.univ.erase i, (1 : Matrix n n ℂ) (σ j) j) *
          M (σ i) i) =
      Matrix.trace M := by
  have hleib :
      HasDerivAt
        (fun z : ℂ => Matrix.det (1 + z • M))
        (∑ σ : Equiv.Perm n,
          (Equiv.Perm.sign σ : ℂ) *
            ∑ i : n, (∏ j ∈ Finset.univ.erase i, (1 : Matrix n n ℂ) (σ j) j) *
              M (σ i) i) 0 := by
    simpa using
      (hasDerivAt_det_leibniz
        (X := fun z : ℂ => (1 : Matrix n n ℂ) + z • M)
        (X' := M)
        (t := 0)
        (fun i j => by
          simpa [Pi.smul_apply, smul_eq_mul] using
            (((hasDerivAt_id' (0 : ℂ)).mul_const (M i j)).const_add
              ((1 : Matrix n n ℂ) i j))))
  exact hleib.unique (hasDerivAt_det_one_add_smul_zero M)

/--
The determinant of the constant matrix exponential flow has infinitesimal
generator `trace A` at the identity time `0`.
-/
theorem hasDerivAt_det_matrixExpFlow_zero (A : Matrix n n ℂ) :
    HasDerivAt (fun z : ℂ => Matrix.det (matrixExpFlow A z)) (Matrix.trace A) 0 := by
  have h := hasDerivAt_det_matrixExpFlow_leibniz A 0
  simpa [matrixExpFlow, Matrix.mul_one, detLeibnizAtOne_eq_trace] using h

/-- Flow-shift identity `X(z) = X(t) X(z - t)` for `X(t) = exp(tA)`. -/
theorem matrixExpFlow_eq_mul_shift (A : Matrix n n ℂ) (t z : ℂ) :
    matrixExpFlow A z = matrixExpFlow A t * matrixExpFlow A (z - t) := by
  have hcomm : Commute (t • A) ((z - t) • A) := by
    exact ((Commute.refl A).smul_left t).smul_right (z - t)
  have hExp := Matrix.exp_add_of_commute (t • A) ((z - t) • A) hcomm
  have hscalar : t • A + (z - t) • A = z • A := by
    rw [← add_smul]
    ring_nf
  calc
    matrixExpFlow A z = NormedSpace.exp (z • A) := rfl
    _ = NormedSpace.exp (t • A + (z - t) • A) := by rw [hscalar]
    _ = matrixExpFlow A t * matrixExpFlow A (z - t) := by
      simpa [matrixExpFlow] using hExp

/-- Determinant form of the flow-shift identity. -/
theorem det_matrixExpFlow_eq_det_mul_shift (A : Matrix n n ℂ) (t z : ℂ) :
    Matrix.det (matrixExpFlow A z) =
      Matrix.det (matrixExpFlow A t) * Matrix.det (matrixExpFlow A (z - t)) := by
  rw [matrixExpFlow_eq_mul_shift A t z, Matrix.det_mul]

/--
Liouville ODE for the determinant of the constant matrix exponential flow.

This derives the derivative at an arbitrary `t` from the canonical determinant
derivative at the identity and the exponential flow law, instead of assuming a
general Jacobi formula for arbitrary matrix paths.
-/
theorem hasDerivAt_det_matrixExpFlow (A : Matrix n n ℂ) (t : ℂ) :
    HasDerivAt
      (fun z : ℂ => Matrix.det (matrixExpFlow A z))
      (Matrix.trace A * Matrix.det (matrixExpFlow A t)) t := by
  have hshift :
      HasDerivAt
        (fun z : ℂ => Matrix.det (matrixExpFlow A (z - t)))
        (Matrix.trace A) t := by
    have hbase :
        HasDerivAt (fun u : ℂ => Matrix.det (matrixExpFlow A u)) (Matrix.trace A) (t - t) := by
      simpa using hasDerivAt_det_matrixExpFlow_zero A
    simpa using hbase.comp_sub_const t t
  have hmul := hshift.const_mul (Matrix.det (matrixExpFlow A t))
  convert hmul using 1
  · ext z
    rw [det_matrixExpFlow_eq_det_mul_shift A t z]
  · ring

/-- The constant matrix exponential flow has nonzero determinant at every time. -/
theorem det_matrixExpFlow_ne_zero (A : Matrix n n ℂ) (t : ℂ) :
    Matrix.det (matrixExpFlow A t) ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det (matrixExpFlow A t)).mp
    (isUnit_matrixExpFlow A t)).ne_zero

/--
Logarithmic derivative of the determinant along a constant matrix-exponential
flow.  This packages the branch-free `d log det` readout as `f' / f`.
-/
def detLogDerivative (A : Matrix n n ℂ) (t : ℂ) : ℂ :=
  deriv (fun z : ℂ => Matrix.det (matrixExpFlow A z)) t /
    Matrix.det (matrixExpFlow A t)

/--
Branch-free Jacobi/Liouville readout for the constant flow:
`(d/dt det(exp(tA))) / det(exp(tA)) = trace A`.
-/
theorem detLogDerivative_matrixExpFlow_eq_trace (A : Matrix n n ℂ) (t : ℂ) :
    detLogDerivative A t = Matrix.trace A := by
  unfold detLogDerivative
  rw [(hasDerivAt_det_matrixExpFlow A t).deriv]
  field_simp [det_matrixExpFlow_ne_zero A t]

/-- Determinant of the constant matrix exponential flow. -/
theorem det_matrixExpFlow_eq_exp_trace_mul (A : Matrix n n ℂ) :
    ∀ t : ℂ,
      Matrix.det (matrixExpFlow A t) =
        NormedSpace.exp (t * Matrix.trace A) :=
  eq_normed_exp_mul_of_hasDerivAt_eq_const_mul
    (c := Matrix.trace A)
    (f := fun t : ℂ => Matrix.det (matrixExpFlow A t))
    (fun t => by simpa using hasDerivAt_det_matrixExpFlow A t)
    (by simp [matrixExpFlow])

end MatrixDetExpTraceJacobi

namespace Matrix

open Matrix.Norms.Frobenius

/--
The determinant of a complex matrix exponential is the exponential of the
trace.

This closes the matrix-exponential TODO over `ℂ` using only mathlib-rooted
ingredients: the matrix exponential flow derivative, the determinant derivative
at the identity from the characteristic-polynomial coefficient lemma, the
exponential flow law, and scalar ODE uniqueness.
-/
theorem det_exp_eq_exp_trace
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) := by
  simpa [InfoGeometry.Canonical.MatrixDetExpTraceJacobi.matrixExpFlow] using
    (InfoGeometry.Canonical.MatrixDetExpTraceJacobi.det_matrixExpFlow_eq_exp_trace_mul
      (n := n) A 1)

/-- Real-to-complex compatibility for the matrix exponential. -/
lemma map_matrix_exp_real_complex
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    (algebraMap ℝ ℂ).mapMatrix (NormedSpace.exp A) =
      NormedSpace.exp ((algebraMap ℝ ℂ).mapMatrix A) := by
  have hcont : Continuous (fun M : Matrix n n ℝ => (algebraMap ℝ ℂ).mapMatrix M) := by
    simpa [RingHom.mapMatrix_apply] using
      (Continuous.matrix_map (A := fun M : Matrix n n ℝ => M)
        continuous_id (continuous_algebraMap ℝ ℂ))
  exact NormedSpace.map_exp ((algebraMap ℝ ℂ).mapMatrix) hcont A

/-- Trace commutes with real-to-complex matrix base change. -/
lemma trace_map_real_complex
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    Matrix.trace ((algebraMap ℝ ℂ).mapMatrix A) =
      (algebraMap ℝ ℂ) (Matrix.trace A) := by
  simpa [RingHom.mapMatrix_apply] using
    (AddMonoidHom.map_trace (algebraMap ℝ ℂ) A).symm

/--
The determinant of a real matrix exponential is the exponential of the trace.

This is transferred from the complex theorem by the canonical embedding
`ℝ → ℂ`.
-/
theorem det_exp_eq_exp_trace_real
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) := by
  apply Complex.ofReal_injective
  have hcomplex := Matrix.det_exp_eq_exp_trace ((algebraMap ℝ ℂ).mapMatrix A)
  have hmapExp := map_matrix_exp_real_complex A
  have hdet :
      (algebraMap ℝ ℂ) (Matrix.det (NormedSpace.exp A)) =
        Matrix.det (NormedSpace.exp ((algebraMap ℝ ℂ).mapMatrix A)) := by
    rw [RingHom.map_det, hmapExp]
  have htrace :
      (algebraMap ℝ ℂ) (NormedSpace.exp (Matrix.trace A)) =
        NormedSpace.exp (Matrix.trace ((algebraMap ℝ ℂ).mapMatrix A)) := by
    change Complex.ofReal (NormedSpace.exp (Matrix.trace A)) =
      NormedSpace.exp (Matrix.trace ((algebraMap ℝ ℂ).mapMatrix A))
    rw [← Real.exp_eq_exp_ℝ, Complex.ofReal_exp, Complex.exp_eq_exp_ℂ,
      trace_map_real_complex]
    simp
  calc
    (algebraMap ℝ ℂ) (Matrix.det (NormedSpace.exp A))
        = Matrix.det (NormedSpace.exp ((algebraMap ℝ ℂ).mapMatrix A)) := hdet
    _ = NormedSpace.exp (Matrix.trace ((algebraMap ℝ ℂ).mapMatrix A)) := hcomplex
    _ = (algebraMap ℝ ℂ) (NormedSpace.exp (Matrix.trace A)) := htrace.symm

end Matrix
