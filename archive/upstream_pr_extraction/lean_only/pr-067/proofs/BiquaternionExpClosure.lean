import Mathlib
open Matrix
open Complex

/-!
# Biquaternion Exponential Map Self-Closure

The biquaternion algebra ℍ_ℂ ≅ Cℓ_{3,0}(ℝ) ≅ M₂(ℂ) has a self-closed exponential map.
The Lie algebra gl(2,ℂ) coincides with the associative algebra M₂(ℂ), and the Lie group
GL(2,ℂ) is an open subset of M₂(ℂ). The exponential map `exp : M₂(ℂ) → M₂(ℂ)` maps
the space into itself.

Because of the identity `T² = r²·I` for any traceless `T = xσ₁ + yσ₂ + zσ₃`,
the exponential series collapses into a closed form:
  exp(αI + T) = e^α [cosh(r)I + sinh(r)/r · T]
where `r² = x² + y² + z²`.

We formalize the core squaring identity and the closed-form definition.
-/

noncomputable section

namespace BiquaternionExpClosure

/-- Pauli σ₁ -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli σ₂ -/
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli σ₃ -/
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- A traceless biquaternion in the Pauli basis -/
def tracelessPauli (x y z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  x • σ₁ + y • σ₂ + z • σ₃

/-- 
The fundamental squaring identity: T² = (x² + y² + z²) · I₂
This is the geometric engine that collapses the Taylor series.
-/
theorem tracelessPauli_sq (x y z : ℂ) :
    tracelessPauli x y z * tracelessPauli x y z =
      (x * x + y * y + z * z) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tracelessPauli, σ₁, σ₂, σ₃,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (ring_nf; try simp; try ring)

/-- A general biquaternion parameterized by (α, x, y, z) -/
def biquaternion (α x y z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  α • (1 : Matrix (Fin 2) (Fin 2) ℂ) + tracelessPauli x y z

/--
The closed-form exponential of a biquaternion, directly returning a matrix
in the same Pauli-basis space.
This explicitly witnesses the self-closure: the output is a 2×2 complex matrix
constructed as a linear combination of I, σ₁, σ₂, σ₃.

We assume a complex square root `r` has been chosen such that `r² = x² + y² + z²`.
-/
def biquaternionExp (α r x y z : ℂ) (_hr : r * r = x * x + y * y + z * z) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let exp_α := Complex.exp α
  let cosh_r := Complex.cosh r
  let sinh_r_over_r := if r = 0 then (1 : ℂ) else Complex.sinh r / r
  exp_α • (cosh_r • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
           sinh_r_over_r • tracelessPauli x y z)

/-- 
The exponential of a biquaternion evaluates to an element of M₂(ℂ),
which we can verify forms a valid biquaternion decomposition itself
by extracting its Pauli coordinates algebraically.
-/
theorem biquaternionExp_is_M2C (α r x y z : ℂ) (hr : r * r = x * x + y * y + z * z) :
    ∃ (a₀ a₁ a₂ a₃ : ℂ),
      biquaternionExp α r x y z hr =
        a₀ • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        a₁ • σ₁ +
        a₂ • σ₂ +
        a₃ • σ₃ := by
  use Complex.exp α * Complex.cosh r
  use Complex.exp α * (if r = 0 then (1 : ℂ) else Complex.sinh r / r) * x
  use Complex.exp α * (if r = 0 then (1 : ℂ) else Complex.sinh r / r) * y
  use Complex.exp α * (if r = 0 then (1 : ℂ) else Complex.sinh r / r) * z
  simp only [biquaternionExp, tracelessPauli]
  module

/-! ## Trace removal, determinant classifier, and Weyl thermodynamic scale

This is the algebraic core of the verbal picture: a biquaternion decomposes into
an identity/trace part plus a traceless Pauli part; the determinant classifies
the normalized element; and a Weyl gauge scale can diffuse an operator and bring
it back by inverse scaling.
-/

/-- Trace coordinate of a biquaternion: `tr(αI+T)=2α`. -/
theorem trace_biquaternion (α x y z : ℂ) :
    Matrix.trace (biquaternion α x y z) = 2 * α := by
  simp [biquaternion, tracelessPauli, σ₁, σ₂, σ₃, Matrix.trace_fin_two]
  ring

/-- Remove the scalar/identity trace part from a `2×2` matrix. -/
def removeTrace (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  A - ((2 : ℂ)⁻¹ * Matrix.trace A) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Removing the trace from a biquaternion leaves precisely its Pauli/traceless part. -/
theorem removeTrace_biquaternion (α x y z : ℂ) :
    removeTrace (biquaternion α x y z) = tracelessPauli x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [removeTrace, biquaternion, tracelessPauli, σ₁, σ₂, σ₃,
      Matrix.trace_fin_two] <;> ring

/-- The Pauli/traceless part has trace zero. -/
theorem trace_tracelessPauli (x y z : ℂ) :
    Matrix.trace (tracelessPauli x y z) = 0 := by
  simp [tracelessPauli, σ₁, σ₂, σ₃, Matrix.trace_fin_two]

/-- Determinant classifier of a biquaternion: scalar part squared minus Pauli norm squared. -/
theorem det_biquaternion (α x y z : ℂ) :
    (biquaternion α x y z).det = α * α - (x * x + y * y + z * z) := by
  simp [biquaternion, tracelessPauli, σ₁, σ₂, σ₃, Matrix.det_fin_two]
  ring_nf
  simp
  ring

/-- Weyl diffusion by a nonzero scale.  Think of `s` as the thermodynamic scale
accumulated during parabolic/Rindler diffusion time. -/
def weylDiffuse (s : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  s • A

/-- Gauge-return by the inverse Weyl scale. -/
def weylReturn (s : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  s⁻¹ • A

/-- Diffusion followed by inverse Weyl return recovers the operator for nonzero scale. -/
theorem weylReturn_weylDiffuse {s : ℂ} (hs : s ≠ 0) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    weylReturn s (weylDiffuse s A) = A := by
  ext i j
  simp [weylReturn, weylDiffuse, hs]

/-- Rindler/Gibbs weights for the two chiral parity sectors. -/
def gibbsPlus (θ : ℝ) : ℝ := Real.exp θ

def gibbsMinus (θ : ℝ) : ℝ := Real.exp (-θ)

/-- Ordinary partition function over the two chiral parity sectors. -/
def rindlerPartition (θ : ℝ) : ℝ := gibbsPlus θ + gibbsMinus θ

/-- Witten/chiral-parity insertion: plus sector minus minus sector. -/
def chiralParityPartition (θ : ℝ) : ℝ := gibbsPlus θ - gibbsMinus θ

/-- The rapidity partition is `2 cosh θ`. -/
theorem rindlerPartition_eq_two_cosh (θ : ℝ) :
    rindlerPartition θ = 2 * Real.cosh θ := by
  simp [rindlerPartition, gibbsPlus, gibbsMinus, Real.cosh_eq]
  ring

/-- The chiral/Witten partition is `2 sinh θ`. -/
theorem chiralParityPartition_eq_two_sinh (θ : ℝ) :
    chiralParityPartition θ = 2 * Real.sinh θ := by
  simp [chiralParityPartition, gibbsPlus, gibbsMinus, Real.sinh_eq]
  ring

/-- Grand-canonical Souriau beta-vector data for one charge sector. -/
structure SouriauBetaVector where
  β : ℝ
  μ : ℝ
  energy : ℝ
  charge : ℝ

/-- The affine thermodynamic exponent before applying the exponential. -/
def SouriauBetaVector.exponent (B : SouriauBetaVector) : ℝ :=
  -B.β * (B.energy - B.μ * B.charge)

#check tracelessPauli_sq
#check biquaternionExp
#check biquaternionExp_is_M2C
#check removeTrace_biquaternion
#check det_biquaternion
#check weylReturn_weylDiffuse
#check rindlerPartition_eq_two_cosh
#check chiralParityPartition_eq_two_sinh

end BiquaternionExpClosure
