import Mathlib.Tactic

open Matrix Complex

noncomputable section

namespace JonesCalculus

/-- Jones vectors: polarization spinors in `ℂ²`. -/
abbrev JonesVector := Fin 2 → ℂ

/-- Jones matrices: `2 × 2` complex matrices acting on polarization spinors. -/
abbrev JonesMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Raw projective polarization carrier: nonzero Jones spinors. -/
def PoincareSphere := {ψ : JonesVector // ψ ≠ 0}

/-- A determinant-one Jones matrix acts on raw spinors by matrix-vector multiplication. -/
def jonesSpinorAction (M : {M : JonesMatrix // M.det = 1}) (ψ : JonesVector) : JonesVector :=
  M.val.mulVec ψ

/-- Determinant-one readout for the finite `SL₂(ℂ)` Jones packet. -/
theorem jonesSpinorAction_det (M : {M : JonesMatrix // M.det = 1}) :
    M.val.det = 1 :=
  M.property

/-- Pauli matrices: a finite basis for the optical spinor algebra. -/
def pauli₁ : JonesMatrix := !![0, 1; 1, 0]
def pauli₂ : JonesMatrix := !![0, -I; I, 0]
def pauli₃ : JonesMatrix := !![1, 0; 0, -1]

theorem pauli_commutation :
    pauli₁ * pauli₂ - pauli₂ * pauli₁ = (2 * I : ℂ) • pauli₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli₁, pauli₂, pauli₃, Matrix.smul_apply] <;> ring_nf

theorem pauli_anticommutation :
    pauli₁ * pauli₂ + pauli₂ * pauli₁ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli₁, pauli₂]

/-! ### Scalar/vector readout of the Pauli product

The following is the associative soldering identity used by the Zorn
coordinates.  It is an identity in the Pauli matrix carrier; it does not
assert multiplicativity for a split-octonion product.
-/

abbrev PauliCoefficient := Fin 3 → ℂ

def pauliVector (x : PauliCoefficient) : JonesMatrix :=
  x 0 • pauli₁ + x 1 • pauli₂ + x 2 • pauli₃

def pauliDot (x y : PauliCoefficient) : ℂ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def pauliCross (x y : PauliCoefficient) : PauliCoefficient := fun i =>
  match i with
  | 0 => x 1 * y 2 - x 2 * y 1
  | 1 => x 2 * y 0 - x 0 * y 2
  | 2 => x 0 * y 1 - x 1 * y 0

theorem pauliVector_mul (x y : PauliCoefficient) :
    pauliVector x * pauliVector y =
      pauliDot x y • (1 : JonesMatrix) +
        I • pauliVector (pauliCross x y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVector, pauliDot, pauliCross, pauli₁, pauli₂, pauli₃,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply,
      Complex.I_mul_I, Complex.I_sq, pow_two] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem pauliVector_mul_scalar_readout (x y : PauliCoefficient) :
    (pauliVector x * pauliVector y) 0 0 +
        (pauliVector x * pauliVector y) 1 1 =
      2 * pauliDot x y := by
  rw [pauliVector_mul]
  simp [pauliDot, pauliVector, pauliCross, pauli₁, pauli₂, pauli₃,
    Matrix.smul_apply]
  ring

theorem pauliVector_mul_antisymmetric_readout (x y : PauliCoefficient) :
    pauliVector x * pauliVector y - pauliVector y * pauliVector x =
      (2 * I) • pauliVector (pauliCross x y) := by
  rw [pauliVector_mul, pauliVector_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliDot, pauliVector, pauliCross, Matrix.smul_apply,
      Complex.I_mul_I, Complex.I_sq, pow_two] <;>
    ring

/-- Stokes parameters for a Jones spinor. -/
def stokes (ψ : JonesVector) : ℝ × ℝ × ℝ × ℝ :=
  let s0 := Complex.normSq (ψ 0) + Complex.normSq (ψ 1)
  let s1 := Complex.normSq (ψ 0) - Complex.normSq (ψ 1)
  let s2 := 2 * ((ψ 0).re * (ψ 1).re + (ψ 0).im * (ψ 1).im)
  let s3 := 2 * ((ψ 0).re * (ψ 1).im - (ψ 0).im * (ψ 1).re)
  (s0, s1, s2, s3)

/-- The Stokes four-vector of any Jones spinor is lightlike. -/
theorem stokes_on_sphere (ψ : JonesVector) :
    let (s0, s1, s2, s3) := stokes ψ
    s1 ^ 2 + s2 ^ 2 + s3 ^ 2 = s0 ^ 2 := by
  simp [stokes, Complex.normSq]
  ring

/-- Birefringence as a finite anisotropy packet. -/
def BirefringentMedium : Type :=
  ℝ × (ℝ × (Fin 3 → ℝ))

namespace BirefringentMedium

@[simp] def ordinary_index (B : BirefringentMedium) : ℝ :=
  B.1

@[simp] def extraordinary_index (B : BirefringentMedium) : ℝ :=
  B.2.1

@[simp] def optic_axis (B : BirefringentMedium) : Fin 3 → ℝ :=
  B.2.2

end BirefringentMedium

def birefringentAnisotropy (B : BirefringentMedium) : ℝ :=
  B.extraordinary_index - B.ordinary_index

theorem birefringent_index_split (B : BirefringentMedium) :
    B.ordinary_index + birefringentAnisotropy B = B.extraordinary_index := by
  simp [birefringentAnisotropy, BirefringentMedium.ordinary_index,
    BirefringentMedium.extraordinary_index]

/-- Jones matrix for a diagonal birefringent plate with retardance `δ`. -/
def waveplate (δ : ℝ) (_axis : Fin 3 → ℝ) : JonesMatrix :=
  !![Complex.exp (-I * (δ : ℂ) / 2), 0;
     0, Complex.exp (I * (δ : ℂ) / 2)]

/-- The diagonal waveplate is determinant-one. -/
theorem waveplate_det_one (δ : ℝ) (axis : Fin 3 → ℝ) :
    (waveplate δ axis).det = 1 := by
  simp [waveplate, Matrix.det_fin_two, ← Complex.exp_add]
  have h : -(I * (δ : ℂ)) / 2 + I * (δ : ℂ) / 2 = 0 := by ring
  rw [h, Complex.exp_zero]

/-- Optical resonator holonomy as ordered multiplication of Jones matrices. -/
def resonatorHolonomy (matrices : List JonesMatrix) : JonesMatrix :=
  matrices.foldl (fun acc M => acc * M) 1

/-- Stability condition: trace lies in the closed radius-two disk. -/
def isStableResonator (M : JonesMatrix) : Prop :=
  M.trace.re ^ 2 + M.trace.im ^ 2 ≤ 4

/-- Sequential optical transport is action by the folded holonomy matrix. -/
theorem lightAsParallelTransport (path : List JonesMatrix) (initial_state : JonesVector) :
    (resonatorHolonomy path).mulVec initial_state =
      (path.foldl (fun acc M => acc * M) 1).mulVec initial_state := by
  rfl

end JonesCalculus
