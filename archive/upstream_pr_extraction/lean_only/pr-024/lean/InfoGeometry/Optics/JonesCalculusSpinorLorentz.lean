import Mathlib

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
structure BirefringentMedium where
  ordinary_index : ℝ
  extraordinary_index : ℝ
  optic_axis : Fin 3 → ℝ

def birefringentAnisotropy (B : BirefringentMedium) : ℝ :=
  B.extraordinary_index - B.ordinary_index

theorem birefringent_index_split (B : BirefringentMedium) :
    B.ordinary_index + birefringentAnisotropy B = B.extraordinary_index := by
  simp [birefringentAnisotropy]

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
