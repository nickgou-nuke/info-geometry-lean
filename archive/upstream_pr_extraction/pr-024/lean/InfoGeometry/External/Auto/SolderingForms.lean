import Mathlib

open Matrix

/-!
# Pauli/Cartan Soldering Forms

Lean mirror of `proofs/soldering_forms_sympy.py`, in a real split form.

The soldering map sends internal Pauli/Clifford coordinates to an external
`2 x 2` matrix representative of a spacetime vector.  The determinant is the
quadratic form.
-/

noncomputable section

def σ0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
def σx : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def σy_split : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
def σz : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def solder (t x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  t • σ0 + x • σx + y • σy_split + z • σz

theorem solder_eq (t x y z : ℝ) :
    solder t x y z = !![t + z, x + y; x - y, t - z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [solder, σ0, σx, σy_split, σz] <;> ring

theorem det_solder (t x y z : ℝ) :
    (solder t x y z).det = t ^ 2 - x ^ 2 + y ^ 2 - z ^ 2 := by
  rw [solder_eq, Matrix.det_fin_two]
  simp
  ring

theorem σx_sq : σx * σx = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σx]

theorem σy_split_sq : σy_split * σy_split = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σy_split]

theorem σz_sq : σz * σz = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σz]

theorem σx_anticomm_σy_split : σx * σy_split + σy_split * σx = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σx, σy_split]

theorem σy_split_anticomm_σz : σy_split * σz + σz * σy_split = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σy_split, σz]

theorem σz_anticomm_σx : σz * σx + σx * σz = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σz, σx]

theorem solder_linear_scale (s t x y z : ℝ) :
    solder (s * t) (s * x) (s * y) (s * z) = s • solder t x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [solder_eq] <;> ring

theorem det_solder_scale (s t x y z : ℝ) :
    (solder (s * t) (s * x) (s * y) (s * z)).det =
      s ^ 2 * (solder t x y z).det := by
  rw [det_solder, det_solder]
  ring

/-- Soldering coordinates (unsoldering by contraction).

    In this split-signature convention:
    - t uses `σ0` (identity),
    - x uses `σx`,
    - y uses `σy_split` with a minus sign,
    - z uses `σz`. -/
def solder_t (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ((M 0 0) + (M 1 1)) / 2

def solder_x (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ((M 0 1) + (M 1 0)) / 2

def solder_y (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ((M 0 1) - (M 1 0)) / 2

def solder_z (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ((M 0 0) - (M 1 1)) / 2

theorem solder_t_of_solder (t x y z : ℝ) :
    solder_t (solder t x y z) = (1 / 2 : ℝ) * Matrix.trace (solder t x y z) := by
  simp [solder_t, solder_eq, Matrix.trace]
  ring_nf

-- Trace of a soldered matrix is twice the time-coordinate.
theorem trace_solder_t (t x y z : ℝ) :
    Matrix.trace (solder t x y z) = 2 * t := by
  simp [solder_eq, Matrix.trace]
  ring

-- Trace contractions against split Pauli basis.
theorem trace_solder_x (t x y z : ℝ) :
    Matrix.trace (σx * solder t x y z) = 2 * x := by
  simp [solder_eq, Matrix.trace, σx, Fin.sum_univ_two]
  ring_nf

theorem trace_solder_y (t x y z : ℝ) :
    Matrix.trace (σy_split * solder t x y z) = -2 * y := by
  simp [solder_eq, Matrix.trace, σy_split, Fin.sum_univ_two]
  ring_nf

theorem trace_solder_z (t x y z : ℝ) :
    Matrix.trace (σz * solder t x y z) = 2 * z := by
  simp [solder_eq, Matrix.trace, σz, Fin.sum_univ_two]
  ring_nf

theorem solder_coord_t_of_solder (t x y z : ℝ) :
    solder_t (solder t x y z) = t := by
  simp [solder_t, solder_eq]

theorem solder_coord_x_of_solder (t x y z : ℝ) :
    solder_x (solder t x y z) = x := by
  simp [solder_x, solder_eq]

theorem solder_x_trace_of_solder (t x y z : ℝ) :
    solder_x (solder t x y z) = (1 / 2 : ℝ) * Matrix.trace (σx * (solder t x y z)) := by
  calc
    solder_x (solder t x y z) = x := by simp [solder_x, solder_eq]
    _ = (1 / 2 : ℝ) * (2 * x) := by ring
    _ = (1 / 2 : ℝ) * Matrix.trace (σx * (solder t x y z)) := by rw [trace_solder_x]

theorem solder_coord_y_of_solder (t x y z : ℝ) :
    solder_y (solder t x y z) = y := by
  simp [solder_y, solder_eq]

theorem solder_y_trace_of_solder (t x y z : ℝ) :
    solder_y (solder t x y z) = -(1 / 2 : ℝ) * Matrix.trace (σy_split * (solder t x y z)) := by
  calc
    solder_y (solder t x y z) = y := by simp [solder_y, solder_eq]
    _ = (-(1 / 2 : ℝ)) * (-2 * y) := by ring
    _ = -(1 / 2 : ℝ) * Matrix.trace (σy_split * (solder t x y z)) := by rw [trace_solder_y]

theorem solder_coord_z_of_solder (t x y z : ℝ) :
    solder_z (solder t x y z) = z := by
  simp [solder_z, solder_eq]

theorem solder_z_trace_of_solder (t x y z : ℝ) :
    solder_z (solder t x y z) = (1 / 2 : ℝ) * Matrix.trace (σz * (solder t x y z)) := by
  calc
    solder_z (solder t x y z) = z := by simp [solder_z, solder_eq]
    _ = (1 / 2 : ℝ) * (2 * z) := by ring
    _ = (1 / 2 : ℝ) * Matrix.trace (σz * (solder t x y z)) := by rw [trace_solder_z]

/-- Full inverse formula: coordinates + reconstruction are mutually inverse. -/
theorem solder_roundtrip (M : Matrix (Fin 2) (Fin 2) ℝ) :
    solder (solder_t M) (solder_x M) (solder_y M) (solder_z M) = M := by
  ext i j
  fin_cases i
  · fin_cases j
    · rw [solder_eq]
      simp [solder_t, solder_x, solder_y, solder_z]
      ring
    · rw [solder_eq]
      simp [solder_t, solder_x, solder_y, solder_z]
      ring
  · fin_cases j
    · rw [solder_eq]
      simp [solder_t, solder_x, solder_y, solder_z]
      ring
    · rw [solder_eq]
      simp [solder_t, solder_x, solder_y, solder_z]
      ring


def spinorDyad (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a * a, a * b; b * a, b * b]

theorem det_spinorDyad (a b : ℝ) : (spinorDyad a b).det = 0 := by
  rw [Matrix.det_fin_two]
  simp [spinorDyad]
  ring

/-- Pauli soldering theorem: the soldered matrix has the quadratic determinant,
    respects Weyl scaling, and sends spinor dyads to null boundary points. -/
theorem pauli_soldering_theorem :
    (∀ t x y z, (solder t x y z).det = t ^ 2 - x ^ 2 + y ^ 2 - z ^ 2) ∧
    (∀ s t x y z, solder (s * t) (s * x) (s * y) (s * z) = s • solder t x y z) ∧
    (∀ s t x y z,
      (solder (s * t) (s * x) (s * y) (s * z)).det =
        s ^ 2 * (solder t x y z).det) ∧
    (∀ t x y z, solder_t (solder t x y z) = t) ∧
    (∀ t x y z, solder_x (solder t x y z) = x) ∧
    (∀ t x y z, solder_y (solder t x y z) = y) ∧
    (∀ t x y z, solder_z (solder t x y z) = z) ∧
    (∀ t x y z, Matrix.trace (solder t x y z) = 2 * t) ∧
    (∀ t x y z, Matrix.trace (σx * solder t x y z) = 2 * x) ∧
    (∀ t x y z, Matrix.trace (σy_split * solder t x y z) = -2 * y) ∧
    (∀ t x y z, Matrix.trace (σz * solder t x y z) = 2 * z) ∧
    (∀ t x y z, solder_x (solder t x y z) = (1 / 2 : ℝ) * Matrix.trace (σx * (solder t x y z))) ∧
    (∀ t x y z, solder_y (solder t x y z) = -(1 / 2 : ℝ) * Matrix.trace (σy_split * (solder t x y z))) ∧
    (∀ t x y z, solder_z (solder t x y z) = (1 / 2 : ℝ) * Matrix.trace (σz * (solder t x y z))) ∧
    (∀ M : Matrix (Fin 2) (Fin 2) ℝ,
      solder (solder_t M) (solder_x M) (solder_y M) (solder_z M) = M) ∧
    (∀ a b, (spinorDyad a b).det = 0) := by
  exact ⟨det_solder, solder_linear_scale, det_solder_scale,
    solder_coord_t_of_solder, solder_coord_x_of_solder,
    solder_coord_y_of_solder, solder_coord_z_of_solder,
    trace_solder_t, trace_solder_x, trace_solder_y, trace_solder_z,
    solder_x_trace_of_solder, solder_y_trace_of_solder, solder_z_trace_of_solder,
    solder_roundtrip, det_spinorDyad⟩
