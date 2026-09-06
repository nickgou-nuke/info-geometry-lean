import Mathlib

/-!
# 2×2 Matrix → determinant normalization → supergrading → Pauli/KAN chain

A finite answer to the requested chain for a real `2 × 2` matrix:

1. start with `M = [[a,b],[c,d]]`;
2. normalize by determinant in the positive determinant sector;
3. compute the `σ₃` Witten/supertrace;
4. split into traceful and traceless parts;
5. represent the matrix in the real Pauli basis
   `I, σ₃, σₓ, iσ₂`;
6. record the KAN factors and their infinitesimal traceless logarithmic
   generators.
-/

noncomputable section

open Matrix Real

namespace InfoGeometry.GrandUnification.Matrix2KANPauliChain

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Coordinate matrix. -/
def mat2 (a b c d : ℝ) : M2R := !![a, b; c, d]

/-- Pauli/scalar basis over the real split lane. -/
def sigma0 : M2R := 1
def sigma3 : M2R := !![1, 0; 0, -1]
def sigmaX : M2R := !![0, 1; 1, 0]
def iSigma2 : M2R := !![0, 1; -1, 0]

/-- Determinant coordinate. -/
def det2 (a b c d : ℝ) : ℝ := a * d - b * c

/-- Positive-determinant normalization to determinant one. -/
def detNormalize (a b c d : ℝ) : M2R :=
  (1 / Real.sqrt (det2 a b c d)) • mat2 a b c d

/-- Chiral/Witten supertrace `Tr(σ₃ M)`. -/
def wittenSupertrace (M : M2R) : ℝ :=
  Matrix.trace (sigma3 * M)

/-- Traceful scalar part. -/
def tracefulPart (M : M2R) : M2R :=
  ((Matrix.trace M) / 2) • (1 : M2R)

/-- Traceless part. -/
def tracelessPart (M : M2R) : M2R :=
  M - tracefulPart M

/-- Pauli coordinates: scalar, `σ₃`, `σₓ`, and `iσ₂` coefficients. -/
def scalarCoord (a _ _ d : ℝ) : ℝ := (a + d) / 2
def sigma3Coord (a _ _ d : ℝ) : ℝ := (a - d) / 2
def sigmaXCoord (_ b c _ : ℝ) : ℝ := (b + c) / 2
def iSigma2Coord (_ b c _ : ℝ) : ℝ := (b - c) / 2

/-- Compact K factor. -/
def KPart (θ : ℝ) : M2R := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Abelian A/squeeze factor. -/
def APart (α : ℝ) : M2R := !![Real.exp α, 0; 0, Real.exp (-α)]

/-- Nilpotent N/shear factor. -/
def NPart (n : ℝ) : M2R := !![1, n; 0, 1]

/-- KAN normal form block. -/
def KANMatrix (θ α n : ℝ) : M2R :=
  KPart θ * APart α * NPart n

/-- Infinitesimal logarithmic generator for `K`. -/
def kLog (θ : ℝ) : M2R := !![0, -θ; θ, 0]

/-- Infinitesimal logarithmic generator for `A`. -/
def aLog (α : ℝ) : M2R := !![α, 0; 0, -α]

/-- Infinitesimal logarithmic generator for `N`. -/
def nLog (n : ℝ) : M2R := !![0, n; 0, 0]

/-- Determinant formula for coordinates. -/
theorem mat2_det (a b c d : ℝ) :
    (mat2 a b c d).det = det2 a b c d := by
  simp [mat2, det2, Matrix.det_fin_two]

/-- Positive determinant normalization has determinant one. -/
theorem detNormalize_det_one {a b c d : ℝ} (hΔ : 0 < det2 a b c d) :
    (detNormalize a b c d).det = 1 := by
  simp [detNormalize, mat2, Matrix.det_fin_two, det2]
  have hΔ' : 0 < a * d - b * c := by simpa [det2] using hΔ
  have hs : Real.sqrt (a * d - b * c) ^ 2 = a * d - b * c :=
    Real.sq_sqrt (le_of_lt hΔ')
  have hsnz : Real.sqrt (a * d - b * c) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hΔ')
  field_simp [hsnz]
  nlinarith

/-- Supertrace is the difference of diagonal entries. -/
theorem wittenSupertrace_mat2 (a b c d : ℝ) :
    wittenSupertrace (mat2 a b c d) = a - d := by
  simp [wittenSupertrace, mat2, sigma3, Matrix.trace]
  ring

/-- Traceless part has zero trace. -/
theorem trace_tracelessPart (M : M2R) :
    Matrix.trace (tracelessPart M) = 0 := by
  simp [tracelessPart, tracefulPart, Matrix.trace]
  ring

/-- Traceful plus traceless reconstructs the matrix. -/
theorem traceful_add_traceless (M : M2R) :
    tracefulPart M + tracelessPart M = M := by
  simp [tracelessPart]

/-- Exact Pauli-basis reconstruction of an arbitrary real `2 × 2` matrix. -/
theorem pauli_reconstruction (a b c d : ℝ) :
    mat2 a b c d =
      scalarCoord a b c d • sigma0 +
      sigma3Coord a b c d • sigma3 +
      sigmaXCoord a b c d • sigmaX +
      iSigma2Coord a b c d • iSigma2 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [mat2, scalarCoord, sigma3Coord, sigmaXCoord, iSigma2Coord,
      sigma0, sigma3, sigmaX, iSigma2]
    ring

/-- Determinant in Pauli coordinates. -/
theorem pauli_det_formula (x z u v : ℝ) :
    (x • sigma0 + z • sigma3 + u • sigmaX + v • iSigma2 : M2R).det =
      x ^ 2 - z ^ 2 - u ^ 2 + v ^ 2 := by
  simp [sigma0, sigma3, sigmaX, iSigma2, Matrix.det_fin_two]
  ring

/-- Traceless Pauli determinant/light-cone form. -/
theorem traceless_pauli_det (z u v : ℝ) :
    (z • sigma3 + u • sigmaX + v • iSigma2 : M2R).det =
      - z ^ 2 - u ^ 2 + v ^ 2 := by
  simpa using pauli_det_formula 0 z u v

/-- K, A, and N all have determinant one. -/
theorem KPart_det (θ : ℝ) : (KPart θ).det = 1 := by
  simp [KPart, Matrix.det_fin_two]
  rw [← pow_two, ← pow_two]
  exact Real.cos_sq_add_sin_sq θ

theorem APart_det (α : ℝ) : (APart α).det = 1 := by
  simp [APart, Matrix.det_fin_two]
  rw [← Real.exp_add]
  simp

theorem NPart_det (n : ℝ) : (NPart n).det = 1 := by
  simp [NPart, Matrix.det_fin_two]

/-- Therefore the KAN product lies in the determinant-one sector. -/
theorem KANMatrix_det (θ α n : ℝ) :
    (KANMatrix θ α n).det = 1 := by
  simp [KANMatrix, Matrix.det_mul, KPart_det, APart_det, NPart_det]

/-- Each infinitesimal KAN logarithmic generator is traceless. -/
theorem kLog_trace (θ : ℝ) : Matrix.trace (kLog θ) = 0 := by simp [kLog, Matrix.trace]
theorem aLog_trace (α : ℝ) : Matrix.trace (aLog α) = 0 := by simp [aLog, Matrix.trace]
theorem nLog_trace (n : ℝ) : Matrix.trace (nLog n) = 0 := by simp [nLog, Matrix.trace]

/-- Consolidated chain theorem. -/
theorem matrix2_kan_pauli_chain_synthesis :
    (∀ a b c d : ℝ, (mat2 a b c d).det = det2 a b c d) ∧
    (∀ {a b c d : ℝ}, 0 < det2 a b c d → (detNormalize a b c d).det = 1) ∧
    (∀ a b c d : ℝ, wittenSupertrace (mat2 a b c d) = a - d) ∧
    (∀ M : M2R, Matrix.trace (tracelessPart M) = 0) ∧
    (∀ M : M2R, tracefulPart M + tracelessPart M = M) ∧
    (∀ a b c d : ℝ, mat2 a b c d =
      scalarCoord a b c d • sigma0 + sigma3Coord a b c d • sigma3 +
      sigmaXCoord a b c d • sigmaX + iSigma2Coord a b c d • iSigma2) ∧
    (∀ x z u v : ℝ, (x • sigma0 + z • sigma3 + u • sigmaX + v • iSigma2 : M2R).det =
      x ^ 2 - z ^ 2 - u ^ 2 + v ^ 2) ∧
    (∀ θ α n : ℝ, (KANMatrix θ α n).det = 1) ∧
    (∀ θ : ℝ, Matrix.trace (kLog θ) = 0) ∧
    (∀ α : ℝ, Matrix.trace (aLog α) = 0) ∧
    (∀ n : ℝ, Matrix.trace (nLog n) = 0) := by
  constructor
  · exact mat2_det
  constructor
  · intro a b c d hΔ
    exact detNormalize_det_one hΔ
  constructor
  · exact wittenSupertrace_mat2
  constructor
  · exact trace_tracelessPart
  constructor
  · exact traceful_add_traceless
  constructor
  · exact pauli_reconstruction
  constructor
  · exact pauli_det_formula
  constructor
  · exact KANMatrix_det
  constructor
  · exact kLog_trace
  constructor
  · exact aLog_trace
  · exact nLog_trace

end InfoGeometry.GrandUnification.Matrix2KANPauliChain
