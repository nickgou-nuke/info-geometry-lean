import Mathlib
import InfoGeometry.External.Auto.KanCayley
import InfoGeometry.External.Auto.TraceSeparationFlow

noncomputable section

open Matrix Complex

namespace InfoGeometry.GrandUnification.KANTraceSectorization

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/--
`Λ = |det g|` split (continuous, phase-free scale) and `η = det g / |det g|` (phase).
-/
def determinantScale (g : M2C) : ℝ := ‖g.det‖
def determinantPhase (g : M2C) : ℂ := g.det / (‖g.det‖ : ℂ)

def normalizeScale (g : M2C) : M2C :=
  ((Real.sqrt (determinantScale g) : ℝ)⁻¹ : ℂ) • g

lemma determinantScale_nonneg (g : M2C) : 0 ≤ determinantScale g := by
  simp [determinantScale]

lemma determinantScale_ne_zero_of_det_ne_zero (g : M2C) (hg : g.det ≠ 0) :
    determinantScale g ≠ 0 := by
  intro h
  exact hg (by
    exact (norm_eq_zero.mp h))

lemma determinantPhase_unit (g : M2C) (hg : g.det ≠ 0) : ‖determinantPhase g‖ = 1 := by
  have hnorm : ‖g.det‖ ≠ 0 := by simpa [norm_eq_zero] using hg
  calc
    ‖determinantPhase g‖ = ‖g.det‖ / ‖(‖g.det‖ : ℂ)‖ := by
      rw [determinantPhase, norm_div]
    _ = ‖g.det‖ / ‖g.det‖ := by simp
    _ = 1 := by
      have h : (‖g.det‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm
      field_simp [h]

lemma normalizeScale_det (g : M2C) (hg : g.det ≠ 0) :
    (normalizeScale g).det = determinantPhase g := by
  have hnorm : ‖g.det‖ ≠ 0 := by
    simpa [norm_eq_zero] using hg
  have hsqrt : (Real.sqrt (‖g.det‖) : ℝ) ≠ 0 := by
    intro hs
    exact hnorm ((Real.sqrt_eq_zero (norm_nonneg _)).1 hs)
  have haux : (((Real.sqrt ‖g.det‖ : ℝ)⁻¹ : ℂ) ^ (2 : ℕ)) * g.det = g.det / (‖g.det‖ : ℂ) := by
    have hsq : (((Real.sqrt ‖g.det‖ : ℝ)) : ℂ) ^ (2 : ℕ) = (‖g.det‖ : ℂ) := by
      exact_mod_cast (Real.sq_sqrt (show 0 ≤ ‖g.det‖ by exact norm_nonneg _))
    calc
      (((Real.sqrt ‖g.det‖ : ℝ)⁻¹ : ℂ) ^ (2 : ℕ)) * g.det
          = ((((Real.sqrt ‖g.det‖ : ℝ) : ℂ) ^ (2 : ℕ))⁻¹) * g.det := by
            rw [inv_pow]
      _ = ((‖g.det‖ : ℂ)⁻¹) * g.det := by rw [hsq]
      _ = g.det / (‖g.det‖ : ℂ) := by
        field_simp [hsqrt]
  calc
    (normalizeScale g).det = (((Real.sqrt ‖g.det‖ : ℝ)⁻¹ : ℂ) ^ (2 : ℕ)) * g.det := by
      simp [normalizeScale, determinantScale, Matrix.det_smul]
    _ = g.det / (‖g.det‖ : ℂ) := haux

-- Existing K/A/N blocks from `KanCayley`.
def compactBlock (θ : ℝ) : M2C := KPart θ

def dilationBlock (β : ℝ) : M2C := APart β

def nilpotentBlock (z : ℂ) : M2C := NPart z

def nilpotentShearBlock (z : ℂ) : M2C := nilpotentShear z

-- KAN block determinant/trace identities.
theorem kanBlock_dets (θ : ℝ) (β : ℝ) (z : ℂ) :
    (compactBlock θ).det = 1 ∧ (dilationBlock β).det = 1 ∧ (nilpotentBlock z).det = 1 := by
  exact ⟨det_KPart θ, det_APart β, det_NPart z⟩

/-- Pauli generators over `ℂ`. -/
def pauliSigmaX : M2C := !![0, 1; 1, 0]
def pauliSigmaY : M2C := !![0, -Complex.I; Complex.I, 0]
def pauliSigmaZ : M2C := !![1, 0; 0, -1]

def pauliComplex (vx vy vz : ℂ) : M2C :=
  vx • pauliSigmaX + vy • pauliSigmaY + vz • pauliSigmaZ

/-- For `M = v_x σ_x + v_y σ_y + v_z σ_z`, `det M = -(v_x^2+v_y^2+v_z^2)`. -/
theorem pauliComplex_det (vx vy vz : ℂ) :
    (pauliComplex vx vy vz).det = - (vx * vx + vy * vy + vz * vz) := by
  have hxy : (vx + -(vy * Complex.I)) * (vx + vy * Complex.I) = vx * vx + vy * vy := by
    ring_nf
    simp
  have hdet :
      (pauliComplex vx vy vz).det = -(vz * vz) - (vx + -(vy * Complex.I)) * (vx + vy * Complex.I) := by
    simp [pauliComplex, pauliSigmaX, pauliSigmaY, pauliSigmaZ, Matrix.det_fin_two]
  calc
    (pauliComplex vx vy vz).det = -(vz * vz) - (vx + -(vy * Complex.I)) * (vx + vy * Complex.I) := hdet
    _ = -(vz * vz) - (vx * vx + vy * vy) := by simpa [hxy]
    _ = - (vx * vx + vy * vy + vz * vz) := by ring

/-- Compact Lie generator `k = i(θ·σ)` with compact quadratic form `+|θ|²`. -/
def compactGenerator (θx θy θz : ℝ) : M2C :=
  pauliComplex ((Complex.I * (θx : ℂ))) ((Complex.I * (θy : ℂ))) ((Complex.I * (θz : ℂ)))

theorem compactGenerator_det (θx θy θz : ℝ) :
    (compactGenerator θx θy θz).det = ((θx ^ 2 + θy ^ 2 + θz ^ 2 : ℝ) : ℂ) := by
  rw [compactGenerator, pauliComplex_det]
  have hθx : (Complex.I * (θx : ℂ)) * (Complex.I * (θx : ℂ)) = -((θx : ℂ)^2) := by
    ring_nf
    simp
  have hθy : (Complex.I * (θy : ℂ)) * (Complex.I * (θy : ℂ)) = -((θy : ℂ)^2) := by
    ring_nf
    simp
  have hθz : (Complex.I * (θz : ℂ)) * (Complex.I * (θz : ℂ)) = -((θz : ℂ)^2) := by
    ring_nf
    simp
  rw [hθx, hθy, hθz]
  have hsq :
      ((θx ^ 2 + θy ^ 2 + θz ^ 2 : ℝ) : ℂ) = (θx : ℂ)^2 + (θy : ℂ)^2 + (θz : ℂ)^2 := by
    norm_num
  rw [hsq]
  ring

/-- Non-compact generator `a = (a_x σ_x + a_y σ_y + a_z σ_z)` with `det = -( |a|² )`. -/
def noncompactGenerator (ax ay az : ℝ) : M2C :=
  pauliComplex (ax : ℂ) (ay : ℂ) (az : ℂ)

theorem noncompactGenerator_det (ax ay az : ℝ) :
    (noncompactGenerator ax ay az).det = -((ax ^ 2 + ay ^ 2 + az ^ 2 : ℝ) : ℂ) := by
  rw [noncompactGenerator, pauliComplex_det]
  have hsq :
      ((ax ^ 2 + ay ^ 2 + az ^ 2 : ℝ) : ℂ) = (ax : ℂ)^2 + (ay : ℂ)^2 + (az : ℂ)^2 := by
    norm_num
  rw [hsq]
  ring

/-- Nilpotent generator in the unipotent direction, with `det = 0`. -/
def nilpotentGenerator (ν : ℂ) : M2C := !![0, ν; 0, 0]

theorem nilpotentGenerator_det (ν : ℂ) : (nilpotentGenerator ν).det = 0 := by
  simp [nilpotentGenerator, Matrix.det_fin_two]

theorem nilpotentGenerator_eq_nilpotentShear (ν : ℂ) :
    nilpotentGenerator ν = nilpotentShearBlock ν := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [nilpotentGenerator, nilpotentShearBlock, nilpotentShear, NPart]


-- Trace is always zero for `su(2)`/`sl(2)`-type traceless generators.
theorem compactGenerator_trace_zero (θx θy θz : ℝ) :
    Matrix.trace (compactGenerator θx θy θz) = 0 := by
  simp [compactGenerator, pauliComplex, pauliSigmaX, pauliSigmaY, pauliSigmaZ]

theorem noncompactGenerator_trace_zero (ax ay az : ℝ) :
    Matrix.trace (noncompactGenerator ax ay az) = 0 := by
  simp [noncompactGenerator, pauliComplex, pauliSigmaX, pauliSigmaY, pauliSigmaZ]

theorem nilpotentGenerator_trace_zero (ν : ℂ) :
    Matrix.trace (nilpotentGenerator ν) = 0 := by
  simp [nilpotentGenerator]

-- Compatibility with the trace-sector split from `TraceSeparationFlow`.
theorem compactGenerator_traceless (θx θy θz : ℝ) :
    TraceSeparation.tracelessSector (compactGenerator θx θy θz) = compactGenerator θx θy θz := by
  have htr : Matrix.trace (compactGenerator θx θy θz) = 0 :=
    compactGenerator_trace_zero θx θy θz
  simp [TraceSeparation.tracelessSector, TraceSeparation.traceSector, htr]



-- Pauli coordinate extraction from arbitrary 2×2 matrices.

def pauliScalar (X : M2C) : ℂ := X.trace / 2

def pauliCoeffX (X : M2C) : ℂ := (X 0 1 + X 1 0) / 2

def pauliCoeffY (X : M2C) : ℂ := (X 1 0 - X 0 1) / (2 * Complex.I)

def pauliCoeffZ (X : M2C) : ℂ := (X 0 0 - X 1 1) / 2

/-- Full Pauli reconstruction:
`X = (tr X / 2)•I + a σx + b σy + c σz`. -/
theorem pauli_reconstruct (X : M2C) :
    X = pauliScalar X • (1 : M2C) +
      pauliComplex (pauliCoeffX X) (pauliCoeffY X) (pauliCoeffZ X) := by
  ext i j <;> fin_cases i <;> fin_cases j
  · simp [pauliScalar, pauliCoeffX, pauliCoeffY, pauliCoeffZ, pauliComplex,
      pauliSigmaX, pauliSigmaY, pauliSigmaZ, Matrix.trace]
    ring_nf
  · simp [pauliScalar, pauliCoeffX, pauliCoeffY, pauliCoeffZ, pauliComplex,
      pauliSigmaX, pauliSigmaY, pauliSigmaZ, Matrix.trace]
    field_simp [Complex.I_ne_zero]
    ring
  · simp [pauliScalar, pauliCoeffX, pauliCoeffY, pauliCoeffZ, pauliComplex,
      pauliSigmaX, pauliSigmaY, pauliSigmaZ, Matrix.trace]
    field_simp [Complex.I_ne_zero]
    ring
  · simp [pauliScalar, pauliCoeffX, pauliCoeffY, pauliCoeffZ, pauliComplex,
      pauliSigmaX, pauliSigmaY, pauliSigmaZ, Matrix.trace]
    ring_nf

/-- Traceless extraction (`tr X = 0`): `X = a σx + b σy + c σz`. -/
theorem traceless_reconstruct (X : M2C) (htr : Matrix.trace X = 0) :
    X = pauliComplex (pauliCoeffX X) (pauliCoeffY X) (pauliCoeffZ X) := by
  have h0 : pauliScalar X = 0 := by
    simpa [pauliScalar] using htr
  simpa [h0, zero_smul] using (pauli_reconstruct X)

/-- On determinant-one sector, any abstract log map lands in the traceless Pauli span. -/
theorem log_on_SL2_reconstruct_pauli
    (g : M2C) [Fact (g.det = 1)] (L : TraceSeparation.LogTraceModel) :
    L.log g = pauliComplex (pauliCoeffX (L.log g)) (pauliCoeffY (L.log g)) (pauliCoeffZ (L.log g)) := by
  have htr : Matrix.trace (L.log g) = 0 := TraceSeparation.log_map_selfclosed (g := g) (L := L)
  simpa [pauliScalar] using (traceless_reconstruct (L.log g) htr)

/-- Nilpotent Pauli ladder `σ_+ = (σx + iσy)/2`. -/
def sigmaPlus : M2C :=
  (1 / 2 : ℂ) • (pauliSigmaX + (Complex.I : ℂ) • pauliSigmaY)

theorem sigmaPlus_eq_matrix : sigmaPlus = !![0, 1; 0, 0] := by
  ext i j <;> fin_cases i <;> fin_cases j
  · simp [sigmaPlus, pauliSigmaX, pauliSigmaY]
  · norm_num [sigmaPlus, pauliSigmaX, pauliSigmaY]
  · simp [sigmaPlus, pauliSigmaX, pauliSigmaY]
  · simp [sigmaPlus, pauliSigmaX, pauliSigmaY]

theorem sigmaPlus_sq : sigmaPlus * sigmaPlus = (0 : M2C) := by
  rw [sigmaPlus_eq_matrix]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

-- Square of any scalar multiple of σ₊ is zero.
theorem sigmaPlus_scalar_sq (z : ℂ) : (z • sigmaPlus) ^ (2 : ℕ) = 0 := by
  rw [pow_two]
  calc
    (z • sigmaPlus) * (z • sigmaPlus) = z • z • (sigmaPlus * sigmaPlus) := by
      simp [smul_smul]
    _ = 0 := by simp [sigmaPlus_sq]

/-- Scalar multiples of σ₊ are nilpotent. -/
theorem sigmaPlus_scalar_isNilpotent (z : ℂ) : IsNilpotent (z • sigmaPlus) :=
  ⟨2, sigmaPlus_scalar_sq z⟩

/-- Exact nilpotent exponential: `expₙ(z σ₊)=I+z σ₊` (finite polynomial form). -/
theorem sigmaPlus_scalar_exp (z : ℂ) :
    IsNilpotent.exp (z • sigmaPlus) = (1 : M2C) + z • sigmaPlus := by
  calc
    IsNilpotent.exp (z • sigmaPlus)
        = ∑ i ∈ Finset.range 2, (i.factorial : ℚ)⁻¹ • ((z • sigmaPlus) ^ i) := by
          simpa using (IsNilpotent.exp_eq_sum (a := z • sigmaPlus) (k := 2)
            (sigmaPlus_scalar_sq z))
    _ = (1 : M2C) + z • sigmaPlus := by
      simp [pow_zero, pow_one, Finset.range, add_comm]

/-- Pauli nilpotent ladder span: `nilpotentGenerator ν = ν • σ_+`. -/
theorem nilpotentGenerator_eq_smul_sigmaPlus (ν : ℂ) :
    nilpotentGenerator ν = ν • sigmaPlus := by
  calc
    nilpotentGenerator ν = ν • !![0, 1; 0, 0] := by
      ext i j <;> fin_cases i <;> fin_cases j
      · simp [nilpotentGenerator]
      · simp [nilpotentGenerator]
      · simp [nilpotentGenerator]
      · simp [nilpotentGenerator]
    _ = ν • sigmaPlus := by rw [sigmaPlus_eq_matrix]

theorem nilpotentGenerator_isNilpotent (ν : ℂ) : IsNilpotent (nilpotentGenerator ν) := by
  simpa [nilpotentGenerator_eq_smul_sigmaPlus] using (sigmaPlus_scalar_isNilpotent (z := ν))

theorem nilpotentGenerator_exp (ν : ℂ) :
    IsNilpotent.exp (nilpotentGenerator ν) = (1 : M2C) + nilpotentGenerator ν := by
  rw [nilpotentGenerator_eq_smul_sigmaPlus ν]
  simpa [nilpotentGenerator_eq_smul_sigmaPlus] using (sigmaPlus_scalar_exp (z := ν))

end InfoGeometry.GrandUnification.KANTraceSectorization
