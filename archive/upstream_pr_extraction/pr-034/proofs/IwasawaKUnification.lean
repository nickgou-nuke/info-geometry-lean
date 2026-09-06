import Mathlib

noncomputable section

namespace InfoGeometry.Quantum.IwasawaKUnification

open Matrix

/--
Coordinates for the real `SL(2,ℝ)` K/A/N decomposition vocabulary:
compact phase `theta`, logarithmic Cartan scale `r`, and nilpotent shear `x`.
-/
structure KANComponents where
  theta : ℝ
  r : ℝ
  x : ℝ

/-- Local real transfer matrix. -/
abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Compact phase generator in `sl(2,ℝ)`. -/
def generatorK (θ : ℝ) : M2R :=
  !![0, θ; -θ, 0]

/-- Cartan/logarithmic scale generator in `sl(2,ℝ)`. -/
def generatorA (r : ℝ) : M2R :=
  !![r / 2, 0; 0, -r / 2]

/-- Nilpotent boundary/shear generator in `sl(2,ℝ)`. -/
def generatorN (x : ℝ) : M2R :=
  !![0, x; 0, 0]

/-- Total infinitesimal KAN Hamiltonian. -/
def generatorH (c : KANComponents) : M2R :=
  generatorK c.theta + generatorA c.r + generatorN c.x

/-- Compact rotation block. -/
def kPart (θ : ℝ) : M2R :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

/-- Abelian logarithmic scale block. -/
def aPart (r : ℝ) : M2R :=
  !![Real.exp (r / 2), 0; 0, Real.exp (-(r / 2))]

/-- Nilpotent/unipotent shear block. -/
def nPart (x : ℝ) : M2R :=
  !![1, x; 0, 1]

/-- The shear displacement from identity is nilpotent. -/
def nilpotentBoundary (x : ℝ) : M2R :=
  nPart x - 1

@[simp] theorem generatorK_trace (θ : ℝ) : (generatorK θ).trace = 0 := by
  simp [generatorK, Matrix.trace_fin_two]

@[simp] theorem generatorA_trace (r : ℝ) : (generatorA r).trace = 0 := by
  simp [generatorA, Matrix.trace_fin_two]
  ring

@[simp] theorem generatorN_trace (x : ℝ) : (generatorN x).trace = 0 := by
  simp [generatorN, Matrix.trace_fin_two]

/-- The nilpotent KAN generator squares to zero. -/
@[simp] theorem generatorN_sq (x : ℝ) : generatorN x * generatorN x = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [generatorN]

/--
Trace annihilation for the additive K/A/N Lie algebra generator.

This is the real doubled version of the log-det analytic condition:
the infinitesimal Hamiltonian lies in `sl(2,ℝ)`.
-/
theorem iwasawa_trace_annihilation (c : KANComponents) :
    (generatorH c).trace = 0 := by
  simp [generatorH, Matrix.trace_add]

/-- The compact rotation block has determinant one. -/
theorem det_kPart (θ : ℝ) : (kPart θ).det = 1 := by
  rw [Matrix.det_fin_two]
  have htrig : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    simpa [sq, add_comm] using Real.sin_sq_add_cos_sq θ
  simp [kPart, htrig]

/-- The Cartan scale block has determinant one. -/
theorem det_aPart (r : ℝ) : (aPart r).det = 1 := by
  rw [Matrix.det_fin_two]
  have hmul : Real.exp (r / 2) * Real.exp (-(r / 2)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  simp [aPart, hmul]

/-- The unipotent shear block has determinant one. -/
theorem det_nPart (x : ℝ) : (nPart x).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [nPart]

/-- The KAN transfer product is determinant-one. -/
theorem det_kanProduct (c : KANComponents) :
    (kPart c.theta * aPart c.r * nPart c.x).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_mul, det_kPart, det_aPart, det_nPart]
  norm_num

/-- The nilpotent boundary displacement squares to zero. -/
theorem nilpotentBoundary_sq (x : ℝ) :
    nilpotentBoundary x * nilpotentBoundary x = 0 := by
  have hform : nilpotentBoundary x = !![0, x; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilpotentBoundary, nPart]
  rw [hform]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The nilpotent boundary displacement has determinant zero. -/
theorem det_nilpotentBoundary (x : ℝ) : (nilpotentBoundary x).det = 0 := by
  have hform : nilpotentBoundary x = !![0, x; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilpotentBoundary, nPart]
  rw [hform]
  rw [Matrix.det_fin_two]
  simp

/-- Bundled synthesis: phase, scale, and boundary are one real KAN matrix language. -/
theorem iwasawa_kan_unification_synthesis (c : KANComponents) :
    (generatorH c).trace = 0 ∧
      (kPart c.theta).det = 1 ∧
      (aPart c.r).det = 1 ∧
      (nPart c.x).det = 1 ∧
      (kPart c.theta * aPart c.r * nPart c.x).det = 1 ∧
      nilpotentBoundary c.x * nilpotentBoundary c.x = 0 ∧
      (nilpotentBoundary c.x).det = 0 := by
  exact ⟨iwasawa_trace_annihilation c, det_kPart c.theta, det_aPart c.r,
    det_nPart c.x, det_kanProduct c, nilpotentBoundary_sq c.x,
    det_nilpotentBoundary c.x⟩

end InfoGeometry.Quantum.IwasawaKUnification
