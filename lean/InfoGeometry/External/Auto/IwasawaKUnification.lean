import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Quantum.IwasawaKUnification

open Matrix

/--
Coordinates for the real `SL(2,ℝ)` K/A/N decomposition vocabulary:
compact angle `theta`, split-Cartan parameter `r`, and nilpotent shear `x`.
The split-Cartan factor is a determinant-one boost, not an overall volume
dilation.
-/
structure KANComponents where
  theta : ℝ
  r : ℝ
  x : ℝ

/-- Compact phase generator in `sl(2,ℝ)`. -/
def generatorK (θ : ℝ) : InfoGeometry.Algebra.FiniteSpin.Mat2R :=
  !![0, θ; -θ, 0]

/-- Split-Cartan generator in `sl(2,ℝ)` (a trace-zero boost generator). -/
def generatorA (r : ℝ) : InfoGeometry.Algebra.FiniteSpin.Mat2R :=
  !![r / 2, 0; 0, -r / 2]

/-- Nilpotent boundary/shear generator in `sl(2,ℝ)`. -/
def generatorN (x : ℝ) : InfoGeometry.Algebra.FiniteSpin.Mat2R :=
  !![0, x; 0, 0]

/-- Total infinitesimal KAN Hamiltonian. -/
def generatorH (c : KANComponents) : InfoGeometry.Algebra.FiniteSpin.Mat2R :=
  generatorK c.theta + generatorA c.r + generatorN c.x

/-- Compact rotation block. -/
def kPart (θ : ℝ) : InfoGeometry.Algebra.FiniteSpin.Mat2R :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

/-- Abelian split-Cartan boost block; its determinant is one. -/
def aPart (r : ℝ) : InfoGeometry.Algebra.FiniteSpin.Mat2R :=
  !![Real.exp (r / 2), 0; 0, Real.exp (-(r / 2))]

/-- Nilpotent/unipotent shear block. -/
def nPart (x : ℝ) : InfoGeometry.Algebra.FiniteSpin.Mat2R :=
  !![1, x; 0, 1]

/-- The shear displacement from identity is nilpotent. -/
def nilpotentBoundary (x : ℝ) : InfoGeometry.Algebra.FiniteSpin.Mat2R :=
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
  calc
    (generatorH c).trace =
        (generatorK c.theta).trace + (generatorA c.r).trace +
          (generatorN c.x).trace := by
      simp [generatorH, Matrix.trace_add]
    _ = 0 := by rw [generatorK_trace, generatorA_trace, generatorN_trace]; ring

/-- The compact rotation block has determinant one. -/
theorem det_kPart (θ : ℝ) : (kPart θ).det = 1 := by
  rw [Matrix.det_fin_two]
  have htrig : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    simpa [sq, add_comm] using Real.sin_sq_add_cos_sq θ
  simp [kPart, htrig]

/-- The split-Cartan boost block has determinant one. -/
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

/-- Uniqueness of the real K/A/N parameters, with the compact angle recorded
through its sine and cosine (so angles differing by a full turn are identified).
This is uniqueness for the displayed matrix family, not an existence theorem
for all of `SL(2, ℝ)`. -/
theorem kanProduct_parameters_unique
    (θ r x θ' r' x' : ℝ)
    (h : kPart θ * aPart r * nPart x =
      kPart θ' * aPart r' * nPart x') :
    r = r' ∧ x = x' ∧ Real.cos θ = Real.cos θ' ∧ Real.sin θ = Real.sin θ' := by
  let u := Real.exp (r / 2)
  let v := Real.exp (-(r / 2))
  let u' := Real.exp (r' / 2)
  let v' := Real.exp (-(r' / 2))
  have h00 : Real.cos θ * u = Real.cos θ' * u' := by
    have he := congrArg (fun M : InfoGeometry.Algebra.FiniteSpin.Mat2R => M 0 0) h
    simpa [kPart, aPart, nPart, u, u', Matrix.mul_apply, Fin.sum_univ_two] using he
  have h10 : -Real.sin θ * u = -Real.sin θ' * u' := by
    have he := congrArg (fun M : InfoGeometry.Algebra.FiniteSpin.Mat2R => M 1 0) h
    simpa [kPart, aPart, nPart, u, u', Matrix.mul_apply, Fin.sum_univ_two] using he
  have h01 : Real.cos θ * u * x + Real.sin θ * v =
      Real.cos θ' * u' * x' + Real.sin θ' * v' := by
    have he := congrArg (fun M : InfoGeometry.Algebra.FiniteSpin.Mat2R => M 0 1) h
    simpa [kPart, aPart, nPart, u, v, u', v', Matrix.mul_apply,
      Fin.sum_univ_two] using he
  have h11 : -Real.sin θ * u * x + Real.cos θ * v =
      -Real.sin θ' * u' * x' + Real.cos θ' * v' := by
    have he := congrArg (fun M : InfoGeometry.Algebra.FiniteSpin.Mat2R => M 1 1) h
    simpa [kPart, aPart, nPart, u, v, u', v', Matrix.mul_apply,
      Fin.sum_univ_two] using he
  have ht : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    simpa [sq, add_comm] using Real.sin_sq_add_cos_sq θ
  have ht' : Real.cos θ' ^ 2 + Real.sin θ' ^ 2 = 1 := by
    simpa [sq, add_comm] using Real.sin_sq_add_cos_sq θ'
  have h00sq := congrArg (fun z : ℝ => z ^ 2) h00
  have h10sq := congrArg (fun z : ℝ => z ^ 2) h10
  have hnorm : u ^ 2 = u' ^ 2 := by
    nlinarith [ht, ht', h00sq, h10sq]
  have hu : 0 < u := Real.exp_pos _
  have hu' : 0 < u' := Real.exp_pos _
  have huu : u = u' := by nlinarith [hnorm, hu, hu']
  have hr : r = r' := by
    have he : Real.exp (r / 2) = Real.exp (r' / 2) := by
      simpa [u, u'] using huu
    have hinj := Real.exp_injective he
    linarith
  have hcos : Real.cos θ = Real.cos θ' := by
    apply mul_left_cancel₀ hu.ne'
    calc
      u * Real.cos θ = Real.cos θ * u := by ring
      _ = Real.cos θ' * u' := h00
      _ = u * Real.cos θ' := by rw [huu]; ring
  have hsin : Real.sin θ = Real.sin θ' := by
    apply mul_left_cancel₀ hu.ne'
    calc
      u * Real.sin θ = -(-Real.sin θ * u) := by ring
      _ = -(-Real.sin θ' * u') := by rw [h10]
      _ = u * Real.sin θ' := by rw [huu]; ring
  have hdot :
      (Real.cos θ * u) * (Real.cos θ * u * x + Real.sin θ * v) +
        (-Real.sin θ * u) * (-Real.sin θ * u * x + Real.cos θ * v) =
      (Real.cos θ' * u') * (Real.cos θ' * u' * x' + Real.sin θ' * v') +
        (-Real.sin θ' * u') * (-Real.sin θ' * u' * x' + Real.cos θ' * v') := by
    calc
      _ = (Real.cos θ * u) *
            (Real.cos θ' * u' * x' + Real.sin θ' * v') +
          (-Real.sin θ * u) *
            (-Real.sin θ' * u' * x' + Real.cos θ' * v') := by rw [h01, h11]
      _ = _ := by rw [h00, h10]
  have hdot_left :
      (Real.cos θ * u) * (Real.cos θ * u * x + Real.sin θ * v) +
        (-Real.sin θ * u) * (-Real.sin θ * u * x + Real.cos θ * v) = u ^ 2 * x := by
    calc
      _ = u ^ 2 * x * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = u ^ 2 * x := by rw [ht]; ring
  have hdot_right :
      (Real.cos θ' * u') * (Real.cos θ' * u' * x' + Real.sin θ' * v') +
        (-Real.sin θ' * u') * (-Real.sin θ' * u' * x' + Real.cos θ' * v') =
      u' ^ 2 * x' := by
    calc
      _ = u' ^ 2 * x' * (Real.cos θ' ^ 2 + Real.sin θ' ^ 2) := by ring
      _ = u' ^ 2 * x' := by rw [ht']; ring
  have hxmul : u ^ 2 * x = u' ^ 2 * x' := by
    rw [← hdot_left, ← hdot_right]
    exact hdot
  have hx : x = x' := by
    rw [huu] at hxmul
    exact mul_left_cancel₀ (pow_ne_zero 2 hu'.ne') hxmul
  exact ⟨hr, hx, hcos, hsin⟩

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

end InfoGeometry.Quantum.IwasawaKUnification
