import InfoGeometry.Canonical.BiquaternionNegativeRootsLog
import InfoGeometry.Canonical.BiquaternionCliffordIso

open Matrix
open Complex

/-!
# Biquaternion Exponential Map Self-Closure

Maintained owner for the finite biquaternion exponential/trace/determinant/Weyl
packet recovered from the external-auto and removable-disk lanes. This module
reuses the canonical Pauli owners instead of duplicating the basis again.
-/

noncomputable section

namespace InfoGeometry.Canonical.BiquaternionExpClosure

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

def σ₁ : M2C := BiquaternionNegativeRootsLog.σ₁
def σ₂ : M2C := BiquaternionNegativeRootsLog.σ₂
def σ₃ : M2C := BiquaternionNegativeRootsLog.σ₃

def tracelessPauli (x y z : ℂ) : M2C :=
  BiquaternionNegativeRootsLog.T x y z

theorem tracelessPauli_sq (x y z : ℂ) :
    tracelessPauli x y z * tracelessPauli x y z =
      (x * x + y * y + z * z) • (1 : M2C) :=
  BiquaternionNegativeRootsLog.T_sq x y z

def biquaternion (α x y z : ℂ) : M2C :=
  α • (1 : M2C) + tracelessPauli x y z

def biquaternionExp (α r x y z : ℂ) (_hr : r * r = x * x + y * y + z * z) : M2C :=
  let exp_α := Complex.exp α
  let cosh_r := Complex.cosh r
  let sinh_r_over_r := if r = 0 then (1 : ℂ) else Complex.sinh r / r
  exp_α • (cosh_r • (1 : M2C) + sinh_r_over_r • tracelessPauli x y z)

theorem biquaternionExp_is_M2C (α r x y z : ℂ) (hr : r * r = x * x + y * y + z * z) :
    ∃ (a₀ a₁ a₂ a₃ : ℂ),
      biquaternionExp α r x y z hr =
        a₀ • (1 : M2C) + a₁ • σ₁ + a₂ • σ₂ + a₃ • σ₃ := by
  use Complex.exp α * Complex.cosh r
  use Complex.exp α * (if r = 0 then (1 : ℂ) else Complex.sinh r / r) * x
  use Complex.exp α * (if r = 0 then (1 : ℂ) else Complex.sinh r / r) * y
  use Complex.exp α * (if r = 0 then (1 : ℂ) else Complex.sinh r / r) * z
  simp only [biquaternionExp, tracelessPauli, σ₁, σ₂, σ₃, BiquaternionNegativeRootsLog.T]
  module

theorem trace_biquaternion (α x y z : ℂ) :
    Matrix.trace (biquaternion α x y z) = 2 * α := by
  simp [biquaternion, tracelessPauli, σ₁, σ₂, σ₃,
    BiquaternionNegativeRootsLog.T,
    BiquaternionNegativeRootsLog.σ₁,
    BiquaternionNegativeRootsLog.σ₂,
    BiquaternionNegativeRootsLog.σ₃,
    Matrix.trace_fin_two]
  ring

def removeTrace (A : M2C) : M2C :=
  A - ((2 : ℂ)⁻¹ * Matrix.trace A) • (1 : M2C)

theorem removeTrace_biquaternion (α x y z : ℂ) :
    removeTrace (biquaternion α x y z) = tracelessPauli x y z := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [removeTrace, biquaternion, tracelessPauli, σ₁, σ₂, σ₃,
      BiquaternionNegativeRootsLog.T,
      BiquaternionNegativeRootsLog.σ₁,
      BiquaternionNegativeRootsLog.σ₂,
      BiquaternionNegativeRootsLog.σ₃,
      Matrix.trace_fin_two] <;> ring

theorem trace_tracelessPauli (x y z : ℂ) :
    Matrix.trace (tracelessPauli x y z) = 0 := by
  simp [tracelessPauli, σ₁, σ₂, σ₃,
    BiquaternionNegativeRootsLog.T,
    BiquaternionNegativeRootsLog.σ₁,
    BiquaternionNegativeRootsLog.σ₂,
    BiquaternionNegativeRootsLog.σ₃,
    Matrix.trace_fin_two]

theorem det_biquaternion (α x y z : ℂ) :
    (biquaternion α x y z).det = α * α - (x * x + y * y + z * z) := by
  simp [biquaternion, tracelessPauli, σ₁, σ₂, σ₃,
    BiquaternionNegativeRootsLog.T,
    BiquaternionNegativeRootsLog.σ₁,
    BiquaternionNegativeRootsLog.σ₂,
    BiquaternionNegativeRootsLog.σ₃,
    Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
  ring_nf
  simp [Complex.I_mul_I]
  ring

def weylDiffuse (s : ℂ) (A : M2C) : M2C :=
  s • A

def weylReturn (s : ℂ) (A : M2C) : M2C :=
  s⁻¹ • A

theorem weylReturn_weylDiffuse {s : ℂ} (hs : s ≠ 0) (A : M2C) :
    weylReturn s (weylDiffuse s A) = A := by
  ext i j
  simp [weylReturn, weylDiffuse, hs]

def gibbsPlus (θ : ℝ) : ℝ := Real.exp θ
def gibbsMinus (θ : ℝ) : ℝ := Real.exp (-θ)
def rindlerPartition (θ : ℝ) : ℝ := gibbsPlus θ + gibbsMinus θ
def chiralParityPartition (θ : ℝ) : ℝ := gibbsPlus θ - gibbsMinus θ

theorem rindlerPartition_eq_two_cosh (θ : ℝ) :
    rindlerPartition θ = 2 * Real.cosh θ := by
  simp [rindlerPartition, gibbsPlus, gibbsMinus, Real.cosh_eq]
  ring

theorem chiralParityPartition_eq_two_sinh (θ : ℝ) :
    chiralParityPartition θ = 2 * Real.sinh θ := by
  simp [chiralParityPartition, gibbsPlus, gibbsMinus, Real.sinh_eq]
  ring

structure SouriauBetaVector where
  β : ℝ
  μ : ℝ
  energy : ℝ
  charge : ℝ

def SouriauBetaVector.exponent (B : SouriauBetaVector) : ℝ :=
  -B.β * (B.energy - B.μ * B.charge)

end InfoGeometry.Canonical.BiquaternionExpClosure
