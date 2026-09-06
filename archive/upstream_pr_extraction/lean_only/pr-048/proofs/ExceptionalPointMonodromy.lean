import Mathlib
import proofs.ExceptionalPointNullSector
import proofs.DeterminantSupergrading
import proofs.Z2NonAbelianBraiding
import proofs.LieFlowCompilerBridge

noncomputable section

open Matrix
open Complex
open Classical
open InfoGeometry.Canonical.LieFlowCompiler

namespace InfoGeometry.GrandUnification.ExceptionalPoints

/-- EP-local `Z₂` index (presence/absence). -/
def exceptionalLoopIndex
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) : SignType :=
  if IsExceptionalPoint H op z then (-1 : SignType) else (1 : SignType)

/-- By definition, exceptional points carry the `-1` branch. -/
theorem exceptionalLoopIndex_eq_neg_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (hep : IsExceptionalPoint H op z) :
    exceptionalLoopIndex op z = (-1 : SignType) := by
  simp [exceptionalLoopIndex, hep]

/-- Non-exceptional points are `+1` branch (`trivial` loop class). -/
theorem exceptionalLoopIndex_eq_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (hno : ¬ IsExceptionalPoint H op z) :
    exceptionalLoopIndex op z = (1 : SignType) := by
  simp [exceptionalLoopIndex, hno]

/-- Applying the loop monodromy to the exceptional branch gives the trivial sector. -/
theorem exceptionalLoopIndex_monodromy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (hep : IsExceptionalPoint H op z) :
    (- exceptionalLoopIndex op z) = (1 : SignType) := by
  simp [exceptionalLoopIndex, hep]

/-- `Z₂` sheet-flip action on `SignType`: one exceptional-loop step. -/
def epSheetMonodromy (s : SignType) : SignType := -s

theorem epSheetMonodromy_involution (s : SignType) :
    epSheetMonodromy (epSheetMonodromy s) = s := by
  simp [epSheetMonodromy]

/-- EP monodromy sector after `n` sheet windings. -/
def epLoopSector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (n : ℕ) : SignType :=
  if IsExceptionalPoint H op z then ((- (1 : SignType)) ^ n) * (-1 : SignType) else (1 : SignType)

/-- Base value: zero windings reproduce the endpoint loop index. -/
theorem epLoopSector_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) :
    epLoopSector op z 0 = exceptionalLoopIndex op z := by
  simp [epLoopSector, exceptionalLoopIndex, pow_zero]

/-- One winding flips the sector in the exceptional branch. -/
theorem epLoopSector_succ
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (n : ℕ) (hep : IsExceptionalPoint H op z) :
    epLoopSector op z (n + 1) = -epLoopSector op z n := by
  simp [epLoopSector, hep, pow_succ]

/-- Two windings return to the same exceptional sector (local `Z₂`). -/
theorem epLoopSector_two_step
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (n : ℕ) (hep : IsExceptionalPoint H op z) :
    epLoopSector op z (n + 2) = epLoopSector op z n := by
  calc
    epLoopSector op z (n + 2) = -epLoopSector op z (n + 1) := by
      simpa [Nat.add_assoc, epLoopSector, hep] using epLoopSector_succ op z (n + 1) hep
    _ = -(-epLoopSector op z n) := by
      rw [epLoopSector_succ op z n hep]
    _ = epLoopSector op z n := by simp

/-- If no EP is present, all windings are trivial in this sectoral packet. -/
theorem epLoopSector_non_exceptional
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (hno : ¬ IsExceptionalPoint H op z) (n : ℕ) :
    epLoopSector op z n = (1 : SignType) := by
  simp [epLoopSector, hno]

/-- Concrete `Z₂`-monodromy on doubled-sheet matrices via multiplication by `modular_j`. -/
abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

def epMatrixMonodromy (A : M2R) : M2R :=
  modular_j * A

theorem epMatrixMonodromy_grade (A : M2R) :
    superGrade (epMatrixMonodromy A) = epSheetMonodromy (superGrade A) := by
  simp [epMatrixMonodromy, epSheetMonodromy, superGrade_mul, superGrade_modular_j]

/-- One loop step is order-2 on sectors: applying twice returns the original matrix. -/
theorem epMatrixMonodromy_square (A : M2R) :
    epMatrixMonodromy (epMatrixMonodromy A) = A := by
  calc
    epMatrixMonodromy (epMatrixMonodromy A) = modular_j * (modular_j * A) := rfl
    _ = (modular_j * modular_j) * A := by simp [mul_assoc]
    _ = (1 : M2R) * A := by simp [modular_j_sq]
    _ = A := one_mul A

/-- Non-abelian transport for the local EP pair (`modular_j`, `chiralParity`). -/
theorem local_ep_nonabelian_transport :
    epMatrixMonodromy (chiralParity : M2R) ≠ (chiralParity : M2R) * modular_j := by
  simpa [epMatrixMonodromy] using
    InfoGeometry.Canonical.TopologicalBraiding.pauliXZ_noncommute_R

/-- Same statement in the trace-free doubled complex chart: monodromy and parity do not commute. -/
theorem local_ep_nonabelian_transport_complex :
    (InfoGeometry.Canonical.TopologicalBraiding.pauliXc *
        InfoGeometry.Canonical.TopologicalBraiding.pauliZc) ≠
      (InfoGeometry.Canonical.TopologicalBraiding.pauliZc *
        InfoGeometry.Canonical.TopologicalBraiding.pauliXc) := by
  simpa using InfoGeometry.Canonical.TopologicalBraiding.pauliXZ_noncommute_C

/-- `epTrajectoryMonodromy` carries only loop-count bookkeeping for a compiler trajectory. -/
def epTrajectoryMonodromy
    {G X V H : Type*}
    [Group G] [MulAction G X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (_C : KMSCompiler G X V) (op : NonHermitianOperator H) (z : ℂ) (n : ℕ) : SignType :=
  epLoopSector op z n

/-- Two-sheeted KMS loop transport is contractible on the EP index. -/
theorem epTrajectoryMonodromy_two_step
    {G X V H : Type*}
    [Group G] [MulAction G X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : KMSCompiler G X V) (op : NonHermitianOperator H) (z : ℂ) (n : ℕ)
    (hep : IsExceptionalPoint H op z) :
    epTrajectoryMonodromy (_C := C) op z (n + 2) = epTrajectoryMonodromy (_C := C) op z n := by
  calc
    epTrajectoryMonodromy (_C := C) op z (n + 2) = epLoopSector op z (n + 2) := rfl
    _ = epLoopSector op z n := epLoopSector_two_step op z n hep
    _ = epTrajectoryMonodromy (_C := C) op z n := rfl

/-- One-step trajectory sector shift is one `Z₂` sheet action in EP branch. -/
theorem epTrajectoryMonodromy_one_step
    {G X V H : Type*}
    [Group G] [MulAction G X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : KMSCompiler G X V) (op : NonHermitianOperator H) (z : ℂ)
    (hep : IsExceptionalPoint H op z) :
    epSheetMonodromy (epTrajectoryMonodromy (_C := C) op z 1) =
      epTrajectoryMonodromy (_C := C) op z 0 := by
  calc
    epSheetMonodromy (epTrajectoryMonodromy (_C := C) op z 1)
        = epSheetMonodromy (epLoopSector op z 1) := rfl
    _ = epSheetMonodromy (-epLoopSector op z 0) := by
      rw [epLoopSector_succ op z 0 hep]
    _ = epLoopSector op z 0 := by
      simp [epSheetMonodromy]
    _ = epTrajectoryMonodromy (_C := C) op z 0 := rfl

/-- Local plus/minus cycle class as a function of parity (for explicit sheet bookkeeping). -/
def ep_parity_sector {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (n : ℕ) : SignType :=
  if IsExceptionalPoint H op z then if Even n then (- (1 : SignType)) else (1 : SignType) else (1 : SignType)

/-- Even/odd parity reduction for the trajectory sector index. -/
theorem ep_parity_sector_eq_epLoopSector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (n : ℕ) :
    ep_parity_sector op z n = epLoopSector op z n := by
  by_cases hep : IsExceptionalPoint H op z
  · by_cases hn : Even n
    · rcases hn with ⟨k, rfl⟩
      simp [ep_parity_sector, epLoopSector, hep]
    · have hodd : Odd n := Nat.not_even_iff_odd.mp hn
      rcases hodd with ⟨k, hk⟩
      have hpow : ((- (1 : SignType)) ^ (2 * k + 1) : SignType) = (- (1 : SignType)) := by
        calc
          ((- (1 : SignType)) ^ (2 * k + 1) : SignType)
              = ((- (1 : SignType)) ^ (2 * k)) * (- (1 : SignType)) := by
                simp [pow_succ]
          _ = (1 : SignType) * (- (1 : SignType)) := by simp [pow_mul]
          _ = (- (1 : SignType)) := one_mul (- (1 : SignType))
      simp [ep_parity_sector, epLoopSector, hep, hk, hpow]
  · simp [ep_parity_sector, epLoopSector, hep]

/-- Summary chain for the exceptional-point monodromy layer. -/
theorem exceptionalPointMonodromy_synthesis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (n : ℕ) (A : M2R) :
    (IsExceptionalPoint H op z → exceptionalLoopIndex op z = (-1 : SignType)) ∧
    (¬ IsExceptionalPoint H op z → exceptionalLoopIndex op z = (1 : SignType)) ∧
    (IsExceptionalPoint H op z → (- exceptionalLoopIndex op z) = (1 : SignType)) ∧
    (epSheetMonodromy (epSheetMonodromy (1 : SignType)) = (1 : SignType)) ∧
    (IsExceptionalPoint H op z → epLoopSector op z 0 = exceptionalLoopIndex op z) ∧
    (IsExceptionalPoint H op z → epLoopSector op z (n + 2) = epLoopSector op z n) ∧
    (¬ IsExceptionalPoint H op z → epLoopSector op z n = (1 : SignType)) ∧
    (superGrade (epMatrixMonodromy A) = epSheetMonodromy (superGrade A)) := by
  constructor
  · intro hep
    exact exceptionalLoopIndex_eq_neg_one op z hep
  constructor
  · intro hno
    exact exceptionalLoopIndex_eq_one op z hno
  constructor
  · intro hep
    exact exceptionalLoopIndex_monodromy op z hep
  constructor
  · simp [epSheetMonodromy]
  constructor
  · intro hep
    exact epLoopSector_zero op z
  constructor
  · intro hep
    exact epLoopSector_two_step op z n hep
  constructor
  · intro hno
    exact epLoopSector_non_exceptional op z hno n
  · exact epMatrixMonodromy_grade A

end InfoGeometry.GrandUnification.ExceptionalPoints
