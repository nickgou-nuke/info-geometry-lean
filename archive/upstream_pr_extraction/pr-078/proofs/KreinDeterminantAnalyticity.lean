import Mathlib

noncomputable section

namespace InfoGeometry.Quantum.KreinDeterminantAnalyticity

open Matrix Complex Finset

/-- Determinant trichotomy used in the Krein-analytic picture. -/
inductive DeterminantSector
  | boson    -- det = 1
  | fermion  -- det = -1
  | pole     -- det = 0
  | other    -- all remaining real values
  deriving DecidableEq, Repr

/-- Local transfer operator in doubled real dimension. -/
abbrev TransferMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- Analyticity is encoded algebraically: unit determinant (`SL(2,ℝ)`). -/
def IsAnalyticFlow {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : Prop :=
  M.det = 1

def IsAnalyticFlow2 (M : TransferMatrix) : Prop :=
  IsAnalyticFlow M

def IsPoleFlow {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : Prop :=
  M.det = 0

def IsFermionFlow {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : Prop :=
  M.det = -1

/-- Determinant as a multiplicative monoid homomorphism on matrices. -/
def detMonoidHom : Matrix (Fin 2) (Fin 2) ℝ →* ℝ where
  toFun := Matrix.det
  map_one' := by simp
  map_mul' := by intro A B; simp [Matrix.det_mul]

@[simp] theorem detMonoidHom_apply (A : Matrix (Fin 2) (Fin 2) ℝ) :
    detMonoidHom A = A.det := rfl

/-- Sector classifier from an explicit determinant value. -/
def determinantSector {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : DeterminantSector :=
  if _h1 : M.det = 1 then
    DeterminantSector.boson
  else if _h_1 : M.det = -1 then
    DeterminantSector.fermion
  else if _h0 : M.det = 0 then
    DeterminantSector.pole
  else
    DeterminantSector.other

@[simp] theorem determinantSector_boson {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (h : M.det = 1) : determinantSector M = DeterminantSector.boson := by
  unfold determinantSector
  simp [h]

@[simp] theorem determinantSector_fermion {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (h : M.det = -1) : determinantSector M = DeterminantSector.fermion := by
  unfold determinantSector
  have hne : (-1 : ℝ) ≠ 1 := by norm_num
  simp [h, hne]

@[simp] theorem determinantSector_pole {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (h : M.det = 0) : determinantSector M = DeterminantSector.pole := by
  unfold determinantSector
  simp [h]

/-- Closure of analyticity under matrix multiplication. -/
theorem analytic_mul {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : IsAnalyticFlow A) (hB : IsAnalyticFlow B) :
    IsAnalyticFlow (A * B) := by
  unfold IsAnalyticFlow
  calc
    (A * B).det = A.det * B.det := by simp [Matrix.det_mul]
    _ = 1 * 1 := by rw [hA, hB]
    _ = 1 := by norm_num

/-- Closure of analyticity under tensor (Kronecker) assembly.
    For `2×2` local blocks this sends `SL(2,ℝ) × SL(2,ℝ)` into `SL(4,ℝ)` in
    this specific determinant convention.
-/
def tensorFlow (A B : TransferMatrix) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.kroneckerMap (fun x y : ℝ => x * y) A B

lemma tensorFlow_det {A B : TransferMatrix} :
    (tensorFlow A B).det = A.det ^ 2 * B.det ^ 2 := by
  unfold tensorFlow
  simpa [Fintype.card_fin] using (Matrix.det_kronecker A B)

lemma tensorFlow_analytic (A B : TransferMatrix)
    (hA : IsAnalyticFlow A) (hB : IsAnalyticFlow B) :
    IsAnalyticFlow (tensorFlow A B) := by
  have hdet : (tensorFlow A B).det = A.det ^ 2 * B.det ^ 2 := tensorFlow_det (A := A) (B := B)
  change (tensorFlow A B).det = 1
  rw [hdet, hA, hB]
  norm_num

/-- A concrete trace-zero generator in the doubled basis and its analytic flow.
    This is the real matrix incarnation of a `sl(2,ℝ)` logarithmic step.
-/
def traceZeroGenerator (θ : ℝ) : TransferMatrix :=
  !![θ, 0; 0, -θ]

/-- Its exact transfer `diag(e^θ,e^{-θ})`; this is still unit determinant. -/
def hyperbolicFlow (θ : ℝ) : TransferMatrix :=
  !![Real.exp θ, 0; 0, Real.exp (-θ)]

lemma traceZeroGenerator_trace (θ : ℝ) :
    (traceZeroGenerator θ).trace = 0 := by
  simp [traceZeroGenerator, Matrix.trace_fin_two]

lemma hyperbolicFlow_analytic (θ : ℝ) : IsAnalyticFlow2 (hyperbolicFlow θ) := by
  unfold IsAnalyticFlow2
  unfold IsAnalyticFlow hyperbolicFlow
  have hmul : Real.exp θ * Real.exp (-θ) = 1 := by
    rw [← Real.exp_add]
    simp
  simp [Matrix.det_fin_two, hmul]

/-- Logarithmic volume (Jacobi-Liouville) witness on the concrete family above:
    `diag(e^θ,e^{-θ})` has determinant one, so its determinant-log is zero.
    This replaces classical complex analyticity in the real doubled setting.
-/
def logVolume (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := Real.log (M.det)

lemma logVolume_hyperbolic (θ : ℝ) : logVolume (hyperbolicFlow θ) = 0 := by
  have hdet : (hyperbolicFlow θ).det = 1 := by
    have hmul : Real.exp θ * Real.exp (-θ) = 1 := by
      rw [← Real.exp_add]
      simp
    simp [hyperbolicFlow, Matrix.det_fin_two, hmul]
  simp [logVolume, hdet]

/-- Parafermionic phase datum: a unit q with a prescribed order. -/
structure ParafermionPhase (N : ℕ) where
  q : ℂ
  unit_order : q ^ N = 1

/-- Closed under multiplication of same order data. -/
def ParafermionPhase.mul {N : ℕ} (a b : ParafermionPhase N) : ParafermionPhase N where
  q := a.q * b.q
  unit_order := by
    calc
      (a.q * b.q) ^ N = (a.q ^ N) * (b.q ^ N) := by simp [mul_pow]
      _ = 1 * 1 := by rw [a.unit_order, b.unit_order]
      _ = 1 := by ring

/-- Main synthesis for this analytic module: determinant is monoid homomorphic,
    the analytic sectors are multiplicative, and parafermionic phases compose.
-/
theorem krein_determinant_analyticity_synthesis :
    (∀ A B : TransferMatrix, IsAnalyticFlow2 A → IsAnalyticFlow2 B → IsAnalyticFlow (A * B)) ∧
    (∀ A B : TransferMatrix, IsAnalyticFlow2 A → IsAnalyticFlow2 B →
      IsAnalyticFlow (tensorFlow A B)) ∧
    (∀ N : ℕ, ∀ a b : ParafermionPhase N,
      (a.q * b.q) ^ N = 1) := by
  constructor
  · intro A B hA hB
    exact analytic_mul A B hA hB
  · constructor
    · intro A B hA hB
      exact tensorFlow_analytic A B hA hB
    · intro N a b
      simpa [ParafermionPhase.mul] using (ParafermionPhase.mul a b).unit_order

end InfoGeometry.Quantum.KreinDeterminantAnalyticity
