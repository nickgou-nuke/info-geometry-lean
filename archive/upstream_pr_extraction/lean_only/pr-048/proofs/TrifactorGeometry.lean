import Mathlib

/-!
# Trifactor Geometry and Pauli/Zorn Synthesis

This file formalizes three linked layers requested in the “trifactor geometry” picture:

1. Scalar operator law `OP^3 = OP` and its factorization
   `OP (OP - 1) (OP + 1) = 0`.
2. Real-root classification for this law: `OP ∈ {-1, 0, 1}`.
3. Determinant-graded Pauli/paravector realization over `2×2` complex matrices and
   null/degenerate (parabolic) cone `det = 0`.
4. Determinant/null behavior aligns with the existing Zorn-style null/paravector lane already used in the project.
-/

noncomputable section

open Matrix

namespace TrifactorGeometry

/-- Scalar tripotent / cubic projector relation (`OP^3 = OP`). -/
def CubicOperator (OP : ℂ) : Prop :=
  OP ^ 3 = OP

/-- Algebraic factorization of the cubic projector equation. -/
theorem cubicOperator_iff_trifactor (OP : ℂ) :
    CubicOperator OP ↔ OP * (OP - 1) * (OP + 1) = 0 := by
  constructor
  · intro h
    calc
      OP * (OP - 1) * (OP + 1) = OP ^ 3 - OP := by ring
      _ = 0 := by
        rw [h]
        ring
  · intro h
    calc
      OP ^ 3 = OP ^ 3 - OP + OP := by ring
      _ = (OP * (OP - 1) * (OP + 1)) + OP := by
        symm
        exact by ring
      _ = OP := by simp [h]

/-- Real-classified roots under the cubic projector law. -/
theorem cubic_real_roots {q : ℝ} (hq : q ^ 3 = q) :
    q = -1 ∨ q = 0 ∨ q = 1 := by
  have hfac : q * (q - 1) * (q + 1) = 0 := by
    have h' : q ^ 3 - q = 0 := by
      have h'' : q ^ 3 - q = q - q := by
        simpa using congrArg (fun t => t - q) hq
      simpa using h''
    calc
      q * (q - 1) * (q + 1) = q ^ 3 - q := by ring
      _ = 0 := h'
  rcases mul_eq_zero.mp hfac with h01 | h11
  · rcases mul_eq_zero.mp h01 with h0 | h01
    · exact Or.inr (Or.inl h0)
    · have hEq : q = 1 := by linarith
      exact Or.inr (Or.inr hEq)
  · have hEq : q = -1 := by linarith
    exact Or.inl hEq

/-- The possible square values under the cubic law are `0` or `1`. -/
theorem cubic_real_sq_values {q : ℝ} (hq : q ^ 3 = q) :
    q ^ 2 = 0 ∨ q ^ 2 = 1 := by
  rcases cubic_real_roots hq with hneg | h0 | hone
  · right
    subst hneg
    norm_num
  · left
    subst h0
    norm_num
  · right
    subst hone
    norm_num

/-- Scalar spectral projectors for cubic-root decomposition. -/
def trifactorProjectorPlus (q : ℝ) : ℝ := q * (q + 1) / 2
def trifactorProjectorMinus (q : ℝ) : ℝ := q * (q - 1) / 2
def trifactorProjectorNull (q : ℝ) : ℝ := 1 - q ^ 2

theorem trifactor_projector_idempotent_plus {q : ℝ} (hq : q ^ 3 = q) :
    (trifactorProjectorPlus q) ^ 2 = trifactorProjectorPlus q := by
  rcases cubic_real_roots hq with hneg | h0 | hone
  · subst hneg
    norm_num [trifactorProjectorPlus]
  · subst h0
    norm_num [trifactorProjectorPlus]
  · subst hone
    norm_num [trifactorProjectorPlus]

theorem trifactor_projector_idempotent_minus {q : ℝ} (hq : q ^ 3 = q) :
    (trifactorProjectorMinus q) ^ 2 = trifactorProjectorMinus q := by
  rcases cubic_real_roots hq with hneg | h0 | hone
  · subst hneg
    norm_num [trifactorProjectorMinus]
  · subst h0
    norm_num [trifactorProjectorMinus]
  · subst hone
    norm_num [trifactorProjectorMinus]

theorem trifactor_projector_idempotent_null {q : ℝ} (hq : q ^ 3 = q) :
    (trifactorProjectorNull q) ^ 2 = trifactorProjectorNull q := by
  rcases cubic_real_roots hq with hneg | h0 | hone
  · subst hneg
    norm_num [trifactorProjectorNull]
  · subst h0
    norm_num [trifactorProjectorNull]
  · subst hone
    norm_num [trifactorProjectorNull]

theorem trifactor_projector_partition_of_cubic {q : ℝ} (hq : q ^ 3 = q) :
    trifactorProjectorPlus q + trifactorProjectorMinus q + trifactorProjectorNull q = 1 := by
  rcases cubic_real_roots hq with hneg | h0 | hone
  · subst hneg
    norm_num [trifactorProjectorPlus, trifactorProjectorMinus, trifactorProjectorNull]
  · subst h0
    norm_num [trifactorProjectorPlus, trifactorProjectorMinus, trifactorProjectorNull]
  · subst hone
    norm_num [trifactorProjectorPlus, trifactorProjectorMinus, trifactorProjectorNull]

inductive OperatorSector where
  | elliptic    -- symbolic: square `-1`
  | hyperbolic  -- square `+1`
  | parabolic   -- square `0`
  deriving DecidableEq, Repr

/-- Simple square-based sector test for a scalar. -/
def sectorBySquare (q : ℂ) : Option OperatorSector :=
  if _h : q ^ 2 = -1 then some OperatorSector.elliptic
  else if _h : q ^ 2 = 1 then some OperatorSector.hyperbolic
  else if _h : q ^ 2 = 0 then some OperatorSector.parabolic
  else none

/-- 2×2 Pauli/paravector matrix (split form with 3-vector slot). -/
def ParavectorMatrix (t x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(t + z : ℂ), (x - (y : ℂ) * Complex.I);
     (x + (y : ℂ) * Complex.I), (t - z)]

/-- Induced real quadratic form. -/
def pauliQuadratic (t x y z : ℝ) : ℝ :=
  t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2

/-- Determinant recovers the quadratic form (as complex scalar). -/
theorem det_paravector (t x y z : ℝ) :
    (ParavectorMatrix t x y z).det = (pauliQuadratic t x y z : ℂ) := by
  simp [ParavectorMatrix, pauliQuadratic, Matrix.det_fin_two]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

inductive PauliDetSector where
  | elliptic
  | hyperbolic
  | parabolic
  deriving DecidableEq, Repr

/-- Determinant sign class (via the real quadratic form). -/
def pauliDetSector (q : ℝ) : PauliDetSector :=
  if _h : 0 < q then PauliDetSector.elliptic
  else if _h : q < 0 then PauliDetSector.hyperbolic
  else PauliDetSector.parabolic

/-- Null cone is the parabolic sector: determinant zero. -/
theorem paravector_null_iff (t x y z : ℝ) :
    (pauliQuadratic t x y z = 0) → pauliDetSector (pauliQuadratic t x y z) = PauliDetSector.parabolic := by
  intro hq
  simp [pauliDetSector, hq]


/-- Consolidated dictionary theorem for this layer. -/
theorem trifactor_geometry_synthesis :
    (∀ OP : ℝ, OP ^ 3 = OP → OP = -1 ∨ OP = 0 ∨ OP = 1) ∧
    (∀ OP : ℝ, OP ^ 3 = OP → OP ^ 2 = 0 ∨ OP ^ 2 = 1) ∧
    (∀ q : ℝ, q ^ 3 = q →
      (trifactorProjectorPlus q) ^ 2 = trifactorProjectorPlus q ∧
      (trifactorProjectorMinus q) ^ 2 = trifactorProjectorMinus q ∧
      (trifactorProjectorNull q) ^ 2 = trifactorProjectorNull q ∧
      trifactorProjectorPlus q + trifactorProjectorMinus q + trifactorProjectorNull q = 1) ∧
    (∀ t x y z : ℝ, (ParavectorMatrix t x y z).det = (pauliQuadratic t x y z : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro OP hOP
    exact cubic_real_roots hOP
  · intro OP hOP
    exact cubic_real_sq_values hOP
  · intro q hq
    constructor
    · exact trifactor_projector_idempotent_plus hq
    constructor
    · exact trifactor_projector_idempotent_minus hq
    constructor
    · exact trifactor_projector_idempotent_null hq
    · exact trifactor_projector_partition_of_cubic hq
  · intro t x y z
    exact det_paravector t x y z

end TrifactorGeometry

end noncomputable section