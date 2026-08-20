import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Trifold State-Space Classification: Volume, Chirality, and Shape

This module formalizes the exact projector algebra for the trifold decomposition:
  StateSpace ≅ Volume ⊕ Chirality ⊕ Shape

Proving idempotency, mutual orthogonality, partition of unity, and exact kernel
characterization with zero `sorry`s in native Mathlib.
-/

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.Modular.Classification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "SubMat" => Matrix ι ι R
local notation "State" => SubMat × SubMat

/-!
=============================================================================
PART 1: Observables on the Doubled State Space
=============================================================================
-/

/-- The Identity Operator: I = (Iₙ, Iₙ). -/
def OpIdentity : State :=
  ((1 : SubMat), (1 : SubMat))

/-- The Involutive Grading Operator: Γ = (Iₙ, -Iₙ). -/
def OpGamma : State :=
  ((1 : SubMat), (-(1 : SubMat)))

/-- Total Trace (Ordinary Volume): Tr(A, B) = Tr(A) + Tr(B). -/
def totalTrace (S : State) : R :=
  Matrix.trace S.1 + Matrix.trace S.2

/-- Supertrace (Chiral Inbalance): STr(A, B) = Tr(A) - Tr(B). -/
def superTrace (S : State) : R :=
  Matrix.trace S.1 - Matrix.trace S.2

/-- The Common Volume Scalar: α = Tr(S) / 2n. -/
def alpha (two_n_inv : R) (S : State) : R :=
  totalTrace S * two_n_inv

/-- The Chiral Inbalance Scalar: β = STr(S) / 2n. -/
def beta (two_n_inv : R) (S : State) : R :=
  superTrace S * two_n_inv

/-!
=============================================================================
PART 2: The Three Canonical Projectors
=============================================================================
-/

/-- Volume Projector: π_vol(S) = α(S) • I. -/
def projVol (two_n_inv : R) (S : State) : State :=
  (alpha two_n_inv S • (1 : SubMat), alpha two_n_inv S • (1 : SubMat))

/-- Chiral Projector: π_chir(S) = β(S) • Γ. -/
def projChir (two_n_inv : R) (S : State) : State :=
  (beta two_n_inv S • (1 : SubMat), -(beta two_n_inv S • (1 : SubMat)))

/-- Pure Shape Projector: π_shape(S) = S - π_vol(S) - π_chir(S). -/
def projShape (two_n_inv : R) (S : State) : State :=
  (S.1 - (alpha two_n_inv S + beta two_n_inv S) • (1 : SubMat),
   S.2 - (alpha two_n_inv S - beta two_n_inv S) • (1 : SubMat))

/-!
=============================================================================
PART 3: Trace and Supertrace Evaluation on the Basis Elements
=============================================================================
-/

@[simp]
theorem totalTrace_identity :
    totalTrace (OpIdentity : State) = (2 * (Fintype.card ι : R)) := by
  dsimp [totalTrace, OpIdentity]
  simp only [Matrix.trace_one]
  ring

@[simp]
theorem superTrace_identity :
    superTrace (OpIdentity : State) = 0 := by
  dsimp [superTrace, OpIdentity]
  simp only [Matrix.trace_one, sub_self]

@[simp]
theorem totalTrace_gamma :
    totalTrace (OpGamma : State) = 0 := by
  dsimp [totalTrace, OpGamma]
  simp only [Matrix.trace_one, Matrix.trace_neg]
  ring

@[simp]
theorem superTrace_gamma :
    superTrace (OpGamma : State) = (2 * (Fintype.card ι : R)) := by
  dsimp [superTrace, OpGamma]
  simp only [Matrix.trace_one, Matrix.trace_neg]
  ring

@[simp]
theorem alpha_identity (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) :
    alpha two_n_inv (OpIdentity : State) = 1 := by
  dsimp [alpha]
  rw [totalTrace_identity, h_two_n]

@[simp]
theorem beta_identity (two_n_inv : R) :
    beta two_n_inv (OpIdentity : State) = 0 := by
  dsimp [beta]
  rw [superTrace_identity, zero_mul]

@[simp]
theorem alpha_gamma (two_n_inv : R) :
    alpha two_n_inv (OpGamma : State) = 0 := by
  dsimp [alpha]
  rw [totalTrace_gamma, zero_mul]

@[simp]
theorem beta_gamma (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) :
    beta two_n_inv (OpGamma : State) = 1 := by
  dsimp [beta]
  rw [superTrace_gamma, h_two_n]

/-!
=============================================================================
PART 4: Idempotence of the Projectors
=============================================================================
-/

theorem alpha_projVol (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (S : State) :
    alpha two_n_inv (projVol two_n_inv S) = alpha two_n_inv S := by
  dsimp [alpha, projVol, totalTrace]
  simp only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  calc (alpha two_n_inv S * (Fintype.card ι : R) + alpha two_n_inv S * (Fintype.card ι : R)) * two_n_inv
    _ = alpha two_n_inv S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by ring
    _ = alpha two_n_inv S * 1 := by rw [h_two_n]
    _ = alpha two_n_inv S := mul_one (alpha two_n_inv S)

/-- THEOREM 1: The Volume Projector is Idempotent (π_vol² = π_vol). -/
theorem projVol_idempotent (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (S : State) :
    projVol two_n_inv (projVol two_n_inv S) = projVol two_n_inv S := by
  have h := alpha_projVol two_n_inv h_two_n S
  dsimp [projVol] at *
  rw [h]

theorem beta_projChir (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (S : State) :
    beta two_n_inv (projChir two_n_inv S) = beta two_n_inv S := by
  dsimp [beta, projChir, superTrace]
  simp only [Matrix.trace_smul, Matrix.trace_neg, Matrix.trace_one, smul_eq_mul]
  calc (beta two_n_inv S * (Fintype.card ι : R) - -(beta two_n_inv S * (Fintype.card ι : R))) * two_n_inv
    _ = beta two_n_inv S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by ring
    _ = beta two_n_inv S * 1 := by rw [h_two_n]
    _ = beta two_n_inv S := mul_one (beta two_n_inv S)

/-- THEOREM 2: The Chiral Projector is Idempotent (π_chir² = π_chir). -/
theorem projChir_idempotent (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (S : State) :
    projChir two_n_inv (projChir two_n_inv S) = projChir two_n_inv S := by
  have h := beta_projChir two_n_inv h_two_n S
  dsimp [projChir] at *
  rw [h]

/-!
=============================================================================
PART 5: Mutual Orthogonality of the Projectors
=============================================================================
-/

theorem alpha_projChir (two_n_inv : R) (S : State) : alpha two_n_inv (projChir two_n_inv S) = 0 := by
  dsimp [alpha, projChir, totalTrace]
  simp only [Matrix.trace_smul, Matrix.trace_neg, Matrix.trace_one, smul_eq_mul]
  calc (beta two_n_inv S * (Fintype.card ι : R) + -(beta two_n_inv S * (Fintype.card ι : R))) * two_n_inv
    _ = 0 * two_n_inv := by ring
    _ = 0 := zero_mul _

/-- THEOREM 3: Volume and Chirality are strictly Orthogonal: π_vol ∘ π_chir = 0. -/
theorem projVol_projChir_orthogonal (two_n_inv : R) (S : State) :
    projVol two_n_inv (projChir two_n_inv S) = (0, 0) := by
  have h := alpha_projChir two_n_inv S
  dsimp [projVol] at *
  rw [h]
  simp

/-- Alias: projVol_projChir_ortho -/
theorem projVol_projChir_ortho (two_n_inv : R) (S : State) :
    projVol two_n_inv (projChir two_n_inv S) = (0, 0) :=
  projVol_projChir_orthogonal two_n_inv S

theorem beta_projVol (two_n_inv : R) (S : State) : beta two_n_inv (projVol two_n_inv S) = 0 := by
  dsimp [beta, projVol, superTrace]
  simp only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  calc (alpha two_n_inv S * (Fintype.card ι : R) - alpha two_n_inv S * (Fintype.card ι : R)) * two_n_inv
    _ = 0 * two_n_inv := by ring
    _ = 0 := zero_mul _

/-- THEOREM 4: Chirality and Volume are strictly Orthogonal: π_chir ∘ π_vol = 0. -/
theorem projChir_projVol_orthogonal (two_n_inv : R) (S : State) :
    projChir two_n_inv (projVol two_n_inv S) = (0, 0) := by
  have h := beta_projVol two_n_inv S
  dsimp [projChir] at *
  rw [h]
  simp

/-!
=============================================================================
PART 6: Completeness (Partition of Unity) and Shape Idempotency
=============================================================================
-/

/-- THEOREM 5: Partition of Unity (Completeness)
  π_vol(S) + π_chir(S) + π_shape(S) = S -/
theorem trifold_partition_of_unity (two_n_inv : R) (S : State) :
    (projVol two_n_inv S).1 + (projChir two_n_inv S).1 + (projShape two_n_inv S).1 = S.1 ∧
    (projVol two_n_inv S).2 + (projChir two_n_inv S).2 + (projShape two_n_inv S).2 = S.2 := by
  dsimp [projVol, projChir, projShape]
  constructor
  · simp only [add_smul]
    abel
  · simp only [sub_smul]
    abel

/-- Alias: proj_partition_of_unity -/
theorem proj_partition_of_unity (two_n_inv : R) (S : State) :
    (projVol two_n_inv S).1 + (projChir two_n_inv S).1 + (projShape two_n_inv S).1 = S.1 ∧
    (projVol two_n_inv S).2 + (projChir two_n_inv S).2 + (projShape two_n_inv S).2 = S.2 :=
  trifold_partition_of_unity two_n_inv S

theorem alpha_projShape (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (S : State) :
    alpha two_n_inv (projShape two_n_inv S) = 0 := by
  dsimp [alpha, projShape, totalTrace]
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  calc ((Matrix.trace S.1 - (alpha two_n_inv S + beta two_n_inv S) * (Fintype.card ι : R)) +
        (Matrix.trace S.2 - (alpha two_n_inv S - beta two_n_inv S) * (Fintype.card ι : R))) * two_n_inv
    _ = (totalTrace S - 2 * alpha two_n_inv S * (Fintype.card ι : R)) * two_n_inv := by
      dsimp [totalTrace]; ring
    _ = totalTrace S * two_n_inv - alpha two_n_inv S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by ring
    _ = alpha two_n_inv S - alpha two_n_inv S * 1 := by rw [h_two_n]; rfl
    _ = 0 := by ring

theorem beta_projShape (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (S : State) :
    beta two_n_inv (projShape two_n_inv S) = 0 := by
  dsimp [beta, projShape, superTrace]
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  calc ((Matrix.trace S.1 - (alpha two_n_inv S + beta two_n_inv S) * (Fintype.card ι : R)) -
        (Matrix.trace S.2 - (alpha two_n_inv S - beta two_n_inv S) * (Fintype.card ι : R))) * two_n_inv
    _ = (superTrace S - 2 * beta two_n_inv S * (Fintype.card ι : R)) * two_n_inv := by
      dsimp [superTrace]; ring
    _ = superTrace S * two_n_inv - beta two_n_inv S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by ring
    _ = beta two_n_inv S - beta two_n_inv S * 1 := by rw [h_two_n]; rfl
    _ = 0 := by ring

/-- THEOREM 6: The Pure Shape Projector is Idempotent (π_shape² = π_shape). -/
theorem projShape_idempotent (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (S : State) :
    projShape two_n_inv (projShape two_n_inv S) = projShape two_n_inv S := by
  have ha := alpha_projShape two_n_inv h_two_n S
  have hb := beta_projShape two_n_inv h_two_n S
  dsimp [projShape] at *
  rw [ha, hb]
  simp

/-!
=============================================================================
PART 7: Exact Characterization of the Pure Shape Sector
=============================================================================
-/

/-- 
  THEOREM 7: An operator is pure shape if and only if its Trace and Supertrace vanish.
  S ∈ im(π_shape) ↔ Tr(S) = 0 ∧ STr(S) = 0
-/
theorem mem_shape_iff_traces_zero (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (S : State) :
    projShape two_n_inv S = S ↔ totalTrace S = 0 ∧ superTrace S = 0 := by
  constructor
  · intro h
    have h1 := congr_arg Prod.fst h
    have h2 := congr_arg Prod.snd h
    dsimp [projShape] at h1 h2
    have h_sub1 : (alpha two_n_inv S + beta two_n_inv S) • (1 : SubMat) = 0 := by
      calc (alpha two_n_inv S + beta two_n_inv S) • (1 : SubMat)
        = S.1 - (S.1 - (alpha two_n_inv S + beta two_n_inv S) • 1) := by abel
      _ = S.1 - S.1 := by rw [h1]
      _ = 0 := by abel
    have h_sub2 : (alpha two_n_inv S - beta two_n_inv S) • (1 : SubMat) = 0 := by
      calc (alpha two_n_inv S - beta two_n_inv S) • (1 : SubMat)
        = S.2 - (S.2 - (alpha two_n_inv S - beta two_n_inv S) • 1) := by abel
      _ = S.2 - S.2 := by rw [h2]
      _ = 0 := by abel
    have h_tr1 := congr_arg Matrix.trace h_sub1
    have h_tr2 := congr_arg Matrix.trace h_sub2
    simp only [Matrix.trace_smul, Matrix.trace_one, Matrix.trace_zero, smul_eq_mul] at h_tr1 h_tr2
    have h_a_zero : 2 * alpha two_n_inv S * (Fintype.card ι : R) = 0 := by
      calc 2 * alpha two_n_inv S * (Fintype.card ι : R)
        = (alpha two_n_inv S + beta two_n_inv S) * (Fintype.card ι : R) +
          (alpha two_n_inv S - beta two_n_inv S) * (Fintype.card ι : R) := by ring
      _ = 0 + 0 := by rw [h_tr1, h_tr2]
      _ = 0 := by ring
    have h_b_zero : 2 * beta two_n_inv S * (Fintype.card ι : R) = 0 := by
      calc 2 * beta two_n_inv S * (Fintype.card ι : R)
        = (alpha two_n_inv S + beta two_n_inv S) * (Fintype.card ι : R) -
          (alpha two_n_inv S - beta two_n_inv S) * (Fintype.card ι : R) := by ring
      _ = 0 - 0 := by rw [h_tr1, h_tr2]
      _ = 0 := by ring
    have h_a : alpha two_n_inv S = 0 := by
      calc alpha two_n_inv S = alpha two_n_inv S * 1 := (mul_one (alpha two_n_inv S)).symm
      _ = alpha two_n_inv S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by rw [h_two_n]
      _ = (2 * alpha two_n_inv S * (Fintype.card ι : R)) * two_n_inv := by ring
      _ = 0 * two_n_inv := by rw [h_a_zero]
      _ = 0 := by ring
    have h_b : beta two_n_inv S = 0 := by
      calc beta two_n_inv S = beta two_n_inv S * 1 := (mul_one (beta two_n_inv S)).symm
      _ = beta two_n_inv S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by rw [h_two_n]
      _ = (2 * beta two_n_inv S * (Fintype.card ι : R)) * two_n_inv := by ring
      _ = 0 * two_n_inv := by rw [h_b_zero]
      _ = 0 := by ring
    have h_tr : totalTrace S = 0 := by
      calc totalTrace S = totalTrace S * 1 := (mul_one (totalTrace S)).symm
      _ = totalTrace S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by rw [h_two_n]
      _ = (totalTrace S * two_n_inv) * (2 * (Fintype.card ι : R)) := by ring
      _ = alpha two_n_inv S * (2 * (Fintype.card ι : R)) := rfl
      _ = 0 * (2 * (Fintype.card ι : R)) := by rw [h_a]
      _ = 0 := by ring
    have h_str : superTrace S = 0 := by
      calc superTrace S = superTrace S * 1 := (mul_one (superTrace S)).symm
      _ = superTrace S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by rw [h_two_n]
      _ = (superTrace S * two_n_inv) * (2 * (Fintype.card ι : R)) := by ring
      _ = beta two_n_inv S * (2 * (Fintype.card ι : R)) := rfl
      _ = 0 * (2 * (Fintype.card ι : R)) := by rw [h_b]
      _ = 0 := by ring
    exact ⟨h_tr, h_str⟩
  · rintro ⟨h_tr, h_str⟩
    have h_a : alpha two_n_inv S = 0 := by
      dsimp [alpha]
      rw [h_tr, zero_mul]
    have h_b : beta two_n_inv S = 0 := by
      dsimp [beta]
      rw [h_str, zero_mul]
    dsimp [projShape]
    rw [h_a, h_b]
    simp

/-- Alias: projShape_fixed_iff -/
theorem projShape_fixed_iff (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (S : State) :
    projShape two_n_inv S = S ↔ totalTrace S = 0 ∧ superTrace S = 0 :=
  mem_shape_iff_traces_zero two_n_inv h_two_n S

/-- THEOREM 8: The pure shape projector outputs traceless and supertraceless elements. -/
theorem projShape_traceless (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (S : State) :
    totalTrace (projShape two_n_inv S) = 0 ∧ superTrace (projShape two_n_inv S) = 0 := by
  have ha := alpha_projShape two_n_inv h_two_n S
  have hb := beta_projShape two_n_inv h_two_n S
  have h_tr : totalTrace (projShape two_n_inv S) = 0 := by
    calc totalTrace (projShape two_n_inv S) = totalTrace (projShape two_n_inv S) * 1 := (mul_one _).symm
    _ = totalTrace (projShape two_n_inv S) * ((2 * (Fintype.card ι : R)) * two_n_inv) := by rw [h_two_n]
    _ = (totalTrace (projShape two_n_inv S) * two_n_inv) * (2 * (Fintype.card ι : R)) := by ring
    _ = alpha two_n_inv (projShape two_n_inv S) * (2 * (Fintype.card ι : R)) := rfl
    _ = 0 * (2 * (Fintype.card ι : R)) := by rw [ha]
    _ = 0 := by ring
  have h_str : superTrace (projShape two_n_inv S) = 0 := by
    calc superTrace (projShape two_n_inv S) = superTrace (projShape two_n_inv S) * 1 := (mul_one _).symm
    _ = superTrace (projShape two_n_inv S) * ((2 * (Fintype.card ι : R)) * two_n_inv) := by rw [h_two_n]
    _ = (superTrace (projShape two_n_inv S) * two_n_inv) * (2 * (Fintype.card ι : R)) := by ring
    _ = beta two_n_inv (projShape two_n_inv S) * (2 * (Fintype.card ι : R)) := rfl
    _ = 0 * (2 * (Fintype.card ι : R)) := by rw [hb]
    _ = 0 := by ring
  exact ⟨h_tr, h_str⟩

end InfoGeometry.Modular.Classification
