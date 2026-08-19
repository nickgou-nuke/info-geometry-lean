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

variable (two_n_inv : R)
variable (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1)

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
def alpha (S : State) : R :=
  totalTrace S * two_n_inv

/-- The Chiral Inbalance Scalar: β = STr(S) / 2n. -/
def beta (S : State) : R :=
  superTrace S * two_n_inv

/-!
=============================================================================
PART 2: The Three Canonical Projectors
=============================================================================
-/

/-- Volume Projector: π_vol(S) = α(S) • I. -/
def projVol (S : State) : State :=
  (alpha S • (1 : SubMat), alpha S • (1 : SubMat))

/-- Chiral Projector: π_chir(S) = β(S) • Γ. -/
def projChir (S : State) : State :=
  (beta S • (1 : SubMat), -(beta S • (1 : SubMat)))

/-- Pure Shape Projector: π_shape(S) = S - π_vol(S) - π_chir(S). -/
def projShape (S : State) : State :=
  (S.1 - (alpha S + beta S) • (1 : SubMat),
   S.2 - (alpha S - beta S) • (1 : SubMat))

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
theorem alpha_identity :
    alpha (OpIdentity : State) = 1 := by
  dsimp [alpha]
  rw [totalTrace_identity, h_two_n]

@[simp]
theorem beta_identity :
    beta (OpIdentity : State) = 0 := by
  dsimp [beta]
  rw [superTrace_identity, zero_mul]

@[simp]
theorem alpha_gamma :
    alpha (OpGamma : State) = 0 := by
  dsimp [alpha]
  rw [totalTrace_gamma, zero_mul]

@[simp]
theorem beta_gamma :
    beta (OpGamma : State) = 1 := by
  dsimp [beta]
  rw [superTrace_gamma, h_two_n]

/-!
=============================================================================
PART 4: Idempotence of the Projectors
=============================================================================
-/

/-- THEOREM 1: The Volume Projector is Idempotent (π_vol² = π_vol). -/
theorem projVol_idempotent (S : State) :
    projVol (projVol S) = projVol S := by
  dsimp [projVol, alpha, totalTrace]
  simp only [Matrix.trace_smul, Matrix.trace_one]
  <;>
  (try ring_nf at *) <;>
  (try simp_all [h_two_n]) <;>
  (try
    {
      ext <;>
      simp_all [Prod.mk.inj_iff, Matrix.one_apply, Matrix.trace, Finset.sum_const, Finset.card_range]
      <;>
      ring_nf at * <;>
      simp_all [h_two_n]
      <;>
      aesop
    }) <;>
  (try
    {
      simp_all [Prod.mk.inj_iff, Matrix.one_apply, Matrix.trace, Finset.sum_const, Finset.card_range]
      <;>
      ring_nf at * <;>
      simp_all [h_two_n]
      <;>
      aesop
    })
  <;>
  aesop

/-- THEOREM 2: The Chiral Projector is Idempotent (π_chir² = π_chir). -/
theorem projChir_idempotent (S : State) :
    projChir (projChir S) = projChir S := by
  dsimp [projChir, beta, superTrace]
  simp only [Matrix.trace_smul, Matrix.trace_neg, Matrix.trace_one]
  <;>
  (try ring_nf at *) <;>
  (try simp_all [h_two_n]) <;>
  (try
    {
      ext <;>
      simp_all [Prod.mk.inj_iff, Matrix.one_apply, Matrix.trace, Finset.sum_const, Finset.card_range]
      <;>
      ring_nf at * <;>
      simp_all [h_two_n]
      <;>
      aesop
    }) <;>
  (try
    {
      simp_all [Prod.mk.inj_iff, Matrix.one_apply, Matrix.trace, Finset.sum_const, Finset.card_range]
      <;>
      ring_nf at * <;>
      simp_all [h_two_n]
      <;>
      aesop
    })
  <;>
  aesop

/-!
=============================================================================
PART 5: Mutual Orthogonality of the Projectors
=============================================================================
-/

/-- THEOREM 3: Volume and Chirality are strictly Orthogonal: π_vol ∘ π_chir = 0. -/
theorem projVol_projChir_orthogonal (S : State) :
    projVol (projChir S) = (0, 0) := by
  dsimp [projVol, projChir, alpha, totalTrace]
  simp only [Matrix.trace_smul, Matrix.trace_neg, Matrix.trace_one]
  <;>
  (try ring_nf at *) <;>
  (try simp_all [h_two_n]) <;>
  (try
    {
      ext <;>
      simp_all [Prod.mk.inj_iff, Matrix.one_apply, Matrix.trace, Finset.sum_const, Finset.card_range]
      <;>
      ring_nf at * <;>
      simp_all [h_two_n]
      <;>
      aesop
    }) <;>
  (try
    {
      simp_all [Prod.mk.inj_iff, Matrix.one_apply, Matrix.trace, Finset.sum_const, Finset.card_range]
      <;>
      ring_nf at * <;>
      simp_all [h_two_n]
      <;>
      aesop
    })
  <;>
  aesop

/-- THEOREM 4: Chirality and Volume are strictly Orthogonal: π_chir ∘ π_vol = 0. -/
theorem projChir_projVol_orthogonal (S : State) :
    projChir (projVol S) = (0, 0) := by
  dsimp [projVol, projChir, beta, superTrace]
  simp only [Matrix.trace_smul, Matrix.trace_one]
  <;>
  (try ring_nf at *) <;>
  (try simp_all [h_two_n]) <;>
  (try
    {
      ext <;>
      simp_all [Prod.mk.inj_iff, Matrix.one_apply, Matrix.trace, Finset.sum_const, Finset.card_range]
      <;>
      ring_nf at * <;>
      simp_all [h_two_n]
      <;>
      aesop
    }) <;>
  (try
    {
      simp_all [Prod.mk.inj_iff, Matrix.one_apply, Matrix.trace, Finset.sum_const, Finset.card_range]
      <;>
      ring_nf at * <;>
      simp_all [h_two_n]
      <;>
      aesop
    })
  <;>
  aesop

/-!
=============================================================================
PART 6: Completeness (Partition of Unity) and Shape Idempotency
=============================================================================
-/

/-- 
  THEOREM 5: Partition of Unity (Completeness)
  π_vol(S) + π_chir(S) + π_shape(S) = S
-/
theorem trifold_partition_of_unity (S : State) :
    (projVol S).1 + (projChir S).1 + (projShape S).1 = S.1 ∧
    (projVol S).2 + (projChir S).2 + (projShape S).2 = S.2 := by
  dsimp [projVol, projChir, projShape]
  constructor
  · simp only [add_smul]
    abel
  · simp only [sub_smul]
    abel

/-- THEOREM 6: The Pure Shape Projector is Idempotent (π_shape² = π_shape). -/
theorem projShape_idempotent (S : State) :
    projShape (projShape S) = projShape S := by
  dsimp [projShape, alpha, beta, totalTrace, superTrace]
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  <;>
  (try ring_nf at *) <;>
  (try simp_all [h_two_n]) <;>
  (try
    {
      ext <;>
      simp_all [Prod.mk.inj_iff, Matrix.one_apply, Matrix.trace, Finset.sum_const, Finset.card_range]
      <;>
      ring_nf at * <;>
      simp_all [h_two_n]
      <;>
      aesop
    }) <;>
  (try
    {
      simp_all [Prod.mk.inj_iff, Matrix.one_apply, Matrix.trace, Finset.sum_const, Finset.card_range]
      <;>
      ring_nf at * <;>
      simp_all [h_two_n]
      <;>
      aesop
    })
  <;>
  aesop

/-!
=============================================================================
PART 7: Exact Characterization of the Pure Shape Sector
=============================================================================
-/

/-- 
  THEOREM 7: An operator is pure shape if and only if its Trace and Supertrace vanish.
  S ∈ im(π_shape) ↔ Tr(S) = 0 ∧ STr(S) = 0
-/
theorem mem_shape_iff_traces_zero (S : State) :
    projShape S = S ↔ totalTrace S = 0 ∧ superTrace S = 0 := by
  constructor
  · intro h
    have h_a : alpha S = 0 := by
      have h1 := congr_arg Prod.fst h
      dsimp [projShape] at h1
      have h_tr := congr_arg Matrix.trace h1
      simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at h_tr
      have h_sub_zero : (alpha S + beta S) * (Fintype.card ι : R) = 0 := by
        linear_combination -h_tr
      have h2 := congr_arg Prod.snd h
      dsimp [projShape] at h2
      have h_tr2 := congr_arg Matrix.trace h2
      simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at h_tr2
      have h_sub_zero2 : (alpha S - beta S) * (Fintype.card ι : R) = 0 := by
        linear_combination -h_tr2
      have h_add_zeros : (2 * alpha S) * (Fintype.card ι : R) = 0 := by
        calc
          (2 * alpha S) * (Fintype.card ι : R)
            = (alpha S + beta S) * (Fintype.card ι : R) +
              (alpha S - beta S) * (Fintype.card ι : R) := by ring
          _ = 0 + 0 := by rw [h_sub_zero, h_sub_zero2]
          _ = 0 := add_zero 0
      calc
        alpha S = alpha S * 1 := (mul_one (alpha S)).symm
        _ = alpha S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by rw [h_two_n]
        _ = ((2 * alpha S) * (Fintype.card ι : R)) * two_n_inv := by ring
        _ = 0 * two_n_inv := by rw [h_add_zeros]
        _ = 0 := zero_mul two_n_inv
    have h_b : beta S = 0 := by
      have h1 := congr_arg Prod.fst h
      dsimp [projShape] at h1
      have h_tr := congr_arg Matrix.trace h1
      simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at h_tr
      have h_sub_zero : (alpha S + beta S) * (Fintype.card ι : R) = 0 := by
        linear_combination -h_tr
      rw [h_a, zero_add] at h_sub_zero
      calc
        beta S = beta S * 1 := (mul_one (beta S)).symm
        _ = beta S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by rw [h_two_n]
        _ = 2 * (beta S * (Fintype.card ι : R)) * two_n_inv := by ring
        _ = 2 * 0 * two_n_inv := by rw [h_sub_zero]
        _ = 0 := by ring
    have h_tr_tot : totalTrace S = 0 := by
      calc
        totalTrace S = totalTrace S * 1 := (mul_one (totalTrace S)).symm
        _ = totalTrace S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by rw [h_two_n]
        _ = (totalTrace S * two_n_inv) * (2 * (Fintype.card ι : R)) := by ring
        _ = 0 * (2 * (Fintype.card ι : R)) := by rw [h_a]
        _ = 0 := zero_mul _
    have h_str_tot : superTrace S = 0 := by
      calc
        superTrace S = superTrace S * 1 := (mul_one (superTrace S)).symm
        _ = superTrace S * ((2 * (Fintype.card ι : R)) * two_n_inv) := by rw [h_two_n]
        _ = (superTrace S * two_n_inv) * (2 * (Fintype.card ι : R)) := by ring
        _ = 0 * (2 * (Fintype.card ι : R)) := by rw [h_b]
        _ = 0 := zero_mul _
    exact ⟨h_tr_tot, h_str_tot⟩
  · rintro ⟨h_tr, h_str⟩
    have h_a : alpha S = 0 := by
      calc
        alpha S = totalTrace S * two_n_inv := rfl
        _ = 0 * two_n_inv := by rw [h_tr]
        _ = 0 := by simp
    have h_b : beta S = 0 := by
      calc
        beta S = superTrace S * two_n_inv := rfl
        _ = 0 * two_n_inv := by rw [h_str]
        _ = 0 := by simp
    dsimp [projShape, alpha, beta] at *
    <;>
    (try simp_all [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]) <;>
    (try
      {
        ext <;>
        simp_all [Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
        <;>
        ring_nf at * <;>
        aesop
      }) <;>
    (try
      {
        constructor <;>
        simp_all [Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
        <;>
        ring_nf at * <;>
        aesop
      })

end InfoGeometry.Modular.Classification

end noncomputable section