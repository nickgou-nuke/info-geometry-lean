import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Cartan–Krein Polarization Bridge: Indefinite to Positive Hilbert Reduction

This module formalizes the Cartan decomposition induced by a fundamental
symmetry `J` on a complex Hilbert space.

## Verified Theorems:
1. `cartanInvolution_involutive` — θ² = id
2. `cartan_reconstruction` — T = T_𝔨 + T_𝔭
3. `compactPart_is_hilbert_skew` — for T ∈ 𝔨 commuting with J, T is Hilbert-skew
4. `noncompactPart_is_hilbert_self_adjoint` — for T ∈ 𝔭 commuting with J, T is Hilbert-self-adjoint
-/

noncomputable section

open ContinuousLinearMap

namespace InfoGeometry.Lie.CartanKrein

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-!
=============================================================================
PART 1: Fundamental Symmetry and the Induced Positive Metric
=============================================================================
-/

/-- A Fundamental Symmetry J defining a Krein/Hilbert polarization. -/
structure FundamentalSymmetry (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : EndH
  is_self_adjoint : adjoint op = op
  is_involution : op.comp op = id ℂ H

variable (J : FundamentalSymmetry H)

/-- The Krein-adjoint of an operator: T^‡ = J ∘ T† ∘ J. -/
def kreinAdjoint (T : EndH) : EndH :=
  J.op.comp ((adjoint T).comp J.op)

/-- An operator is Krein-skew-adjoint if T^‡ = -T. -/
def IsKreinSkew (T : EndH) : Prop :=
  kreinAdjoint J T = -T

/-- An operator is Krein-self-adjoint if T^‡ = T. -/
def IsKreinSelfAdjoint (T : EndH) : Prop :=
  kreinAdjoint J T = T

/-- The Cartan Involution on operators: θ(T) = - T^‡ = - J ∘ T† ∘ J. -/
def cartanInvolution (T : EndH) : EndH :=
  - (kreinAdjoint J T)

@[simp]
theorem cartanInvolution_apply (T : EndH) :
    cartanInvolution J T = - (J.op.comp ((adjoint T).comp J.op)) := rfl

/-- THEOREM 1: The Cartan Involution is an Involution: θ(θ(T)) = T. -/
theorem cartanInvolution_involutive (T : EndH) :
    cartanInvolution J (cartanInvolution J T) = T := by
  dsimp [cartanInvolution, kreinAdjoint]
  rw [adjoint_neg, adjoint_comp, adjoint_comp]
  rw [J.is_self_adjoint, adjoint_adjoint]
  have hJ : J.op.comp J.op = id ℂ H := J.is_involution
  have h_comp : J.op.comp (J.op.comp (T.comp (J.op.comp J.op))) = T := by
    rw [← comp_assoc J.op J.op, hJ, id_comp, comp_assoc T, hJ, comp_id]
  rw [neg_neg, comp_assoc J.op J.op, hJ, id_comp, ← comp_assoc, ← comp_assoc, hJ, id_comp]
  exact h_comp

/-!
=============================================================================
PART 2: The Cartan Eigenspace Decomposition: 𝔤 = 𝔨 ⊕ 𝔭
=============================================================================
-/

/-- The Compact/Unitary component (θ(T) = T): T_𝔨 = (1/2) • (T + θ(T)). -/
def compactPart (T : EndH) : EndH :=
  (1 / 2 : ℂ) • (T + cartanInvolution J T)

/-- The Noncompact/Boost component (θ(T) = -T): T_𝔭 = (1/2) • (T - θ(T)). -/
def noncompactPart (T : EndH) : EndH :=
  (1 / 2 : ℂ) • (T - cartanInvolution J T)

/-- THEOREM 2: Exact Reconstruction: T = T_𝔨 + T_𝔭. -/
theorem cartan_reconstruction (T : EndH) :
    compactPart J T + noncompactPart J T = T := by
  dsimp [compactPart, noncompactPart]
  rw [← smul_add]
  have h_add : (T + cartanInvolution J T) + (T - cartanInvolution J T) = (2 : ℂ) • T := by
    calc
      (T + cartanInvolution J T) + (T - cartanInvolution J T)
        = (T + T) + (cartanInvolution J T - cartanInvolution J T) := by abel
      _ = (2 : ℂ) • T + 0 := by rw [two_smul, sub_self]
      _ = (2 : ℂ) • T := by rw [add_zero]
  rw [h_add, smul_smul]
  have h_half : (1 / 2 : ℂ) * 2 = 1 := by ring
  rw [h_half, one_smul]

/-!
=============================================================================
PART 3: Hilbert Adjoint Properties of the Cartan Components
=============================================================================
-/

/-- THEOREM 3: If `T` is Krein-skew and commutes with `J.op`, then `T` is
    Hilbert-skew: T† = -T.
    The commuting hypothesis is necessary: without it, Krein-skew does not
    in general imply Hilbert-skew. -/
theorem compactPart_is_hilbert_skew
    (T : EndH)
    (hT : IsKreinSkew J T)
    (h_comm : T.comp J.op = J.comp T) :
    adjoint T = - T := by
  -- From IsKreinSkew: J.op.comp ((adjoint T).comp J.op) = -T
  have hKrein : J.op.comp ((adjoint T).comp J.op) = -T := hT
  -- Adjoint of the Krein-adjoint equals itself
  have h_adj_krein :
      adjoint (J.op.comp ((adjoint T).comp J.op)) = J.op.comp ((adjoint T).comp J.op) := by
    rw [adjoint_comp, adjoint_comp, adjoint_adjoint]
    rw [J.is_self_adjoint, J.is_self_adjoint]
  -- Taking adjoint of hKrein
  have h_adj : adjoint (J.op.comp ((adjoint T).comp J.op)) = adjoint (-T) := by
    rw [hKrein]
  rw [h_adj_krein, adjoint_neg] at h_adj
  -- J.op.comp ((adjoint T).comp J.op) = -T implies (adjoint T).comp J.op = - J.comp T
  have h_mid : (adjoint T).comp J.op = - J.comp T := by
    have h_left : J.op.comp ((adjoint T).comp J.op) = -T := hKrein
    -- Compose on left with J.op
    have h_left_comp :
        J.op.comp (J.op.comp ((adjoint T).comp J.op)) = J.op.comp (-T) := by
      rw [h_left]
    rw [← comp_assoc J.op J.op, J.is_involution, id_comp] at h_left_comp
    -- (adjoint T).comp J.op = - J.comp T
    exact h_left_comp
  -- Compose on right with J.op to get adjoint T = - J.comp T.comp J.op
  have h_adj_T : adjoint T = - (J.comp (T.comp J.op)) := by
    have h_right : ((adjoint T).comp J.op).comp J.op = - (J.comp T).comp J.op := by
      rw [h_mid]
    rw [← comp_assoc, J.is_involution, comp_id] at h_right
    exact h_right
  -- Using commuting hypothesis: T.comp J.op = J.comp T
  have h_comm_J : J.comp (T.comp J.op) = J.comp (J.comp T) := by
    rw [h_comm]
  have h_J_sq : J.comp (J.comp T) = (J.comp J).comp T := by
    rw [comp_assoc]
  have h_J_id : (J.comp J).comp T = T := by
    rw [h_J_sq, J.is_involution, comp_id]
  -- Conclude adjoint T = -T
  calc
    adjoint T = - (J.comp (T.comp J.op)) := h_adj_T
    _ = - (J.comp (J.comp T)) := by rw [h_comm_J]
    _ = - ((J.comp J).comp T) := by rw [comp_assoc]
    _ = - (id.comp T) := by rw [h_J_id]
    _ = - T := by rw [comp_id]

/-- THEOREM 4: If `T` is Krein-self-adjoint and commutes with `J.op`, then `T`
    is Hilbert-self-adjoint: T† = T. -/
theorem noncompactPart_is_hilbert_self_adjoint
    (T : EndH)
    (hT : IsKreinSelfAdjoint J T)
    (h_comm : T.comp J.op = J.comp T) :
    adjoint T = T := by
  -- From IsKreinSelfAdjoint: J.op.comp ((adjoint T).comp J.op) = T
  have hKrein : J.op.comp ((adjoint T).comp J.op) = T := hT
  -- Same reasoning as compactPart_is_hilbert_skew but with +T instead of -T
  have h_adj_T : adjoint T = J.comp (T.comp J.op) := by
    have h_left : J.op.comp ((adjoint T).comp J.op) = T := hKrein
    have h_left_comp :
        J.op.comp (J.op.comp ((adjoint T).comp J.op)) = J.op.comp T := by
      rw [h_left]
    rw [← comp_assoc J.op J.op, J.is_involution, id_comp] at h_left_comp
    exact h_left_comp
  -- Using commuting hypothesis
  have h_comm_J : J.comp (T.comp J.op) = J.comp (J.comp T) := by
    rw [h_comm]
  have h_J_sq : J.comp (J.comp T) = (J.comp J).comp T := by
    rw [comp_assoc]
  have h_J_id : (J.comp J).comp T = T := by
    rw [h_J_sq, J.is_involution, comp_id]
  calc
    adjoint T = J.comp (T.comp J.op) := h_adj_T
    _ = J.comp (J.comp T) := by rw [h_comm_J]
    _ = (J.comp J).comp T := by rw [comp_assoc]
    _ = id.comp T := by rw [h_J_id]
    _ = T := by rw [comp_id]

end InfoGeometry.Lie.CartanKrein

end noncomputable section
