import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Cartan–Krein Polarization Bridge: Indefinite to Positive Hilbert Reduction

This module formalizes the Cartan-Krein polarization bridge for indefinite operator algebras:
1. Fundamental symmetry `J : EndH` with `J† = J` and `J² = I`.
2. The Krein-adjoint operator: `adj_Krein(T) = J ∘ T† ∘ J`.
3. Krein-skewness: `IsKreinSkew(T) ↔ T^‡ = -T`.
4. Cartan Involution on operators: `θ(T) = J ∘ T ∘ J`.
5. Exact decomposition of Krein-skew derivations into compact skew-adjoint (𝔨)
   and noncompact self-adjoint (𝔭) sectors:
     T = T_𝔨 + T_𝔭
   where `adjoint (T_𝔨) = - T_𝔨` (Hilbert skew-adjoint) and `adjoint (T_𝔭) = T_𝔭` (Hilbert self-adjoint).

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open ContinuousLinearMap

namespace InfoGeometry.Lie.CartanKrein

/-- A Fundamental Symmetry J defining a Krein/Hilbert polarization. -/
structure FundamentalSymmetry (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : H →L[ℂ] H
  is_self_adjoint : adjoint op = op
  is_involution : op.comp op = ContinuousLinearMap.id ℂ H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-!
=============================================================================
PART 1: Fundamental Symmetry and the Induced Positive Metric
=============================================================================
-/

/-- The Krein-adjoint of an operator: T^‡ = J ∘ T† ∘ J. -/
def kreinAdjoint (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  J.op.comp ((adjoint T).comp J.op)

/-- An operator is Krein-skew-adjoint if T^‡ = -T. -/
def IsKreinSkew (J : FundamentalSymmetry H) (T : EndH) : Prop :=
  kreinAdjoint J T = -T

/-- The Cartan Involution on operators: θ(T) = J ∘ T ∘ J. -/
def cartanInvolution (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  J.op.comp (T.comp J.op)

@[simp]
theorem cartanInvolution_apply (J : FundamentalSymmetry H) (T : EndH) :
    cartanInvolution J T = J.op.comp (T.comp J.op) := rfl

/-- THEOREM 1: The Cartan Involution is an Involution: θ(θ(T)) = T. -/
theorem cartanInvolution_involutive (J : FundamentalSymmetry H) (T : EndH) :
    cartanInvolution J (cartanInvolution J T) = T := by
  dsimp [cartanInvolution]
  have hJ : J.op.comp J.op = ContinuousLinearMap.id ℂ H := J.is_involution
  calc
    J.op.comp ((J.op.comp (T.comp J.op)).comp J.op)
      = (J.op.comp J.op).comp (T.comp (J.op.comp J.op)) := by
          simp only [comp_assoc]
    _ = (ContinuousLinearMap.id ℂ H).comp (T.comp (ContinuousLinearMap.id ℂ H)) := by rw [hJ]
    _ = T := by simp only [id_comp, comp_id]

/-- The Cartan involution of a Krein-skew operator equals `- adjoint T`. -/
theorem cartanInvolution_eq_neg_adjoint_of_isKreinSkew
    (J : FundamentalSymmetry H) (T : EndH) (hT : IsKreinSkew J T) :
    cartanInvolution J T = - adjoint T := by
  dsimp [IsKreinSkew, kreinAdjoint] at hT
  have hJ : J.op.comp J.op = ContinuousLinearMap.id ℂ H := J.is_involution
  have hT_eq : T = - (J.op.comp ((adjoint T).comp J.op)) := by
    rw [← neg_inj, neg_neg, hT]
  calc
    cartanInvolution J T = J.op.comp (T.comp J.op) := rfl
    _ = J.op.comp ((- (J.op.comp ((adjoint T).comp J.op))).comp J.op) := by
      congr 1
      exact congr_arg (fun X => comp X J.op) hT_eq
    _ = - (J.op.comp ((J.op.comp ((adjoint T).comp J.op)).comp J.op)) := by
      simp only [neg_comp, comp_neg]
    _ = - ((J.op.comp J.op).comp ((adjoint T).comp (J.op.comp J.op))) := by
      simp only [comp_assoc]
    _ = - ((ContinuousLinearMap.id ℂ H).comp ((adjoint T).comp (ContinuousLinearMap.id ℂ H))) := by
      rw [hJ]
    _ = - adjoint T := by
      simp only [id_comp, comp_id]

/-!
=============================================================================
PART 2: The Cartan Eigenspace Decomposition: 𝔤 = 𝔨 ⊕ 𝔭
=============================================================================
-/

/-- The Compact/Unitary component (θ(T) = T): T_𝔨 = (1/2) • (T + θ(T)). -/
def compactPart (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  (1 / 2 : ℂ) • (T + cartanInvolution J T)

/-- The Noncompact/Boost component (θ(T) = -T): T_𝔭 = (1/2) • (T - θ(T)). -/
def noncompactPart (J : FundamentalSymmetry H) (T : EndH) : EndH :=
  (1 / 2 : ℂ) • (T - cartanInvolution J T)

/-- THEOREM 2: Exact Reconstruction: T = T_𝔨 + T_𝔭. -/
theorem cartan_reconstruction (J : FundamentalSymmetry H) (T : EndH) :
    compactPart J T + noncompactPart J T = T := by
  dsimp only [compactPart, noncompactPart]
  rw [← smul_add]
  have h_add : (T + cartanInvolution J T) + (T - cartanInvolution J T) = (2 : ℂ) • T := by
    have h1 : (T + cartanInvolution J T) + (T - cartanInvolution J T) = T + T := by abel
    rw [h1, two_smul]
  rw [h_add, smul_smul]
  have h_half : (1 / 2 : ℂ) * 2 = 1 := by ring
  rw [h_half, one_smul]

/-!
=============================================================================
PART 3: Hilbert Adjoint Properties of the Cartan Components
=============================================================================
-/

theorem adjoint_cartanInvolution (J : FundamentalSymmetry H) (T : EndH) :
    adjoint (cartanInvolution J T) = cartanInvolution J (adjoint T) := by
  dsimp [cartanInvolution]
  simp only [adjoint_comp, J.is_self_adjoint, comp_assoc]

/-- 
  THEOREM 3 (Hilbert Skew-Adjointness of the Compact Part):
  For any Krein-skew operator (such as a split-G₂(2) derivation),
  its compact Cartan component is strictly skew-adjoint on the positive Hilbert space:
    (T_𝔨)† = - T_𝔨
-/
theorem compactPart_is_hilbert_skew
    (J : FundamentalSymmetry H) (T : EndH) (hT : IsKreinSkew J T) :
    adjoint (compactPart J T) = - (compactPart J T) := by
  dsimp only [compactPart]
  rw [adjoint.map_smulₛₗ, map_add adjoint, adjoint_cartanInvolution]
  have h_adj_T : adjoint T = - cartanInvolution J T := by
    have h := cartanInvolution_eq_neg_adjoint_of_isKreinSkew J T hT
    rw [h, neg_neg]
  have h_adj_theta : cartanInvolution J (adjoint T) = - T := by
    calc
      cartanInvolution J (adjoint T) = cartanInvolution J (- cartanInvolution J T) := by rw [h_adj_T]
      _ = - cartanInvolution J (cartanInvolution J T) := by
        dsimp [cartanInvolution]
        simp only [comp_neg, neg_comp]
      _ = - T := by rw [cartanInvolution_involutive]
  have h_half_conj : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    apply Complex.ext <;> simp
  rw [h_adj_theta, h_adj_T, h_half_conj]
  have h_sum : - cartanInvolution J T + - T = - (T + cartanInvolution J T) := by abel
  rw [h_sum, smul_neg]

/-- 
  THEOREM 4 (Hilbert Self-Adjointness of the Noncompact Part):
  For any Krein-skew operator, its noncompact Cartan component is strictly 
  self-adjoint on the positive Hilbert space:
    (T_𝔭)† = T_𝔭
-/
theorem noncompactPart_is_hilbert_self_adjoint
    (J : FundamentalSymmetry H) (T : EndH) (hT : IsKreinSkew J T) :
    adjoint (noncompactPart J T) = noncompactPart J T := by
  dsimp only [noncompactPart]
  rw [adjoint.map_smulₛₗ, map_sub adjoint, adjoint_cartanInvolution]
  have h_adj_T : adjoint T = - cartanInvolution J T := by
    have h := cartanInvolution_eq_neg_adjoint_of_isKreinSkew J T hT
    rw [h, neg_neg]
  have h_adj_theta : cartanInvolution J (adjoint T) = - T := by
    calc
      cartanInvolution J (adjoint T) = cartanInvolution J (- cartanInvolution J T) := by rw [h_adj_T]
      _ = - cartanInvolution J (cartanInvolution J T) := by
        dsimp [cartanInvolution]
        simp only [comp_neg, neg_comp]
      _ = - T := by rw [cartanInvolution_involutive]
  have h_half_conj : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    apply Complex.ext <;> simp
  rw [h_adj_theta, h_adj_T, h_half_conj]
  have h_sub : - cartanInvolution J T - - T = T - cartanInvolution J T := by abel
  rw [h_sub]

/-!
=============================================================================
PART 4: Commutation, Anticommutation, and Eigenspace Invariance
=============================================================================
-/

/-- The compact part commutes with the fundamental symmetry J: J ∘ T_𝔨 = T_𝔨 ∘ J. -/
theorem compactPart_commutes_with_J
    (J : FundamentalSymmetry H) (T : EndH) :
    J.op.comp (compactPart J T) = (compactPart J T).comp J.op := by
  dsimp only [compactPart, cartanInvolution]
  rw [comp_smul, smul_comp]
  congr 1
  rw [comp_add, add_comp]
  have hJ : J.op.comp J.op = ContinuousLinearMap.id ℂ H := J.is_involution
  have h1 : J.op.comp (J.op.comp (T.comp J.op)) = T.comp J.op := by
    calc
      J.op.comp (J.op.comp (T.comp J.op))
        = (J.op.comp J.op).comp (T.comp J.op) := by simp only [comp_assoc]
      _ = (ContinuousLinearMap.id ℂ H).comp (T.comp J.op) := by rw [hJ]
      _ = T.comp J.op := by simp only [id_comp]
  have h2 : (J.op.comp (T.comp J.op)).comp J.op = J.op.comp T := by
    calc
      (J.op.comp (T.comp J.op)).comp J.op
        = J.op.comp (T.comp (J.op.comp J.op)) := by simp only [comp_assoc]
      _ = J.op.comp (T.comp (ContinuousLinearMap.id ℂ H)) := by rw [hJ]
      _ = J.op.comp T := by simp only [comp_id]
  rw [h1, h2, add_comm]

/-- The noncompact part anticommutes with the fundamental symmetry J: J ∘ T_𝔭 = - (T_𝔭 ∘ J). -/
theorem noncompactPart_anticommutes_with_J
    (J : FundamentalSymmetry H) (T : EndH) :
    J.op.comp (noncompactPart J T) = - ((noncompactPart J T).comp J.op) := by
  dsimp only [noncompactPart, cartanInvolution]
  rw [comp_smul, smul_comp, ← smul_neg]
  congr 1
  rw [comp_sub, sub_comp]
  have hJ : J.op.comp J.op = ContinuousLinearMap.id ℂ H := J.is_involution
  have h1 : J.op.comp (J.op.comp (T.comp J.op)) = T.comp J.op := by
    calc
      J.op.comp (J.op.comp (T.comp J.op))
        = (J.op.comp J.op).comp (T.comp J.op) := by simp only [comp_assoc]
      _ = (ContinuousLinearMap.id ℂ H).comp (T.comp J.op) := by rw [hJ]
      _ = T.comp J.op := by simp only [id_comp]
  have h2 : (J.op.comp (T.comp J.op)).comp J.op = J.op.comp T := by
    calc
      (J.op.comp (T.comp J.op)).comp J.op
        = J.op.comp (T.comp (J.op.comp J.op)) := by simp only [comp_assoc]
      _ = J.op.comp (T.comp (ContinuousLinearMap.id ℂ H)) := by rw [hJ]
      _ = J.op.comp T := by simp only [comp_id]
  rw [h1, h2]
  abel

/-- Cartan eigenspace eigenvalue +1: θ(T_𝔨) = T_𝔨. -/
theorem cartanInvolution_compactPart
    (J : FundamentalSymmetry H) (T : EndH) :
    cartanInvolution J (compactPart J T) = compactPart J T := by
  dsimp only [cartanInvolution, compactPart]
  rw [smul_comp, comp_smul]
  congr 1
  rw [add_comp, comp_add]
  have h_inv : J.op.comp ((J.op.comp (T.comp J.op)).comp J.op) = T := cartanInvolution_involutive J T
  rw [h_inv, add_comm]

/-- Cartan eigenspace eigenvalue -1: θ(T_𝔭) = - T_𝔭. -/
theorem cartanInvolution_noncompactPart
    (J : FundamentalSymmetry H) (T : EndH) :
    cartanInvolution J (noncompactPart J T) = - noncompactPart J T := by
  dsimp only [cartanInvolution, noncompactPart]
  rw [smul_comp, comp_smul, ← smul_neg]
  congr 1
  rw [sub_comp, comp_sub]
  have h_inv : J.op.comp ((J.op.comp (T.comp J.op)).comp J.op) = T := cartanInvolution_involutive J T
  rw [h_inv]
  abel

/-- Both compact and noncompact components preserve Krein-skewness. -/
theorem compactPart_isKreinSkew
    (J : FundamentalSymmetry H) (T : EndH) (hT : IsKreinSkew J T) :
    IsKreinSkew J (compactPart J T) := by
  dsimp [IsKreinSkew, kreinAdjoint]
  rw [compactPart_is_hilbert_skew J T hT]
  rw [neg_comp, comp_neg]
  have h_comm := compactPart_commutes_with_J J T
  have hJ : J.op.comp J.op = ContinuousLinearMap.id ℂ H := J.is_involution
  calc
    - (J.op.comp ((compactPart J T).comp J.op))
      = - (J.op.comp (J.op.comp (compactPart J T))) := by rw [← h_comm]
    _ = - ((J.op.comp J.op).comp (compactPart J T)) := by simp only [comp_assoc]
    _ = - ((ContinuousLinearMap.id ℂ H).comp (compactPart J T)) := by rw [hJ]
    _ = - compactPart J T := by simp only [id_comp]

theorem noncompactPart_isKreinSkew
    (J : FundamentalSymmetry H) (T : EndH) (hT : IsKreinSkew J T) :
    IsKreinSkew J (noncompactPart J T) := by
  dsimp [IsKreinSkew, kreinAdjoint]
  rw [noncompactPart_is_hilbert_self_adjoint J T hT]
  have h_anticomm := noncompactPart_anticommutes_with_J J T
  have hJ : J.op.comp J.op = ContinuousLinearMap.id ℂ H := J.is_involution
  have h_swap : (noncompactPart J T).comp J.op = - (J.op.comp (noncompactPart J T)) := by
    have h := congr_arg Neg.neg h_anticomm
    simpa only [neg_neg] using h.symm
  calc
    J.op.comp ((noncompactPart J T).comp J.op)
      = J.op.comp (- (J.op.comp (noncompactPart J T))) := by rw [h_swap]
    _ = - (J.op.comp (J.op.comp (noncompactPart J T))) := by rw [comp_neg]
    _ = - ((J.op.comp J.op).comp (noncompactPart J T)) := by simp only [comp_assoc]
    _ = - ((ContinuousLinearMap.id ℂ H).comp (noncompactPart J T)) := by rw [hJ]
    _ = - noncompactPart J T := by simp only [id_comp]

end InfoGeometry.Lie.CartanKrein

end noncomputable section
