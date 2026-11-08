/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Adapted from AxiomMath/CFSG, Apache-2.0. The model predicates and parameter
conditions follow `CFSG.Open.StatedDefs`.
-/
module

public import Mathlib

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Classical

open Matrix

inductive Family
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus
  deriving DecidableEq, Repr

@[expose] def Scalars (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    Subgroup (GL ι K) :=
  (Matrix.GeneralLinearGroup.scalar ι).range

instance scalars_normal (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    (Scalars ι K).Normal := by
  rw [Scalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  infer_instance

abbrev Projective {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) : Type :=
  H ⧸ (Scalars ι K).subgroupOf H

@[expose] def SpecialLinear (n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  Subgroup.closure {A | (A : Matrix (Fin n) (Fin n) K).det = 1}

@[expose] def SpecialUnitary (n q : ℕ) (K : Type) [Field K] :
    Subgroup (GL (Fin n) K) :=
  Subgroup.closure {A | (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
    ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1}

@[expose] def Symplectic (n : ℕ) (K : Type) [Field K] :
    Subgroup (GL (Fin n ⊕ Fin n) K) :=
  let J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.fromBlocks 0 1 (-1) 0
  Subgroup.closure {A | (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J *
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J}

@[expose] def Orthogonal {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Q : (ι → K) → K) : Subgroup (GL ι K) :=
  Subgroup.closure {A | ∀ v : ι → K,
    Q (Matrix.mulVec (A : Matrix ι ι K) v) = Q v}

@[expose] def QuadOdd (n : ℕ) (K : Type) [Field K]
    (v : Fin n ⊕ Fin n ⊕ Unit → K) : K :=
  ∑ i, v (.inl i) * v (.inr (.inl i)) + v (.inr (.inr ())) ^ 2

@[expose] def QuadPlus (n : ℕ) (K : Type) [Field K] (v : Fin n ⊕ Fin n → K) : K :=
  ∑ i, v (.inl i) * v (.inr i)

@[expose] def QuadMinus (n : ℕ) (K : Type) [Field K] (b c : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) : K :=
  ∑ i, v (.inl i) * v (.inr (.inl i)) + v (.inr (.inr 0)) ^ 2 +
    b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2

@[expose] def Admissible (family : Family) (n p f : ℕ) : Prop :=
  p.Prime ∧ 1 ≤ f ∧
    match family with
    | .PSL => 2 ≤ n ∧ (n, p ^ f) ≠ (2, 2) ∧ (n, p ^ f) ≠ (2, 3)
    | .PSU => 3 ≤ n ∧ (n, p ^ f) ≠ (3, 2)
    | .PSp => 2 ≤ n ∧ (n, p ^ f) ≠ (2, 2)
    | .POmegaOdd => 3 ≤ n ∧ p ≠ 2
    | .POmegaPlus => 4 ≤ n
    | .POmegaMinus => 4 ≤ n

@[expose] def Model (G : Type) [Group G] (family : Family) (n p f : ℕ) : Prop :=
  Admissible family n p f ∧
    match family with
    | .PSL => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
        Nonempty (G ≃* Projective (SpecialLinear n K))
    | .PSU => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (p ^ f) ^ 2 ∧
        Nonempty (G ≃* Projective (SpecialUnitary n (p ^ f) K))
    | .PSp => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
        Nonempty (G ≃* Projective (Symplectic n K))
    | .POmegaOdd => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
        Nonempty (G ≃* Projective (Orthogonal (QuadOdd n K)))
    | .POmegaPlus => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
        Nonempty (G ≃* Projective (Orthogonal (QuadPlus n K)))
    | .POmegaMinus => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
        ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
          Nonempty (G ≃* Projective (Orthogonal (QuadMinus n K b c)))

@[expose] def Catalog (G : Type) [Group G] : Prop :=
  ∃ (family : Family) (n p f : ℕ), Model G family n p f

end InfoGeometry.Exceptional.CFSGPort.Classical

end
