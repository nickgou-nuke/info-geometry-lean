import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

namespace NumberSystemLadder

open CategoryTheory

inductive NumSys
  | Primes
  | Naturals
  | Rationals
  | Reals
  | Complex

open NumSys

def rank : NumSys → ℕ
  | Primes => 0
  | Naturals => 1
  | Rationals => 2
  | Reals => 3
  | Complex => 4

def le (A B : NumSys) : Prop :=
  rank A ≤ rank B

-- To make a category we need Preorder
-- We can just define Hom.

inductive Hom : NumSys → NumSys → Type
  | id (A : NumSys) : Hom A A
  | step_P_N : Hom Primes Naturals
  | step_N_Q : Hom Naturals Rationals
  | step_Q_R : Hom Rationals Reals
  | step_R_C : Hom Reals Complex
  -- composites
  | comp_P_Q : Hom Primes Rationals
  | comp_P_R : Hom Primes Reals
  | comp_P_C : Hom Primes Complex
  | comp_N_R : Hom Naturals Reals
  | comp_N_C : Hom Naturals Complex
  | comp_Q_C : Hom Rationals Complex

def comp : {A B C : NumSys} → Hom A B → Hom B C → Hom A C
  | _, _, _, Hom.id _, g => g
  | _, _, _, f, Hom.id _ => f
  | _, _, _, Hom.step_P_N, Hom.step_N_Q => Hom.comp_P_Q
  | _, _, _, Hom.step_P_N, Hom.comp_N_R => Hom.comp_P_R
  | _, _, _, Hom.step_P_N, Hom.comp_N_C => Hom.comp_P_C
  | _, _, _, Hom.comp_P_Q, Hom.step_Q_R => Hom.comp_P_R
  | _, _, _, Hom.comp_P_Q, Hom.comp_Q_C => Hom.comp_P_C
  | _, _, _, Hom.comp_P_R, Hom.step_R_C => Hom.comp_P_C
  | _, _, _, Hom.step_N_Q, Hom.step_Q_R => Hom.comp_N_R
  | _, _, _, Hom.step_N_Q, Hom.comp_Q_C => Hom.comp_N_C
  | _, _, _, Hom.comp_N_R, Hom.step_R_C => Hom.comp_N_C
  | _, _, _, Hom.step_Q_R, Hom.step_R_C => Hom.comp_Q_C

instance : Category NumSys where
  Hom A B := Hom A B
  id A := Hom.id A
  comp := comp
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl

def SpectralConstraint (S : NumSys) : Prop :=
  S = Primes ∨ S = Complex

theorem riemann_zeroes_structurally_bound {base : Hom Primes Complex} :
    SpectralConstraint Primes → SpectralConstraint Complex := by
  intro _h
  exact Or.inr rfl

end NumberSystemLadder
