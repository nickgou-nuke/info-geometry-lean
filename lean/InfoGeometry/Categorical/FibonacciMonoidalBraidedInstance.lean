/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Fintype.EquivFin
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Quantum.FibonacciFusionCategory
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

/-!
# Full `MonoidalCategory` and `BraidedCategory` Instances on Fibonacci Multiplicities

Constructs a category `FibFam` of finite indexed multiplicity families over `ℂ`, with
`FibObject` (`{unit, tau}`) with the Fibonacci fusion rule `τ ⊗ τ = 1 ⊕ τ`,
the golden-ratio 6j associator `F` (`YangBaxterProof.τ`, `YangBaxterProof.s`),
and the 10th-root-of-unity braiding `R` (`-q`, `q³`), proving Mathlib's full
`MonoidalCategory` and `BraidedCategory` axioms (including arbitrary-morphism
naturality, pentagon, triangle, and both hexagon coherence laws).

This file constructs the category, monoidal structure, and braiding on `FibFam`.
It does not construct a transport to `FibObject → ℕ`, a fusion-category instance,
or a proof that the braiding is nonsymmetric.
-/

noncomputable section

namespace InfoGeometry.Categorical.FibonacciMonoidalBraidedInstance

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open FibonacciFusion
open InfoGeometry.Canonical

/-! ## 1. Finite enumeration and Fibonacci fusion admissibility -/

instance : Fintype FibObject where
  elems := {FibObject.unit, FibObject.tau}
  complete := fun x => by cases x <;> simp

@[simp] theorem sum_fibObject {M : Type*} [AddCommMonoid M] (g : FibObject → M) :
    (∑ x : FibObject, g x) = g FibObject.unit + g FibObject.tau := by
  change (Finset.univ : Finset FibObject).sum g = _
  have h : (Finset.univ : Finset FibObject) = ({FibObject.unit, FibObject.tau} : Finset FibObject) := rfl
  rw [h, Finset.sum_pair (by decide)]

/-- Boolean fusion admissibility predicate $N_{ab}^c = 1$. -/
def FibAdmB : FibObject → FibObject → FibObject → Bool
  | FibObject.unit, FibObject.unit, FibObject.unit => true
  | FibObject.unit, FibObject.tau, FibObject.tau => true
  | FibObject.tau, FibObject.unit, FibObject.tau => true
  | FibObject.tau, FibObject.tau, FibObject.unit => true
  | FibObject.tau, FibObject.tau, FibObject.tau => true
  | _, _, _ => false

theorem fibAdmB_comm (a b d : FibObject) : FibAdmB a b d = FibAdmB b a d := by
  cases a <;> cases b <;> cases d <;> rfl

theorem fibAdmB_unit_left (b d : FibObject) :
    FibAdmB FibObject.unit b d = true ↔ b = d := by
  cases b <;> cases d <;> decide

theorem fibAdmB_unit_right (a d : FibObject) :
    FibAdmB a FibObject.unit d = true ↔ a = d := by
  cases a <;> cases d <;> decide

/-! ## 2. Scalar Fibonacci 6j `F`-symbol and `R`-symbol with coherence laws -/

/-- Full 6-index scalar Fibonacci `F`-symbol over `ℂ`. -/
def fibFSym (a b c d e f : FibObject) : ℂ :=
  match FibAdmB a b e && FibAdmB e c d && FibAdmB b c f && FibAdmB a f d with
  | false => 0
  | true =>
    match a, b, c, d, e, f with
    | .tau, .tau, .tau, .tau, .unit, .unit => YangBaxterProof.τ
    | .tau, .tau, .tau, .tau, .unit, .tau => YangBaxterProof.s
    | .tau, .tau, .tau, .tau, .tau, .unit => YangBaxterProof.s
    | .tau, .tau, .tau, .tau, .tau, .tau => -YangBaxterProof.τ
    | _, _, _, _, _, _ => 1

/-- Full 3-index scalar Fibonacci `R`-symbol over `ℂ`. -/
def fibRSym (a b d : FibObject) : ℂ :=
  match FibAdmB a b d with
  | false => 0
  | true =>
    match a, b, d with
    | .tau, .tau, .unit => -YangBaxterProof.q
    | .tau, .tau, .tau => YangBaxterProof.q ^ 3
    | _, _, _ => 1

/-- Inverse 3-index scalar Fibonacci `R`-symbol over `ℂ`. -/
def fibRSymInv (a b d : FibObject) : ℂ :=
  match FibAdmB a b d with
  | false => 0
  | true =>
    match a, b, d with
    | .tau, .tau, .unit => (-YangBaxterProof.q)⁻¹
    | .tau, .tau, .tau => (YangBaxterProof.q ^ 3)⁻¹
    | _, _, _ => 1

private lemma fib_s_sq : YangBaxterProof.s ^ 2 = YangBaxterProof.τ :=
  YangBaxterProof.s_sq_eq_tau

private lemma fib_τ_sq : YangBaxterProof.τ ^ 2 = 1 - YangBaxterProof.τ := by
  linear_combination YangBaxterProof.tau_sq_add_tau

private lemma fib_τ_eq_q :
    YangBaxterProof.τ = YangBaxterProof.q ^ 2 - YangBaxterProof.q ^ 3 := by
  have h1 := YangBaxterProof.τ_eq_q_minus_q4_minus_one
  have h2 := YangBaxterProof.cyclotomic_relation
  linear_combination h1 - h2

private lemma fib_q_four :
    YangBaxterProof.q ^ 4 =
      YangBaxterProof.q ^ 3 - YangBaxterProof.q ^ 2 + YangBaxterProof.q - 1 := by
  have h := YangBaxterProof.cyclotomic_relation
  linear_combination h

private lemma fib_q_five : YangBaxterProof.q ^ 5 = -1 :=
  YangBaxterProof.q_pow_five

private lemma fib_q_six : YangBaxterProof.q ^ 6 = -YangBaxterProof.q := by
  calc YangBaxterProof.q ^ 6 = YangBaxterProof.q ^ 5 * YangBaxterProof.q := by ring
  _ = -YangBaxterProof.q := by rw [fib_q_five]; ring

private lemma fib_q_ne_zero : YangBaxterProof.q ≠ 0 :=
  Complex.exp_ne_zero _

theorem fibRSym_mul_inv (a b d : FibObject) (h : FibAdmB a b d = true) :
    fibRSym a b d * fibRSymInv a b d = 1 := by
  have hq : YangBaxterProof.q ≠ 0 := fib_q_ne_zero
  have hq3 : YangBaxterProof.q ^ 3 ≠ 0 := pow_ne_zero 3 hq
  cases a <;> cases b <;> cases d <;> simp [FibAdmB] at h
  all_goals simp [fibRSym, fibRSymInv, FibAdmB, hq, hq3, mul_inv_cancel₀]

theorem fibRSym_inv_mul (a b d : FibObject) (h : FibAdmB a b d = true) :
    fibRSymInv a b d * fibRSym a b d = 1 := by
  rw [mul_comm]
  exact fibRSym_mul_inv a b d h

theorem fibFSym_unit_middle (a b d : FibObject) (h : FibAdmB a b d = true) :
    fibFSym a FibObject.unit b d a b = 1 := by
  cases a <;> cases b <;> cases d <;> simp [FibAdmB] at h ⊢ <;>
    simp [fibFSym, FibAdmB]

/-- Kernel-reducible normal form in `ℤ[τ, s]` for orthogonality and pentagon laws. -/
private structure TauS where
  c0 : ℤ
  c1 : ℤ
  d0 : ℤ
  d1 : ℤ
  deriving DecidableEq

private def TauS.zero : TauS := ⟨0, 0, 0, 0⟩
private def TauS.one : TauS := ⟨1, 0, 0, 0⟩
private def TauS.tau : TauS := ⟨0, 1, 0, 0⟩
private def TauS.negTau : TauS := ⟨0, -1, 0, 0⟩
private def TauS.sVal : TauS := ⟨0, 0, 1, 0⟩

private def TauS.add (x y : TauS) : TauS :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.d0 + y.d0, x.d1 + y.d1⟩

private def mulPairTau (a0 a1 b0 b1 : ℤ) : ℤ × ℤ :=
  (a0 * b0 + a1 * b1, a0 * b1 + a1 * b0 - a1 * b1)

private def TauS.mul (x y : TauS) : TauS :=
  let p := mulPairTau x.c0 x.c1 y.c0 y.c1
  let q := mulPairTau x.d0 x.d1 y.d0 y.d1
  let r := mulPairTau x.c0 x.c1 y.d0 y.d1
  let u := mulPairTau x.d0 x.d1 y.c0 y.c1
  ⟨p.1 + q.2, p.2 + q.1 - q.2, r.1 + u.1, r.2 + u.2⟩

private def TauS.eval (x : TauS) : ℂ :=
  (x.c0 : ℂ) + (x.c1 : ℂ) * YangBaxterProof.τ +
    ((x.d0 : ℂ) + (x.d1 : ℂ) * YangBaxterProof.τ) * YangBaxterProof.s

private lemma TauS.eval_add_aux (τ s : ℂ) (x y : TauS) :
    (((x.add y).c0 : ℂ) + ((x.add y).c1 : ℂ) * τ +
        (((x.add y).d0 : ℂ) + ((x.add y).d1 : ℂ) * τ) * s) =
      ((x.c0 : ℂ) + (x.c1 : ℂ) * τ + ((x.d0 : ℂ) + (x.d1 : ℂ) * τ) * s) +
        ((y.c0 : ℂ) + (y.c1 : ℂ) * τ + ((y.d0 : ℂ) + (y.d1 : ℂ) * τ) * s) := by
  dsimp [TauS.add]
  push_cast
  ring

private lemma TauS.eval_add (x y : TauS) : (x.add y).eval = x.eval + y.eval :=
  TauS.eval_add_aux YangBaxterProof.τ YangBaxterProof.s x y

private lemma TauS.eval_mul_aux (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 = 1 - τ) (x y : TauS) :
    (((x.mul y).c0 : ℂ) + ((x.mul y).c1 : ℂ) * τ +
        (((x.mul y).d0 : ℂ) + ((x.mul y).d1 : ℂ) * τ) * s) =
      ((x.c0 : ℂ) + (x.c1 : ℂ) * τ + ((x.d0 : ℂ) + (x.d1 : ℂ) * τ) * s) *
        ((y.c0 : ℂ) + (y.c1 : ℂ) * τ + ((y.d0 : ℂ) + (y.d1 : ℂ) * τ) * s) := by
  dsimp [TauS.mul, mulPairTau]
  push_cast
  have hs2 : s * s = τ := by simpa [sq] using hs
  have h1 : ∀ a0 a1 b0 b1 : ℂ, (a0 + a1 * τ) * (b0 + b1 * τ) =
      (a0 * b0 + a1 * b1) + (a0 * b1 + a1 * b0 - a1 * b1) * τ := by
    intro a0 a1 b0 b1
    linear_combination a1 * b1 * hτ
  have h2 : ∀ q0 q1 : ℂ, (q0 + q1 * τ) * τ = q1 + (q0 - q1) * τ := by
    intro q0 q1
    linear_combination q1 * hτ
  symm
  calc
    ((x.c0 : ℂ) + (x.c1 : ℂ) * τ + ((x.d0 : ℂ) + (x.d1 : ℂ) * τ) * s) *
        ((y.c0 : ℂ) + (y.c1 : ℂ) * τ + ((y.d0 : ℂ) + (y.d1 : ℂ) * τ) * s)
      = ((x.c0 : ℂ) + (x.c1 : ℂ) * τ) * ((y.c0 : ℂ) + (y.c1 : ℂ) * τ) +
          ((x.d0 : ℂ) + (x.d1 : ℂ) * τ) * ((y.d0 : ℂ) + (y.d1 : ℂ) * τ) * (s * s) +
          (((x.c0 : ℂ) + (x.c1 : ℂ) * τ) * ((y.d0 : ℂ) + (y.d1 : ℂ) * τ) +
            ((x.d0 : ℂ) + (x.d1 : ℂ) * τ) * ((y.c0 : ℂ) + (y.c1 : ℂ) * τ)) * s := by ring
    _ = (((x.c0 : ℂ) * y.c0 + x.c1 * y.c1) +
            ((x.c0 : ℂ) * y.c1 + x.c1 * y.c0 - x.c1 * y.c1) * τ) +
          (((x.d0 : ℂ) * y.d0 + x.d1 * y.d1) +
            ((x.d0 : ℂ) * y.d1 + x.d1 * y.d0 - x.d1 * y.d1) * τ) * τ +
          ((((x.c0 : ℂ) * y.d0 + x.c1 * y.d1) +
              ((x.c0 : ℂ) * y.d1 + x.c1 * y.d0 - x.c1 * y.d1) * τ) +
            (((x.d0 : ℂ) * y.c0 + x.d1 * y.c1) +
              ((x.d0 : ℂ) * y.c1 + x.d1 * y.c0 - x.d1 * y.c1) * τ)) * s := by
      rw [hs2, h1, h1, h1, h1]
    _ = (((x.c0 : ℂ) * y.c0 + x.c1 * y.c1) +
            ((x.c0 : ℂ) * y.c1 + x.c1 * y.c0 - x.c1 * y.c1) * τ) +
          (((x.d0 : ℂ) * y.d1 + x.d1 * y.d0 - x.d1 * y.d1) +
            (((x.d0 : ℂ) * y.d0 + x.d1 * y.d1) -
              ((x.d0 : ℂ) * y.d1 + x.d1 * y.d0 - x.d1 * y.d1)) * τ) +
          ((((x.c0 : ℂ) * y.d0 + x.c1 * y.d1) +
              ((x.c0 : ℂ) * y.d1 + x.c1 * y.d0 - x.c1 * y.d1) * τ) +
            (((x.d0 : ℂ) * y.c0 + x.d1 * y.c1) +
              ((x.d0 : ℂ) * y.c1 + x.d1 * y.c0 - x.d1 * y.c1) * τ)) * s := by
      rw [h2]
    _ = (((x.c0 : ℂ) * y.c0 + x.c1 * y.c1 + (x.d0 * y.d1 + x.d1 * y.d0 - x.d1 * y.d1)) +
            ((x.c0 * y.c1 + x.c1 * y.c0 - x.c1 * y.c1) +
              (x.d0 * y.d0 + x.d1 * y.d1) -
              (x.d0 * y.d1 + x.d1 * y.d0 - x.d1 * y.d1)) * τ) +
          (((x.c0 * y.d0 + x.c1 * y.d1 + (x.d0 * y.c0 + x.d1 * y.c1)) +
              ((x.c0 * y.d1 + x.c1 * y.d0 - x.c1 * y.d1) +
                (x.d0 * y.c1 + x.d1 * y.c0 - x.d1 * y.c1)) * τ) * s) := by ring

private lemma TauS.eval_mul (x y : TauS) : (x.mul y).eval = x.eval * y.eval :=
  TauS.eval_mul_aux YangBaxterProof.τ YangBaxterProof.s fib_s_sq fib_τ_sq x y

private def fibFSymT (a b c d e f : FibObject) : TauS :=
  match FibAdmB a b e && FibAdmB e c d && FibAdmB b c f && FibAdmB a f d with
  | false => TauS.zero
  | true =>
    match a, b, c, d, e, f with
    | .tau, .tau, .tau, .tau, .unit, .unit => TauS.tau
    | .tau, .tau, .tau, .tau, .unit, .tau => TauS.sVal
    | .tau, .tau, .tau, .tau, .tau, .unit => TauS.sVal
    | .tau, .tau, .tau, .tau, .tau, .tau => TauS.negTau
    | _, _, _, _, _, _ => TauS.one

private lemma fibFSymT_eval (a b c d e f : FibObject) :
    (fibFSymT a b c d e f).eval = fibFSym a b c d e f := by
  dsimp [fibFSymT, fibFSym]
  cases FibAdmB a b e && FibAdmB e c d && FibAdmB b c f && FibAdmB a f d
  · simp [TauS.eval, TauS.zero]
  · cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
      simp [TauS.eval, TauS.one, TauS.tau, TauS.negTau, TauS.sVal]

private theorem fibFSymT_orthog_left :
    ∀ a b c d e e' : FibObject,
      ((FibAdmB a b e && FibAdmB e c d && FibAdmB a b e' && FibAdmB e' c d) = true →
        ((fibFSymT a b c d e .unit).mul (fibFSymT a b c d e' .unit)).add
          ((fibFSymT a b c d e .tau).mul (fibFSymT a b c d e' .tau)) =
        (if e = e' then TauS.one else TauS.zero)) := by
  decide

theorem fibFSym_orthog_left (a b c d e e' : FibObject)
    (he₁ : FibAdmB a b e = true) (he₂ : FibAdmB e c d = true)
    (he'₁ : FibAdmB a b e' = true) (he'₂ : FibAdmB e' c d = true) :
    (∑ f : FibObject, fibFSym a b c d e f * fibFSym a b c d e' f) =
      if e = e' then 1 else 0 := by
  have hcond : (FibAdmB a b e && FibAdmB e c d && FibAdmB a b e' && FibAdmB e' c d) = true := by
    simp [he₁, he₂, he'₁, he'₂]
  have hT := congrArg TauS.eval (fibFSymT_orthog_left a b c d e e' hcond)
  rw [sum_fibObject, ← fibFSymT_eval, ← fibFSymT_eval, ← fibFSymT_eval, ← fibFSymT_eval]
  rw [← TauS.eval_mul, ← TauS.eval_mul, ← TauS.eval_add, hT]
  split_ifs <;> simp [TauS.eval, TauS.one, TauS.zero]

private theorem fibFSymT_orthog_right :
    ∀ a b c d f f' : FibObject,
      ((FibAdmB b c f && FibAdmB a f d && FibAdmB b c f' && FibAdmB a f' d) = true →
        ((fibFSymT a b c d .unit f).mul (fibFSymT a b c d .unit f')).add
          ((fibFSymT a b c d .tau f).mul (fibFSymT a b c d .tau f')) =
        (if f = f' then TauS.one else TauS.zero)) := by
  decide

theorem fibFSym_orthog_right (a b c d f f' : FibObject)
    (hf₁ : FibAdmB b c f = true) (hf₂ : FibAdmB a f d = true)
    (hf'₁ : FibAdmB b c f' = true) (hf'₂ : FibAdmB a f' d = true) :
    (∑ e : FibObject, fibFSym a b c d e f * fibFSym a b c d e f') =
      if f = f' then 1 else 0 := by
  have hcond : (FibAdmB b c f && FibAdmB a f d && FibAdmB b c f' && FibAdmB a f' d) = true := by
    simp [hf₁, hf₂, hf'₁, hf'₂]
  have hT := congrArg TauS.eval (fibFSymT_orthog_right a b c d f f' hcond)
  rw [sum_fibObject, ← fibFSymT_eval, ← fibFSymT_eval, ← fibFSymT_eval, ← fibFSymT_eval]
  rw [← TauS.eval_mul, ← TauS.eval_mul, ← TauS.eval_add, hT]
  split_ifs <;> simp [TauS.eval, TauS.one, TauS.zero]

private theorem fibFSymT_pentagon :
    ∀ a b c d t e g l k : FibObject,
      (((fibFSymT a b c g e .unit).mul (fibFSymT a .unit d t g k)).mul (fibFSymT b c d k .unit l)).add
          (((fibFSymT a b c g e .tau).mul (fibFSymT a .tau d t g k)).mul (fibFSymT b c d k .tau l)) =
        (fibFSymT e c d t g l).mul (fibFSymT a b l t e k) := by
  decide

theorem fibFSym_pentagon (a b c d t e g l k : FibObject) :
    (∑ m : FibObject, fibFSym a b c g e m * fibFSym a m d t g k * fibFSym b c d k m l) =
      fibFSym e c d t g l * fibFSym a b l t e k := by
  have hT := congrArg TauS.eval (fibFSymT_pentagon a b c d t e g l k)
  rw [sum_fibObject]
  simp only [← fibFSymT_eval, ← TauS.eval_mul, ← TauS.eval_add]
  exact hT

/-- Kernel-reducible cyclotomic normal form in `ℤ[q, s]` (`q^5 = -1`, `s^2 = q^2 - q^3`). -/
private structure Cyc4 where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
  deriving DecidableEq

private def Cyc4.zero : Cyc4 := ⟨0, 0, 0, 0⟩
private def Cyc4.one : Cyc4 := ⟨1, 0, 0, 0⟩
private def Cyc4.tau : Cyc4 := ⟨0, 0, 1, -1⟩
private def Cyc4.negTau : Cyc4 := ⟨0, 0, -1, 1⟩
private def Cyc4.negQ : Cyc4 := ⟨0, -1, 0, 0⟩
private def Cyc4.q3 : Cyc4 := ⟨0, 0, 0, 1⟩

private def Cyc4.add (x y : Cyc4) : Cyc4 :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3⟩

private def Cyc4.mul (x y : Cyc4) : Cyc4 :=
  let p0 := x.c0 * y.c0
  let p1 := x.c0 * y.c1 + x.c1 * y.c0
  let p2 := x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0
  let p3 := x.c0 * y.c3 + x.c1 * y.c2 + x.c2 * y.c1 + x.c3 * y.c0
  let p4 := x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1
  let p5 := x.c2 * y.c3 + x.c3 * y.c2
  let p6 := x.c3 * y.c3
  ⟨p0 - p4 - p5, p1 + p4 - p6, p2 - p4, p3 + p4⟩

private def Cyc4.eval (q : ℂ) (x : Cyc4) : ℂ :=
  (x.c0 : ℂ) + (x.c1 : ℂ) * q + (x.c2 : ℂ) * q ^ 2 + (x.c3 : ℂ) * q ^ 3

private lemma Cyc4.eval_add (q : ℂ) (x y : Cyc4) :
    (x.add y).eval q = x.eval q + y.eval q := by
  dsimp [Cyc4.add, Cyc4.eval]
  push_cast
  ring

private lemma Cyc4.eval_mul_aux (q : ℂ)
    (hq4 : q ^ 4 = q ^ 3 - q ^ 2 + q - 1) (hq5 : q ^ 5 = -1) (hq6 : q ^ 6 = -q)
    (x y : Cyc4) :
    (x.mul y).eval q = x.eval q * y.eval q := by
  dsimp [Cyc4.mul, Cyc4.eval]
  push_cast
  symm
  calc
    ((x.c0 : ℂ) + x.c1 * q + x.c2 * q ^ 2 + x.c3 * q ^ 3) *
        ((y.c0 : ℂ) + y.c1 * q + y.c2 * q ^ 2 + y.c3 * q ^ 3)
      = (x.c0 : ℂ) * y.c0 + (x.c0 * y.c1 + x.c1 * y.c0) * q +
          (x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0) * q ^ 2 +
          (x.c0 * y.c3 + x.c1 * y.c2 + x.c2 * y.c1 + x.c3 * y.c0) * q ^ 3 +
          (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1) * q ^ 4 +
          (x.c2 * y.c3 + x.c3 * y.c2) * q ^ 5 +
          (x.c3 * y.c3) * q ^ 6 := by ring
    _ = (x.c0 : ℂ) * y.c0 + (x.c0 * y.c1 + x.c1 * y.c0) * q +
          (x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0) * q ^ 2 +
          (x.c0 * y.c3 + x.c1 * y.c2 + x.c2 * y.c1 + x.c3 * y.c0) * q ^ 3 +
          (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1) * (q ^ 3 - q ^ 2 + q - 1) +
          (x.c2 * y.c3 + x.c3 * y.c2) * (-1) +
          (x.c3 * y.c3) * (-q) := by rw [hq4, hq5, hq6]
    _ = _ := by ring

private structure Cyc5S where
  a : Cyc4
  b : Cyc4
  deriving DecidableEq

private def Cyc5S.zero : Cyc5S := ⟨Cyc4.zero, Cyc4.zero⟩
private def Cyc5S.one : Cyc5S := ⟨Cyc4.one, Cyc4.zero⟩
private def Cyc5S.tau : Cyc5S := ⟨Cyc4.tau, Cyc4.zero⟩
private def Cyc5S.negTau : Cyc5S := ⟨Cyc4.negTau, Cyc4.zero⟩
private def Cyc5S.sVal : Cyc5S := ⟨Cyc4.zero, Cyc4.one⟩
private def Cyc5S.negQ : Cyc5S := ⟨Cyc4.negQ, Cyc4.zero⟩
private def Cyc5S.q3 : Cyc5S := ⟨Cyc4.q3, Cyc4.zero⟩

private def Cyc5S.add (x y : Cyc5S) : Cyc5S :=
  ⟨x.a.add y.a, x.b.add y.b⟩

private def Cyc5S.mul (x y : Cyc5S) : Cyc5S :=
  ⟨(x.a.mul y.a).add (Cyc4.tau.mul (x.b.mul y.b)),
   (x.a.mul y.b).add (x.b.mul y.a)⟩

private def Cyc5S.eval (x : Cyc5S) : ℂ :=
  x.a.eval YangBaxterProof.q + x.b.eval YangBaxterProof.q * YangBaxterProof.s

private lemma Cyc5S.eval_add (x y : Cyc5S) : (x.add y).eval = x.eval + y.eval := by
  dsimp [Cyc5S.add, Cyc5S.eval]
  rw [Cyc4.eval_add, Cyc4.eval_add]
  ring

private lemma Cyc5S.eval_mul_aux (q τ s : ℂ)
    (hq4 : q ^ 4 = q ^ 3 - q ^ 2 + q - 1) (hq5 : q ^ 5 = -1) (hq6 : q ^ 6 = -q)
    (hs : s ^ 2 = τ) (hτ : τ = q ^ 2 - q ^ 3) (x y : Cyc5S) :
    ((x.mul y).a.eval q + (x.mul y).b.eval q * s) =
      (x.a.eval q + x.b.eval q * s) * (y.a.eval q + y.b.eval q * s) := by
  dsimp [Cyc5S.mul]
  rw [Cyc4.eval_add, Cyc4.eval_add]
  rw [Cyc4.eval_mul_aux q hq4 hq5 hq6, Cyc4.eval_mul_aux q hq4 hq5 hq6,
    Cyc4.eval_mul_aux q hq4 hq5 hq6, Cyc4.eval_mul_aux q hq4 hq5 hq6,
    Cyc4.eval_mul_aux q hq4 hq5 hq6]
  have htau : Cyc4.tau.eval q = s ^ 2 := by
    dsimp [Cyc4.tau, Cyc4.eval]
    push_cast
    calc (0 : ℂ) + 0 * q + 1 * q ^ 2 + (-1 : ℂ) * q ^ 3 = q ^ 2 - q ^ 3 := by ring
    _ = τ := hτ.symm
    _ = s ^ 2 := hs.symm
  rw [htau]
  ring

private lemma Cyc5S.eval_mul (x y : Cyc5S) : (x.mul y).eval = x.eval * y.eval :=
  Cyc5S.eval_mul_aux YangBaxterProof.q YangBaxterProof.τ YangBaxterProof.s
    fib_q_four fib_q_five fib_q_six fib_s_sq fib_τ_eq_q x y

private def fibFSymC (a b c d e f : FibObject) : Cyc5S :=
  match FibAdmB a b e && FibAdmB e c d && FibAdmB b c f && FibAdmB a f d with
  | false => Cyc5S.zero
  | true =>
    match a, b, c, d, e, f with
    | .tau, .tau, .tau, .tau, .unit, .unit => Cyc5S.tau
    | .tau, .tau, .tau, .tau, .unit, .tau => Cyc5S.sVal
    | .tau, .tau, .tau, .tau, .tau, .unit => Cyc5S.sVal
    | .tau, .tau, .tau, .tau, .tau, .tau => Cyc5S.negTau
    | _, _, _, _, _, _ => Cyc5S.one

private def fibRSymC (a b d : FibObject) : Cyc5S :=
  match FibAdmB a b d with
  | false => Cyc5S.zero
  | true =>
    match a, b, d with
    | .tau, .tau, .unit => Cyc5S.negQ
    | .tau, .tau, .tau => Cyc5S.q3
    | _, _, _ => Cyc5S.one

private lemma fibFSymC_eval (a b c d e f : FibObject) :
    (fibFSymC a b c d e f).eval = fibFSym a b c d e f := by
  dsimp [fibFSymC, fibFSym]
  cases FibAdmB a b e && FibAdmB e c d && FibAdmB b c f && FibAdmB a f d
  · simp [Cyc5S.eval, Cyc5S.zero, Cyc4.eval, Cyc4.zero]
  · cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
      simp [Cyc5S.eval, Cyc5S.one, Cyc5S.tau, Cyc5S.negTau, Cyc5S.sVal,
        Cyc4.eval, Cyc4.zero, Cyc4.one, Cyc4.tau, Cyc4.negTau, fib_τ_eq_q] <;>
      ring

private lemma fibRSymC_eval (a b d : FibObject) :
    (fibRSymC a b d).eval = fibRSym a b d := by
  dsimp [fibRSymC, fibRSym]
  cases FibAdmB a b d
  · simp [Cyc5S.eval, Cyc5S.zero, Cyc4.eval, Cyc4.zero]
  · cases a <;> cases b <;> cases d <;>
      simp [Cyc5S.eval, Cyc5S.one, Cyc5S.negQ, Cyc5S.q3,
        Cyc4.eval, Cyc4.zero, Cyc4.one, Cyc4.negQ, Cyc4.q3]

private theorem fibFSymC_hexagon_forward :
    ∀ a b c d e g : FibObject,
      (((fibFSymC a b c d e .unit).mul (fibRSymC a .unit d)).mul (fibFSymC b c a d .unit g)).add
          (((fibFSymC a b c d e .tau).mul (fibRSymC a .tau d)).mul (fibFSymC b c a d .tau g)) =
        ((fibRSymC a b e).mul (fibFSymC b a c d e g)).mul (fibRSymC a c g) := by
  decide

theorem fibFSym_hexagon_forward (a b c d e g : FibObject) :
    (∑ f : FibObject, fibFSym a b c d e f * fibRSym a f d * fibFSym b c a d f g) =
      fibRSym a b e * fibFSym b a c d e g * fibRSym a c g := by
  have hC := congrArg Cyc5S.eval (fibFSymC_hexagon_forward a b c d e g)
  rw [sum_fibObject]
  simp only [← fibFSymC_eval, ← fibRSymC_eval, ← Cyc5S.eval_mul, ← Cyc5S.eval_add]
  exact hC

private theorem fibFSymC_hexagon_reverse :
    ∀ a b c d f h : FibObject,
      (((fibFSymC a b c d .unit f).mul (fibRSymC .unit c d)).mul (fibFSymC c a b d h .unit)).add
          (((fibFSymC a b c d .tau f).mul (fibRSymC .tau c d)).mul (fibFSymC c a b d h .tau)) =
        ((fibRSymC b c f).mul (fibFSymC a c b d h f)).mul (fibRSymC a c h) := by
  decide

theorem fibFSym_hexagon_reverse (a b c d f h : FibObject) :
    (∑ e : FibObject, fibFSym a b c d e f * fibRSym e c d * fibFSym c a b d h e) =
      fibRSym b c f * fibFSym a c b d h f * fibRSym a c h := by
  have hC := congrArg Cyc5S.eval (fibFSymC_hexagon_reverse a b c d f h)
  rw [sum_fibObject]
  simp only [← fibFSymC_eval, ← fibRSymC_eval, ← Cyc5S.eval_mul, ← Cyc5S.eval_add]
  exact hC

/-! ## 3. Explicit semisimple Fibonacci fusion category `FibFam` (`MonoidalCategory` & `BraidedCategory`) -/

/-- Family of finite multiplicity index sets indexed by simple Fibonacci objects `{1, τ}`. -/
structure FibFam : Type 1 where
  idx : FibObject → Type 0
  [fintypeIdx : ∀ s, Fintype (idx s)]
  [decEqIdx : ∀ s, DecidableEq (idx s)]

attribute [instance] FibFam.fintypeIdx FibFam.decEqIdx

instance : Category.{0} FibFam where
  Hom A B := ∀ s : FibObject, Matrix (A.idx s) (B.idx s) ℂ
  id A s := (1 : Matrix (A.idx s) (A.idx s) ℂ)
  comp f g s := f s * g s
  id_comp f := by funext s; exact Matrix.one_mul (f s)
  comp_id f := by funext s; exact Matrix.mul_one (f s)
  assoc f g h := by funext s; exact Matrix.mul_assoc (f s) (g s) (h s)

@[ext] theorem FibFam.hom_ext {A B : FibFam} {f g : A ⟶ B}
    (h : ∀ s i j, f s i j = g s i j) : f = g := by
  funext s i j
  exact h s i j

@[simp] theorem FibFam.id_apply (A : FibFam) (s : FibObject) (i j : A.idx s) :
    (𝟙 A : A ⟶ A) s i j = if i = j then 1 else 0 :=
  Matrix.one_apply

@[simp] theorem FibFam.comp_apply {A B C : FibFam} (f : A ⟶ B) (g : B ⟶ C)
    (s : FibObject) (i : A.idx s) (k : C.idx s) :
    (f ≫ g) s i k = ∑ j : B.idx s, f s i j * g s j k :=
  Matrix.mul_apply

/-- Cross-sector safe matrix entry (zero off-sector, avoiding dependent transport leakage). -/
def homEntry {A B : FibFam} (f : A ⟶ B) (s s' : FibObject) (i : A.idx s) (j : B.idx s') : ℂ :=
  if h : s = s' then f s i (h ▸ j) else 0

@[simp] theorem homEntry_same {A B : FibFam} (f : A ⟶ B) (s : FibObject)
    (i : A.idx s) (j : B.idx s) : homEntry f s s i j = f s i j :=
  dite_eq_left rfl

theorem homEntry_ne {A B : FibFam} (f : A ⟶ B) {s s' : FibObject} (h : s ≠ s')
    (i : A.idx s) (j : B.idx s') : homEntry f s s' i j = 0 :=
  dite_eq_right h

theorem sum_homEntry_mul {A₁ A₂ A₃ : FibFam}
    (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (s₁ s₂ s₃ : FibObject)
    (i₁ : A₁.idx s₁) (i₃ : A₃.idx s₃) :
    (∑ i₂ : A₂.idx s₂, homEntry f s₁ s₂ i₁ i₂ * homEntry g s₂ s₃ i₂ i₃) =
      if s₁ = s₂ then homEntry (f ≫ g) s₁ s₃ i₁ i₃ else 0 := by
  by_cases h₁₂ : s₁ = s₂
  · subst h₁₂
    rw [ite_eq_left rfl]
    by_cases h₁₃ : s₁ = s₃
    · subst h₁₃
      simp [homEntry_same, FibFam.comp_apply]
    · simp [homEntry_ne _ h₁₃]
  · simp [h₁₂, homEntry_ne _ h₁₂]

@[simp] theorem sum_homEntry_id_left {A B : FibFam} (g : A ⟶ B) (s₁ s₂ s₃ : FibObject)
    (i₁ : A.idx s₁) (i₃ : B.idx s₃) :
    (∑ i₂ : A.idx s₂, homEntry (𝟙 A) s₁ s₂ i₁ i₂ * homEntry g s₂ s₃ i₂ i₃) =
      if s₁ = s₂ then homEntry g s₁ s₃ i₁ i₃ else 0 := by
  simpa using sum_homEntry_mul (𝟙 A) g s₁ s₂ s₃ i₁ i₃

@[simp] theorem sum_homEntry_id_right {A B : FibFam} (f : A ⟶ B) (s₁ s₂ s₃ : FibObject)
    (i₁ : A.idx s₁) (i₃ : B.idx s₃) :
    (∑ i₂ : B.idx s₂, homEntry f s₁ s₂ i₁ i₂ * homEntry (𝟙 B) s₂ s₃ i₂ i₃) =
      if s₁ = s₂ then homEntry f s₁ s₃ i₁ i₃ else 0 := by
  simpa using sum_homEntry_mul f (𝟙 B) s₁ s₂ s₃ i₁ i₃

theorem sum_fib_homEntry_mul {A₁ A₂ A₃ : FibFam}
    (w : FibObject → ℂ) (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
    (s₁ s₃ : FibObject) (i₁ : A₁.idx s₁) (i₃ : A₃.idx s₃) :
    (∑ s₂ : FibObject, w s₂ *
        ∑ i₂ : A₂.idx s₂, homEntry f s₁ s₂ i₁ i₂ * homEntry g s₂ s₃ i₂ i₃) =
      w s₁ * homEntry (f ≫ g) s₁ s₃ i₁ i₃ := by
  cases s₁ <;> cases s₃ <;>
    simp [sum_homEntry_mul, homEntry_ne]

theorem homEntry_id_mul_homEntry {A B : FibFam} (g : A ⟶ B) (s₁ s₂ s₃ : FibObject)
    (i₁ : A.idx s₁) (i₂ : A.idx s₂) (i₃ : B.idx s₃) :
    homEntry (𝟙 A) s₁ s₂ i₁ i₂ * homEntry g s₂ s₃ i₂ i₃ =
      if h : s₁ = s₂ then
        (if i₁ = h ▸ i₂ then homEntry g s₁ s₃ i₁ i₃ else 0)
      else 0 := by
  by_cases h₁₂ : s₁ = s₂
  · subst s₂
    simp only [homEntry_same, FibFam.id_apply]
    by_cases hi : i₁ = i₂
    · subst i₂
      simp
    · simp [hi]
  · simp [homEntry_ne _ h₁₂, h₁₂]

/-- Semisimple tensor product object in `FibFam` encoded via Fibonacci fusion channels. -/
@[reducible]
def fibFamTensorObj (A B : FibFam) : FibFam where
  idx c := Σ ab : FibObject × FibObject, PLift (FibAdmB ab.1 ab.2 c = true) × A.idx ab.1 × B.idx ab.2

private theorem sum_plift_bool (b : Bool) (val : ℂ) :
    (∑ _h : PLift (b = true), val) = if b = true then val else 0 := by
  cases b
  · have : IsEmpty (PLift (false = true)) := ⟨fun ⟨h⟩ => by cases h⟩
    simp
  · have : Unique (PLift (true = true)) := ⟨⟨⟨rfl⟩⟩, fun ⟨_⟩ => rfl⟩
    simp

theorem sum_fibFamTensorIdx {A B : FibFam} {c : FibObject}
    (G : ∀ a b : FibObject, A.idx a → B.idx b → ℂ) :
    (∑ x : (fibFamTensorObj A B).idx c, G x.1.1 x.1.2 x.2.2.1 x.2.2.2) =
      ∑ a : FibObject, ∑ b : FibObject,
        if FibAdmB a b c = true then ∑ i : A.idx a, ∑ j : B.idx b, G a b i j else 0 := by
  classical
  change (∑ x : (Σ ab : FibObject × FibObject,
      PLift (FibAdmB ab.1 ab.2 c = true) × A.idx ab.1 × B.idx ab.2),
      G x.1.1 x.1.2 x.2.2.1 x.2.2.2) = _
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [sum_plift_bool]

private theorem tensorIdx_id_eq {A B : FibFam} {c : FibObject}
    (x y : (fibFamTensorObj A B).idx c) :
    homEntry (𝟙 A) x.1.1 y.1.1 x.2.2.1 y.2.2.1 *
      homEntry (𝟙 B) x.1.2 y.1.2 x.2.2.2 y.2.2.2 =
      if x = y then 1 else 0 := by
  rcases x with ⟨⟨a, b⟩, ⟨h⟩, i, j⟩
  rcases y with ⟨⟨a', b'⟩, ⟨h'⟩, i', j'⟩
  by_cases ha : a = a' <;> by_cases hb : b = b'
  · subst ha hb
    have hproof : h = h' := Subsingleton.elim _ _
    cases hproof
    by_cases hi : i = i' <;> by_cases hj : j = j' <;>
      simp [homEntry, FibFam.id_apply, hi, hj]
  · simp [homEntry_ne _ hb, hb]
  · simp [homEntry_ne _ ha, ha]
  · simp [homEntry_ne _ ha, ha]

/-- Tensor product of morphisms in `FibFam`. -/
def fibFamTensorHom {A₁ A₂ B₁ B₂ : FibFam} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
    fibFamTensorObj A₁ B₁ ⟶ fibFamTensorObj A₂ B₂ :=
  fun _c ⟨⟨a₁, b₁⟩, _, i₁, j₁⟩ ⟨⟨a₂, b₂⟩, _, i₂, j₂⟩ =>
    homEntry f a₁ a₂ i₁ i₂ * homEntry g b₁ b₂ j₁ j₂

/-- Left whiskering in `FibFam`. -/
def fibFamWhiskerLeft (A : FibFam) {B₁ B₂ : FibFam} (g : B₁ ⟶ B₂) :
    fibFamTensorObj A B₁ ⟶ fibFamTensorObj A B₂ :=
  fibFamTensorHom (𝟙 A) g

/-- Right whiskering in `FibFam`. -/
def fibFamWhiskerRight {A₁ A₂ : FibFam} (f : A₁ ⟶ A₂) (B : FibFam) :
    fibFamTensorObj A₁ B ⟶ fibFamTensorObj A₂ B :=
  fibFamTensorHom f (𝟙 B)

/-- Monoidal unit object `1` supported solely at `FibObject.unit` with multiplicity `1`. -/
def fibFamUnit : FibFam where
  idx
    | .unit => PUnit
    | .tau => PEmpty
  fintypeIdx
    | .unit => inferInstanceAs (Fintype PUnit)
    | .tau => inferInstanceAs (Fintype PEmpty)
  decEqIdx
    | .unit => inferInstanceAs (DecidableEq PUnit)
    | .tau => inferInstanceAs (DecidableEq PEmpty)

/-- The unit fusion channel identifies the left tensor index with the original
fiber.  This equivalence records the carrier identification explicitly;
admissibility forces the second simple object to be the output object. -/
private def fibFamLeftUnitIndexEquiv (B : FibFam) (c : FibObject) :
    (fibFamTensorObj fibFamUnit B).idx c ≃ B.idx c where
  toFun x := by
    rcases x with ⟨⟨u, b⟩, ⟨h⟩, p, i⟩
    cases u with
    | unit =>
        have hbc : b = c := (fibAdmB_unit_left b c).mp h
        cases hbc
        exact i
    | tau => exact p.elim
  invFun j := ⟨(FibObject.unit, c), ⟨⟨(fibAdmB_unit_left c c).mpr rfl⟩,
    PUnit.unit, j⟩⟩
  left_inv x := by
    rcases x with ⟨⟨u, b⟩, ⟨h⟩, p, i⟩
    cases u with
    | unit =>
        have hbc : b = c := (fibAdmB_unit_left b c).mp h
        cases hbc
        rfl
    | tau => exact p.elim
  right_inv _ := rfl

/-- The right unit fusion channel identifies the right tensor index with the
original fiber. -/
private def fibFamRightUnitIndexEquiv (A : FibFam) (c : FibObject) :
    (fibFamTensorObj A fibFamUnit).idx c ≃ A.idx c where
  toFun x := by
    rcases x with ⟨⟨a, u⟩, ⟨h⟩, i, p⟩
    cases u with
    | unit =>
        have hac : a = c := (fibAdmB_unit_right a c).mp h
        cases hac
        exact i
    | tau => exact p.elim
  invFun i := ⟨(c, FibObject.unit), ⟨⟨(fibAdmB_unit_right c c).mpr rfl⟩,
    i, PUnit.unit⟩⟩
  left_inv x := by
    rcases x with ⟨⟨a, u⟩, ⟨h⟩, i, p⟩
    cases u with
    | unit =>
        have hac : a = c := (fibAdmB_unit_right a c).mp h
        cases hac
        rfl
    | tau => exact p.elim
  right_inv _ := rfl

/-- Left unitor `1 ⊗ B ≅ B` in `FibFam`. -/
private def fibFamLeftUnitorEntry (B : FibFam) (c : FibObject) (j : B.idx c)
    (u b : FibObject) (i : B.idx b) : ℂ :=
  match u with
  | .unit => homEntry (𝟙 B) c b j i
  | .tau => 0

def fibFamLeftUnitor (B : FibFam) : fibFamTensorObj fibFamUnit B ≅ B where
  hom c x j' := homEntry (𝟙 B) x.1.2 c x.2.2.2 j'
  inv c j x := fibFamLeftUnitorEntry B c j x.1.1 x.1.2 x.2.2.2
  hom_inv_id := by
    ext c ⟨⟨u, b⟩, ⟨hb⟩, p, i⟩ ⟨⟨u', b'⟩, ⟨hb'⟩, p', i'⟩
    cases u; cases u'
    · change PUnit at p
      change PUnit at p'
      have hp : p = PUnit.unit := Subsingleton.elim _ _
      have hp' : p' = PUnit.unit := Subsingleton.elim _ _
      have hbc : b = c := (fibAdmB_unit_left b c).mp hb
      have hbc' : b' = c := (fibAdmB_unit_left b' c).mp hb'
      subst hp hp'
      subst b
      subst b'
      have hproof : hb = hb' := Subsingleton.elim _ _
      cases hproof
      change (∑ k : B.idx c,
        homEntry (𝟙 B) c c i k * homEntry (𝟙 B) c c k i') =
        if (⟨(FibObject.unit, c), ⟨⟨hb⟩, PUnit.unit, i⟩⟩ :
          (fibFamTensorObj fibFamUnit B).idx c) =
          ⟨(FibObject.unit, c), ⟨⟨hb⟩, PUnit.unit, i'⟩⟩ then 1 else 0
      have h_index :
          (⟨(FibObject.unit, c), ⟨⟨hb⟩, PUnit.unit, i⟩⟩ :
            (fibFamTensorObj fibFamUnit B).idx c) =
          ⟨(FibObject.unit, c), ⟨⟨hb⟩, PUnit.unit, i'⟩⟩ ↔ i = i' := by
        constructor
        · intro h; cases h; rfl
        · rintro rfl; rfl
      simp only [h_index]
      simp only [homEntry_same, FibFam.id_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [hki.symm]
      · intro h; exact (h (Finset.mem_univ i)).elim
    · exact p'.elim
    · exact p.elim
  inv_hom_id := by
    ext c j₁ j₂
    classical
    change (∑ x : (fibFamTensorObj fibFamUnit B).idx c,
        fibFamLeftUnitorEntry B c j₁ x.1.1 x.1.2 x.2.2.2 *
          homEntry (𝟙 B) x.1.2 c x.2.2.2 j₂) = _
    rw [sum_fibFamTensorIdx (A := fibFamUnit) (B := B) (c := c)
      (G := fun (u b : FibObject) (_p : fibFamUnit.idx u) (i : B.idx b) =>
        fibFamLeftUnitorEntry B c j₁ u b i * homEntry (𝟙 B) b c i j₂)]
    rw [sum_fibObject]
    simp only [fibFamLeftUnitorEntry]
    rw [Finset.sum_eq_single c]
    · have huc : FibAdmB .unit c c = true := (fibAdmB_unit_left c c).mpr rfl
      let : Unique (fibFamUnit.idx .unit) := by
        change Unique PUnit
        infer_instance
      rw [ite_eq_left huc, Fintype.sum_unique]
      rw [sum_homEntry_mul]
      simp [homEntry_same, FibFam.id_apply]
    · intro b _ hne
      have hbf : FibAdmB .unit b c = false := by
        cases hval : FibAdmB .unit b c <;> simp_all [fibAdmB_unit_left]
      simp [hbf]
    · intro hm; exact (hm (Finset.mem_univ c)).elim

private def fibFamRightUnitorEntry (A : FibFam) (c : FibObject) (i₁ : A.idx c)
    (a u : FibObject) (i : A.idx a) : ℂ :=
  match u with
  | .unit => homEntry (𝟙 A) c a i₁ i
  | .tau => 0

/-- Right unitor `A ⊗ 1 ≅ A` in `FibFam`. -/
def fibFamRightUnitor (A : FibFam) : fibFamTensorObj A fibFamUnit ≅ A where
  hom c x i' := homEntry (𝟙 A) x.1.1 c x.2.2.1 i'
  inv c i x := fibFamRightUnitorEntry A c i x.1.1 x.1.2 x.2.2.1
  hom_inv_id := by
    ext c ⟨⟨a, u⟩, ⟨ha⟩, i, p⟩ ⟨⟨a', u'⟩, ⟨ha'⟩, i', p'⟩
    cases u; cases u'
    · change PUnit at p
      change PUnit at p'
      have hp : p = PUnit.unit := Subsingleton.elim _ _
      have hp' : p' = PUnit.unit := Subsingleton.elim _ _
      have hac : a = c := (fibAdmB_unit_right a c).mp ha
      have hac' : a' = c := (fibAdmB_unit_right a' c).mp ha'
      subst hp hp'
      subst a
      subst a'
      have hproof : ha = ha' := Subsingleton.elim _ _
      cases hproof
      change (∑ k : A.idx c,
        homEntry (𝟙 A) c c i k * homEntry (𝟙 A) c c k i') =
        if (⟨(c, FibObject.unit), ⟨⟨ha⟩, i, PUnit.unit⟩⟩ :
          (fibFamTensorObj A fibFamUnit).idx c) =
          ⟨(c, FibObject.unit), ⟨⟨ha⟩, i', PUnit.unit⟩⟩ then 1 else 0
      have h_index :
          (⟨(c, FibObject.unit), ⟨⟨ha⟩, i, PUnit.unit⟩⟩ :
            (fibFamTensorObj A fibFamUnit).idx c) =
          ⟨(c, FibObject.unit), ⟨⟨ha⟩, i', PUnit.unit⟩⟩ ↔ i = i' := by
        constructor
        · intro h; cases h; rfl
        · rintro rfl; rfl
      simp only [h_index, homEntry_same, FibFam.id_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [hki.symm]
      · intro h; exact (h (Finset.mem_univ i)).elim
    · exact p'.elim
    · exact p.elim
  inv_hom_id := by
    ext c i₁ i₂
    classical
    change (∑ x : (fibFamTensorObj A fibFamUnit).idx c,
        fibFamRightUnitorEntry A c i₁ x.1.1 x.1.2 x.2.2.1 *
          homEntry (𝟙 A) x.1.1 c x.2.2.1 i₂) = _
    rw [sum_fibFamTensorIdx (A := A) (B := fibFamUnit) (c := c)
      (G := fun (a u : FibObject) (i : A.idx a) (_p : fibFamUnit.idx u) =>
        fibFamRightUnitorEntry A c i₁ a u i * homEntry (𝟙 A) a c i i₂)]
    rw [Finset.sum_eq_single c]
    · have huc : FibAdmB c .unit c = true := (fibAdmB_unit_right c c).mpr rfl
      rw [sum_fibObject]
      simp only [fibFamRightUnitorEntry, zero_mul, Finset.sum_const_zero, ite_self, add_zero]
      rw [ite_eq_left huc]
      let : Unique (fibFamUnit.idx .unit) := by
        change Unique PUnit
        infer_instance
      have hunit : ∀ z : ℂ, (∑ _ : fibFamUnit.idx .unit, z) = z := by
        intro z
        exact Fintype.sum_unique _
      simp_rw [hunit]
      rw [sum_homEntry_mul]
      simp [homEntry_same, FibFam.id_apply]
    · intro a _ hne
      rw [sum_fibObject]
      simp only [fibFamRightUnitorEntry, zero_mul, Finset.sum_const_zero, ite_self, add_zero]
      have haf : FibAdmB a .unit c = false := by
        cases hval : FibAdmB a .unit c <;> simp_all [fibAdmB_unit_right]
      simp [haf]
    · intro hm; exact (hm (Finset.mem_univ c)).elim
private theorem fibFSym_zero_of_adm {a b c d e f : FibObject}
    (h : (FibAdmB a b e && FibAdmB e c d && FibAdmB b c f && FibAdmB a f d) = false) :
    fibFSym a b c d e f = 0 := by
  simp [fibFSym, h]

private theorem fibRSym_zero_of_adm {a b d : FibObject} (h : FibAdmB a b d = false) :
    fibRSym a b d = 0 := by
  simp [fibRSym, h]

/-- Associator `(A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)` weighted by Fibonacci `6j` F-symbols `fibFSym`. -/
def fibFamAssociator (A B C : FibFam) :
    fibFamTensorObj (fibFamTensorObj A B) C ≅ fibFamTensorObj A (fibFamTensorObj B C) where
  hom t
    | ⟨⟨e, c⟩, _, ⟨⟨a, b⟩, _, i, j⟩, k⟩, ⟨⟨a', f⟩, _, i', ⟨⟨b', c'⟩, _, j', k'⟩⟩ =>
      fibFSym a b c t e f *
        homEntry (𝟙 A) a a' i i' * homEntry (𝟙 B) b b' j j' * homEntry (𝟙 C) c c' k k'
  inv t
    | ⟨⟨a', f⟩, _, i', ⟨⟨b', c'⟩, _, j', k'⟩⟩, ⟨⟨e, c⟩, _, ⟨⟨a, b⟩, _, i, j⟩, k⟩ =>
      fibFSym a b c t e f *
        homEntry (𝟙 A) a' a i' i * homEntry (𝟙 B) b' b j' j * homEntry (𝟙 C) c' c k' k
  hom_inv_id := by
    ext t ⟨⟨e, c⟩, ⟨he₂⟩, ⟨⟨a, b⟩, ⟨he₁⟩, i, j⟩, k⟩
      ⟨⟨e', c'⟩, ⟨he'₂⟩, ⟨⟨a', b'⟩, ⟨he'₁⟩, i', j'⟩, k'⟩
    change (∑ x : (fibFamTensorObj A (fibFamTensorObj B C)).idx t,
      (fibFSym a b c t e x.1.2 * homEntry (𝟙 A) a x.1.1 i x.2.2.1 *
          homEntry (𝟙 B) b x.2.2.2.1.1 j x.2.2.2.2.2.1 * homEntry (𝟙 C) c x.2.2.2.1.2 k x.2.2.2.2.2.2) *
        (fibFSym a' b' c' t e' x.1.2 * homEntry (𝟙 A) x.1.1 a' x.2.2.1 i' *
          homEntry (𝟙 B) x.2.2.2.1.1 b' x.2.2.2.2.2.1 j' * homEntry (𝟙 C) x.2.2.2.1.2 c' x.2.2.2.2.2.2 k')) = _
    rw [sum_fibFamTensorIdx (A := A) (B := fibFamTensorObj B C) (c := t)
      (G := fun a'' f i'' yz =>
      (fibFSym a b c t e f * homEntry (𝟙 A) a a'' i i'' *
          homEntry (𝟙 B) b yz.1.1 j yz.2.2.1 * homEntry (𝟙 C) c yz.1.2 k yz.2.2.2) *
        (fibFSym a' b' c' t e' f * homEntry (𝟙 A) a'' a' i'' i' *
          homEntry (𝟙 B) yz.1.1 b' yz.2.2.1 j' * homEntry (𝟙 C) yz.1.2 c' yz.2.2.2 k'))]
    have hinner : ∀ a'' f (i'' : A.idx a''),
        (∑ yz : (fibFamTensorObj B C).idx f,
          (fibFSym a b c t e f * homEntry (𝟙 A) a a'' i i'' *
              homEntry (𝟙 B) b yz.1.1 j yz.2.2.1 * homEntry (𝟙 C) c yz.1.2 k yz.2.2.2) *
            (fibFSym a' b' c' t e' f * homEntry (𝟙 A) a'' a' i'' i' *
              homEntry (𝟙 B) yz.1.1 b' yz.2.2.1 j' * homEntry (𝟙 C) yz.1.2 c' yz.2.2.2 k')) =
          (fibFSym a b c t e f * fibFSym a' b' c' t e' f *
            (homEntry (𝟙 A) a a'' i i'' * homEntry (𝟙 A) a'' a' i'' i')) *
          ∑ b'' : FibObject, ∑ c'' : FibObject,
            if FibAdmB b'' c'' f = true then
              (∑ j'' : B.idx b'', homEntry (𝟙 B) b b'' j j'' * homEntry (𝟙 B) b'' b' j'' j') *
              (∑ k'' : C.idx c'', homEntry (𝟙 C) c c'' k k'' * homEntry (𝟙 C) c'' c' k'' k')
            else 0 := by
      intro a'' f i''
      rw [sum_fibFamTensorIdx (A := B) (B := C) (c := f) (G := fun b'' c'' j'' k'' =>
        (fibFSym a b c t e f * homEntry (𝟙 A) a a'' i i'' *
            homEntry (𝟙 B) b b'' j j'' * homEntry (𝟙 C) c c'' k k'') *
          (fibFSym a' b' c' t e' f * homEntry (𝟙 A) a'' a' i'' i' *
            homEntry (𝟙 B) b'' b' j'' j' * homEntry (𝟙 C) c'' c' k'' k'))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b'' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c'' _ => ?_
      split_ifs with hbc
      · rw [Finset.sum_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j'' _ => ?_
        rw [← mul_assoc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k'' _ => ?_
        ring
      · ring
    simp_rw [hinner]
    by_cases ha : a = a' <;> by_cases hb : b = b' <;> by_cases hc : c = c'
    · subst ha hb hc
      have hcoll : (∑ a'' : FibObject, ∑ f : FibObject,
          if FibAdmB a'' f t = true then
            ∑ i'' : A.idx a'',
              (fibFSym a b c t e f * fibFSym a b c t e' f *
                  (homEntry (𝟙 A) a a'' i i'' * homEntry (𝟙 A) a'' a i'' i')) *
                ∑ b'' : FibObject, ∑ c'' : FibObject,
                  if FibAdmB b'' c'' f = true then
                    (∑ j'' : B.idx b'', homEntry (𝟙 B) b b'' j j'' * homEntry (𝟙 B) b'' b j'' j') *
                    (∑ k'' : C.idx c'', homEntry (𝟙 C) c c'' k k'' * homEntry (𝟙 C) c'' c k'' k')
                  else 0
          else 0) =
        (∑ f : FibObject, fibFSym a b c t e f * fibFSym a b c t e' f) *
          (homEntry (𝟙 A) a a i i' * homEntry (𝟙 B) b b j j' * homEntry (𝟙 C) c c k k') := by
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.sum_eq_single b]
          · rw [Finset.sum_eq_single c]
            · simp only [sum_homEntry_id_left, ite_true]
              by_cases h1 : FibAdmB a f t = true <;> by_cases h2 : FibAdmB b c f = true
              · simp only [h1, h2, ↓reduceIte]
                have hAi : (∑ i'' : A.idx a,
                    fibFSym a b c t e f * fibFSym a b c t e' f *
                      (homEntry (𝟙 A) a a i i'' * homEntry (𝟙 A) a a i'' i') *
                      (homEntry (𝟙 B) b b j j' * homEntry (𝟙 C) c c k k')) =
                    fibFSym a b c t e f * fibFSym a b c t e' f *
                      ((∑ i'' : A.idx a, homEntry (𝟙 A) a a i i'' * homEntry (𝟙 A) a a i'' i') *
                        (homEntry (𝟙 B) b b j j' * homEntry (𝟙 C) c c k k')) := by
                  calc (∑ i'' : A.idx a,
                        fibFSym a b c t e f * fibFSym a b c t e' f *
                          (homEntry (𝟙 A) a a i i'' * homEntry (𝟙 A) a a i'' i') *
                          (homEntry (𝟙 B) b b j j' * homEntry (𝟙 C) c c k k'))
                    = ∑ i'' : A.idx a, (homEntry (𝟙 A) a a i i'' * homEntry (𝟙 A) a a i'' i') *
                        (fibFSym a b c t e f * fibFSym a b c t e' f *
                          (homEntry (𝟙 B) b b j j' * homEntry (𝟙 C) c c k k')) := by
                        refine Finset.sum_congr rfl fun i'' _ => by ring
                    _ = (∑ i'' : A.idx a, homEntry (𝟙 A) a a i i'' * homEntry (𝟙 A) a a i'' i') *
                        (fibFSym a b c t e f * fibFSym a b c t e' f *
                          (homEntry (𝟙 B) b b j j' * homEntry (𝟙 C) c c k k')) := by
                        rw [Finset.sum_mul]
                    _ = fibFSym a b c t e f * fibFSym a b c t e' f *
                        ((∑ i'' : A.idx a, homEntry (𝟙 A) a a i i'' * homEntry (𝟙 A) a a i'' i') *
                          (homEntry (𝟙 B) b b j j' * homEntry (𝟙 C) c c k k')) := by ring
                rw [hAi]
                simp only [sum_homEntry_id_left, ite_true]
                ring
              · have hz : fibFSym a b c t e f = 0 := fibFSym_zero_of_adm (by simp [h1, h2])
                simp [h1, h2, hz]
              · have hz : fibFSym a b c t e f = 0 := fibFSym_zero_of_adm (by simp [h1])
                simp [h1, hz]
              · have hz : fibFSym a b c t e f = 0 := fibFSym_zero_of_adm (by simp [h1])
                simp [h1, hz]
            · intro c'' _ hne; split_ifs <;> simp [sum_homEntry_id_left, hne.symm]
            · intro hm; exact (hm (Finset.mem_univ c)).elim
          · intro b'' _ hne
            refine Finset.sum_eq_zero fun c'' _ => ?_
            split_ifs <;> simp [sum_homEntry_id_left, hne.symm]
          · intro hm; exact (hm (Finset.mem_univ b)).elim
        · intro a'' _ hne
          simp [homEntry_ne _ hne.symm]
        · intro hm; exact (hm (Finset.mem_univ a)).elim
      rw [hcoll, fibFSym_orthog_left a b c t e e' he₁ he₂ he'₁ he'₂]
      simp only [homEntry_same, FibFam.id_apply]
      by_cases hee : e = e' <;> by_cases hii : i = i' <;> by_cases hjj : j = j' <;> by_cases hkk : k = k'
      · subst hee hii hjj hkk
        have heq₂ : he₂ = he'₂ := Subsingleton.elim _ _
        have heq₁ : he₁ = he'₁ := Subsingleton.elim _ _
        subst heq₂ heq₁
        simp
      · have hne : (⟨(e, c), ({ down := he₂ }, ⟨(a, b), ({ down := he₁ }, i, j)⟩, k)⟩ : (fibFamTensorObj (fibFamTensorObj A B) C).idx t) ≠
            ⟨(e', c), ({ down := he'₂ }, ⟨(a, b), ({ down := he'₁ }, i', j')⟩, k')⟩ := by
          intro h; cases h; exact hkk rfl
        simp [hkk, hne]
      · have hne : (⟨(e, c), ({ down := he₂ }, ⟨(a, b), ({ down := he₁ }, i, j)⟩, k)⟩ : (fibFamTensorObj (fibFamTensorObj A B) C).idx t) ≠
            ⟨(e', c), ({ down := he'₂ }, ⟨(a, b), ({ down := he'₁ }, i', j')⟩, k')⟩ := by
          intro h; cases h; exact hjj rfl
        simp [hjj, hne]
      · have hne : (⟨(e, c), ({ down := he₂ }, ⟨(a, b), ({ down := he₁ }, i, j)⟩, k)⟩ : (fibFamTensorObj (fibFamTensorObj A B) C).idx t) ≠
            ⟨(e', c), ({ down := he'₂ }, ⟨(a, b), ({ down := he'₁ }, i', j')⟩, k')⟩ := by
          intro h; cases h; exact hjj rfl
        simp [hjj, hne]
      · have hne : (⟨(e, c), ({ down := he₂ }, ⟨(a, b), ({ down := he₁ }, i, j)⟩, k)⟩ : (fibFamTensorObj (fibFamTensorObj A B) C).idx t) ≠
            ⟨(e', c), ({ down := he'₂ }, ⟨(a, b), ({ down := he'₁ }, i', j')⟩, k')⟩ := by
          intro h; cases h; exact hii rfl
        simp [hii, hne]
      · have hne : (⟨(e, c), ({ down := he₂ }, ⟨(a, b), ({ down := he₁ }, i, j)⟩, k)⟩ : (fibFamTensorObj (fibFamTensorObj A B) C).idx t) ≠
            ⟨(e', c), ({ down := he'₂ }, ⟨(a, b), ({ down := he'₁ }, i', j')⟩, k')⟩ := by
          intro h; cases h; exact hii rfl
        simp [hii, hne]
      · have hne : (⟨(e, c), ({ down := he₂ }, ⟨(a, b), ({ down := he₁ }, i, j)⟩, k)⟩ : (fibFamTensorObj (fibFamTensorObj A B) C).idx t) ≠
            ⟨(e', c), ({ down := he'₂ }, ⟨(a, b), ({ down := he'₁ }, i', j')⟩, k')⟩ := by
          intro h; cases h; exact hii rfl
        simp [hii, hne]
      · have hne : (⟨(e, c), ({ down := he₂ }, ⟨(a, b), ({ down := he₁ }, i, j)⟩, k)⟩ : (fibFamTensorObj (fibFamTensorObj A B) C).idx t) ≠
            ⟨(e', c), ({ down := he'₂ }, ⟨(a, b), ({ down := he'₁ }, i', j')⟩, k')⟩ := by
          intro h; cases h; exact hii rfl
        simp [hii, hne]
      · have hne : (⟨(e, c), ({ down := he₂ }, ⟨(a, b), ({ down := he₁ }, i, j)⟩, k)⟩ : (fibFamTensorObj (fibFamTensorObj A B) C).idx t) ≠
            ⟨(e', c), ({ down := he'₂ }, ⟨(a, b), ({ down := he'₁ }, i', j')⟩, k')⟩ := by
          intro h; cases h; exact hee rfl
        simp [hee, hne]
      all_goals
        have hne : (⟨(e, c), ({ down := he₂ }, ⟨(a, b), ({ down := he₁ }, i, j)⟩, k)⟩ : (fibFamTensorObj (fibFamTensorObj A B) C).idx t) ≠
            ⟨(e', c), ({ down := he'₂ }, ⟨(a, b), ({ down := he'₁ }, i', j')⟩, k')⟩ := by
          intro h; cases h; exact hee rfl
        simp [hee, hne]
    all_goals
      have hzero : (∑ a'' : FibObject, ∑ f : FibObject,
          if FibAdmB a'' f t = true then
            ∑ i'' : A.idx a'',
              (fibFSym a b c t e f * fibFSym a' b' c' t e' f *
                  (homEntry (𝟙 A) a a'' i i'' * homEntry (𝟙 A) a'' a' i'' i')) *
                ∑ b'' : FibObject, ∑ c'' : FibObject,
                  if FibAdmB b'' c'' f = true then
                    (∑ j'' : B.idx b'', homEntry (𝟙 B) b b'' j j'' * homEntry (𝟙 B) b'' b' j'' j') *
                    (∑ k'' : C.idx c'', homEntry (𝟙 C) c c'' k k'' * homEntry (𝟙 C) c'' c' k'' k')
                  else 0
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun a'' _ => Finset.sum_eq_zero fun f _ => ?_
        split_ifs with hf
        · refine Finset.sum_eq_zero fun i'' _ => ?_
          by_cases ha1 : a = a''
          · by_cases ha2 : a'' = a'
            · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b'' _ =>
                Finset.sum_eq_zero fun c'' _ => ?_)
              split_ifs with hbc
              · by_cases hb1 : b = b''
                · by_cases hb2 : b'' = b'
                  · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k'' _ => ?_)
                    by_cases hc1 : c = c''
                    · by_cases hc2 : c'' = c'
                      · first
                        | exact (ha (ha1.trans ha2)).elim
                        | exact (hb (hb1.trans hb2)).elim
                        | exact (hc (hc1.trans hc2)).elim
                      · simp [homEntry_ne _ hc2]
                    · simp [homEntry_ne _ hc1]
                  · exact mul_eq_zero_of_left (Finset.sum_eq_zero fun _ _ => by simp [homEntry_ne _ hb2]) _
                · exact mul_eq_zero_of_left (Finset.sum_eq_zero fun _ _ => by simp [homEntry_ne _ hb1]) _
              · rfl
            · exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (by simp [homEntry_ne _ ha2])) _
          · exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (by simp [homEntry_ne _ ha1])) _
        · rfl
      rw [hzero]
      simp only [FibFam.id_apply]
      split_ifs with heq
      · cases heq; exact absurd rfl (by assumption)
      · rfl
  inv_hom_id := by
    ext t ⟨⟨a', f⟩, ⟨hf₂⟩, i', ⟨⟨b', c'⟩, ⟨hf₁⟩, j', k'⟩⟩
      ⟨⟨a'', f'⟩, ⟨hf'₂⟩, i'', ⟨⟨b'', c''⟩, ⟨hf'₁⟩, j'', k''⟩⟩
    change (∑ x : (fibFamTensorObj (fibFamTensorObj A B) C).idx t,
      (fibFSym x.2.2.1.1.1 x.2.2.1.1.2 x.1.2 t x.1.1 f *
          homEntry (𝟙 A) a' x.2.2.1.1.1 i' x.2.2.1.2.2.1 *
          homEntry (𝟙 B) b' x.2.2.1.1.2 j' x.2.2.1.2.2.2 * homEntry (𝟙 C) c' x.1.2 k' x.2.2.2) *
        (fibFSym x.2.2.1.1.1 x.2.2.1.1.2 x.1.2 t x.1.1 f' *
          homEntry (𝟙 A) x.2.2.1.1.1 a'' x.2.2.1.2.2.1 i'' *
          homEntry (𝟙 B) x.2.2.1.1.2 b'' x.2.2.1.2.2.2 j'' * homEntry (𝟙 C) x.1.2 c'' x.2.2.2 k'')) = _
    rw [sum_fibFamTensorIdx (A := fibFamTensorObj A B) (B := C) (c := t)
      (G := fun e c xy k =>
      (fibFSym xy.1.1 xy.1.2 c t e f * homEntry (𝟙 A) a' xy.1.1 i' xy.2.2.1 *
          homEntry (𝟙 B) b' xy.1.2 j' xy.2.2.2 * homEntry (𝟙 C) c' c k' k) *
        (fibFSym xy.1.1 xy.1.2 c t e f' * homEntry (𝟙 A) xy.1.1 a'' xy.2.2.1 i'' *
          homEntry (𝟙 B) xy.1.2 b'' xy.2.2.2 j'' * homEntry (𝟙 C) c c'' k k''))]
    have hinner : ∀ e c (k : C.idx c),
        (∑ xy : (fibFamTensorObj A B).idx e,
          (fibFSym xy.1.1 xy.1.2 c t e f * homEntry (𝟙 A) a' xy.1.1 i' xy.2.2.1 *
              homEntry (𝟙 B) b' xy.1.2 j' xy.2.2.2 * homEntry (𝟙 C) c' c k' k) *
            (fibFSym xy.1.1 xy.1.2 c t e f' * homEntry (𝟙 A) xy.1.1 a'' xy.2.2.1 i'' *
              homEntry (𝟙 B) xy.1.2 b'' xy.2.2.2 j'' * homEntry (𝟙 C) c c'' k k'')) =
          (homEntry (𝟙 C) c' c k' k * homEntry (𝟙 C) c c'' k k'') *
            ∑ a : FibObject, ∑ b : FibObject,
              if FibAdmB a b e = true then
                fibFSym a b c t e f * fibFSym a b c t e f' *
                  (∑ i : A.idx a, homEntry (𝟙 A) a' a i' i * homEntry (𝟙 A) a a'' i i'') *
                  (∑ j : B.idx b, homEntry (𝟙 B) b' b j' j * homEntry (𝟙 B) b b'' j j'')
              else 0 := by
      intro e c k
      rw [sum_fibFamTensorIdx (A := A) (B := B) (c := e) (G := fun a b i j =>
        (fibFSym a b c t e f * homEntry (𝟙 A) a' a i' i *
            homEntry (𝟙 B) b' b j' j * homEntry (𝟙 C) c' c k' k) *
          (fibFSym a b c t e f' * homEntry (𝟙 A) a a'' i i'' *
            homEntry (𝟙 B) b b'' j j'' * homEntry (𝟙 C) c c'' k k''))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with hab
      · simp only [Finset.mul_sum, Finset.sum_mul]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      · rw [mul_zero]
    have hswap : ∀ (e c : FibObject),
        (∑ xy : (fibFamTensorObj A B).idx e, ∑ k : C.idx c,
          (fibFSym xy.1.1 xy.1.2 c t e f * homEntry (𝟙 A) a' xy.1.1 i' xy.2.2.1 *
              homEntry (𝟙 B) b' xy.1.2 j' xy.2.2.2 * homEntry (𝟙 C) c' c k' k) *
            (fibFSym xy.1.1 xy.1.2 c t e f' * homEntry (𝟙 A) xy.1.1 a'' xy.2.2.1 i'' *
              homEntry (𝟙 B) xy.1.2 b'' xy.2.2.2 j'' * homEntry (𝟙 C) c c'' k k'')) =
        ∑ k : C.idx c, ∑ xy : (fibFamTensorObj A B).idx e,
          (fibFSym xy.1.1 xy.1.2 c t e f * homEntry (𝟙 A) a' xy.1.1 i' xy.2.2.1 *
              homEntry (𝟙 B) b' xy.1.2 j' xy.2.2.2 * homEntry (𝟙 C) c' c k' k) *
            (fibFSym xy.1.1 xy.1.2 c t e f' * homEntry (𝟙 A) xy.1.1 a'' xy.2.2.1 i'' *
              homEntry (𝟙 B) xy.1.2 b'' xy.2.2.2 j'' * homEntry (𝟙 C) c c'' k k'') := by
      intro e c
      exact Finset.sum_comm
    simp_rw [hswap, hinner]
    by_cases ha : a' = a'' <;> by_cases hb : b' = b'' <;> by_cases hc : c' = c''
    · subst ha hb hc
      have hcoll : (∑ e : FibObject, ∑ c : FibObject,
          if FibAdmB e c t = true then
            ∑ k : C.idx c,
              (homEntry (𝟙 C) c' c k' k * homEntry (𝟙 C) c c' k k'') *
                ∑ a : FibObject, ∑ b : FibObject,
                  if FibAdmB a b e = true then
                    fibFSym a b c t e f * fibFSym a b c t e f' *
                      (∑ i : A.idx a, homEntry (𝟙 A) a' a i' i * homEntry (𝟙 A) a a' i i'') *
                      (∑ j : B.idx b, homEntry (𝟙 B) b' b j' j * homEntry (𝟙 B) b b' j j'')
                  else 0
          else 0) =
        (∑ e : FibObject, fibFSym a' b' c' t e f * fibFSym a' b' c' t e f') *
          (homEntry (𝟙 A) a' a' i' i'' * homEntry (𝟙 B) b' b' j' j'' * homEntry (𝟙 C) c' c' k' k'') := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_eq_single c']
        · rw [Finset.sum_eq_single a']
          · rw [Finset.sum_eq_single b']
            · simp only [sum_homEntry_id_left, ite_true]
              by_cases h1 : FibAdmB e c' t = true <;> by_cases h2 : FibAdmB a' b' e = true
              · simp only [h1, h2, ↓reduceIte]
                have hCk : (∑ k : C.idx c',
                    homEntry (𝟙 C) c' c' k' k * homEntry (𝟙 C) c' c' k k'' *
                      (fibFSym a' b' c' t e f * fibFSym a' b' c' t e f' *
                        homEntry (𝟙 A) a' a' i' i'' * homEntry (𝟙 B) b' b' j' j'')) =
                    (∑ k : C.idx c', homEntry (𝟙 C) c' c' k' k * homEntry (𝟙 C) c' c' k k'') *
                      (fibFSym a' b' c' t e f * fibFSym a' b' c' t e f' *
                        homEntry (𝟙 A) a' a' i' i'' * homEntry (𝟙 B) b' b' j' j'') := by
                  rw [Finset.sum_mul]
                rw [hCk]
                simp only [sum_homEntry_id_left, ite_true]
                ring
              · have hz : fibFSym a' b' c' t e f = 0 := fibFSym_zero_of_adm (by simp [h1, h2])
                simp [h1, h2, hz]
              · have hz : fibFSym a' b' c' t e f = 0 := fibFSym_zero_of_adm (by simp [h1])
                simp [h1, hz]
              · have hz : fibFSym a' b' c' t e f = 0 := fibFSym_zero_of_adm (by simp [h1])
                simp [h1, hz]
            · intro b _ hne
              split_ifs with h3
              · simp [sum_homEntry_id_left, hne.symm]
              · rfl
            · intro hm; exact (hm (Finset.mem_univ b')).elim
          · intro a _ hne
            simp [homEntry_ne _ hne.symm]
          · intro hm; exact (hm (Finset.mem_univ a')).elim
        · intro c _ hne
          simp [homEntry_ne _ hne.symm]
        · intro hm; exact (hm (Finset.mem_univ c')).elim
      rw [hcoll, fibFSym_orthog_right a' b' c' t f f' hf₁ hf₂ hf'₁ hf'₂]
      simp only [homEntry_same, FibFam.id_apply]
      by_cases hff : f = f' <;> by_cases hii : i' = i'' <;> by_cases hjj : j' = j'' <;> by_cases hkk : k' = k''
      · subst hff hii hjj hkk
        have heq₂ : hf₂ = hf'₂ := Subsingleton.elim _ _
        have heq₁ : hf₁ = hf'₁ := Subsingleton.elim _ _
        subst heq₂ heq₁
        simp
      · have hne : (⟨(a', f), ({ down := hf₂ }, i', ⟨(b', c'), ({ down := hf₁ }, j', k')⟩)⟩ : (fibFamTensorObj A (fibFamTensorObj B C)).idx t) ≠
            ⟨(a', f'), ({ down := hf'₂ }, i'', ⟨(b', c'), ({ down := hf'₁ }, j'', k'')⟩)⟩ := by
          intro h; cases h; exact hkk rfl
        simp [hkk, hne]
      · have hne : (⟨(a', f), ({ down := hf₂ }, i', ⟨(b', c'), ({ down := hf₁ }, j', k')⟩)⟩ : (fibFamTensorObj A (fibFamTensorObj B C)).idx t) ≠
            ⟨(a', f'), ({ down := hf'₂ }, i'', ⟨(b', c'), ({ down := hf'₁ }, j'', k'')⟩)⟩ := by
          intro h; cases h; exact hjj rfl
        simp [hjj, hne]
      · have hne : (⟨(a', f), ({ down := hf₂ }, i', ⟨(b', c'), ({ down := hf₁ }, j', k')⟩)⟩ : (fibFamTensorObj A (fibFamTensorObj B C)).idx t) ≠
            ⟨(a', f'), ({ down := hf'₂ }, i'', ⟨(b', c'), ({ down := hf'₁ }, j'', k'')⟩)⟩ := by
          intro h; cases h; exact hjj rfl
        simp [hjj, hne]
      · have hne : (⟨(a', f), ({ down := hf₂ }, i', ⟨(b', c'), ({ down := hf₁ }, j', k')⟩)⟩ : (fibFamTensorObj A (fibFamTensorObj B C)).idx t) ≠
            ⟨(a', f'), ({ down := hf'₂ }, i'', ⟨(b', c'), ({ down := hf'₁ }, j'', k'')⟩)⟩ := by
          intro h; cases h; exact hii rfl
        simp [hii, hne]
      · have hne : (⟨(a', f), ({ down := hf₂ }, i', ⟨(b', c'), ({ down := hf₁ }, j', k')⟩)⟩ : (fibFamTensorObj A (fibFamTensorObj B C)).idx t) ≠
            ⟨(a', f'), ({ down := hf'₂ }, i'', ⟨(b', c'), ({ down := hf'₁ }, j'', k'')⟩)⟩ := by
          intro h; cases h; exact hii rfl
        simp [hii, hne]
      · have hne : (⟨(a', f), ({ down := hf₂ }, i', ⟨(b', c'), ({ down := hf₁ }, j', k')⟩)⟩ : (fibFamTensorObj A (fibFamTensorObj B C)).idx t) ≠
            ⟨(a', f'), ({ down := hf'₂ }, i'', ⟨(b', c'), ({ down := hf'₁ }, j'', k'')⟩)⟩ := by
          intro h; cases h; exact hii rfl
        simp [hii, hne]
      · have hne : (⟨(a', f), ({ down := hf₂ }, i', ⟨(b', c'), ({ down := hf₁ }, j', k')⟩)⟩ : (fibFamTensorObj A (fibFamTensorObj B C)).idx t) ≠
            ⟨(a', f'), ({ down := hf'₂ }, i'', ⟨(b', c'), ({ down := hf'₁ }, j'', k'')⟩)⟩ := by
          intro h; cases h; exact hii rfl
        simp [hii, hne]
      · have hne : (⟨(a', f), ({ down := hf₂ }, i', ⟨(b', c'), ({ down := hf₁ }, j', k')⟩)⟩ : (fibFamTensorObj A (fibFamTensorObj B C)).idx t) ≠
            ⟨(a', f'), ({ down := hf'₂ }, i'', ⟨(b', c'), ({ down := hf'₁ }, j'', k'')⟩)⟩ := by
          intro h; cases h; exact hff rfl
        simp [hff, hne]
      all_goals
        have hne : (⟨(a', f), ({ down := hf₂ }, i', ⟨(b', c'), ({ down := hf₁ }, j', k')⟩)⟩ : (fibFamTensorObj A (fibFamTensorObj B C)).idx t) ≠
            ⟨(a', f'), ({ down := hf'₂ }, i'', ⟨(b', c'), ({ down := hf'₁ }, j'', k'')⟩)⟩ := by
          intro h; cases h; exact hff rfl
        simp [hff, hne]
    all_goals
      have hzero : (∑ e : FibObject, ∑ c : FibObject,
          if FibAdmB e c t = true then
            ∑ k : C.idx c,
              (homEntry (𝟙 C) c' c k' k * homEntry (𝟙 C) c c'' k k'') *
                ∑ a : FibObject, ∑ b : FibObject,
                  if FibAdmB a b e = true then
                    fibFSym a b c t e f * fibFSym a b c t e f' *
                      (∑ i : A.idx a, homEntry (𝟙 A) a' a i' i * homEntry (𝟙 A) a a'' i i'') *
                      (∑ j : B.idx b, homEntry (𝟙 B) b' b j' j * homEntry (𝟙 B) b b'' j j'')
                  else 0
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun c _ => ?_
        split_ifs with hec
        · refine Finset.sum_eq_zero fun k _ => ?_
          by_cases hc1 : c' = c
          · by_cases hc2 : c = c''
            · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun a _ =>
                Finset.sum_eq_zero fun b _ => ?_)
              split_ifs with hab
              · by_cases ha1 : a' = a
                · by_cases ha2 : a = a''
                  · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
                    by_cases hb1 : b' = b
                    · by_cases hb2 : b = b''
                      · first
                        | exact (ha (ha1.trans ha2)).elim
                        | exact (hb (hb1.trans hb2)).elim
                        | exact (hc (hc1.trans hc2)).elim
                      · simp [homEntry_ne _ hb2]
                    · simp [homEntry_ne _ hb1]
                  · exact mul_eq_zero_of_left (mul_eq_zero_of_right _
                      (Finset.sum_eq_zero fun _ _ => by simp [homEntry_ne _ ha2])) _
                · exact mul_eq_zero_of_left (mul_eq_zero_of_right _
                    (Finset.sum_eq_zero fun _ _ => by simp [homEntry_ne _ ha1])) _
              · rfl
            · exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (by simp [homEntry_ne _ hc2])) _
          · simp [homEntry_ne _ hc1]
        · rfl
      rw [hzero]
      simp only [FibFam.id_apply]
      split_ifs with heq
      · cases heq; exact absurd rfl (by assumption)
      · rfl

instance : MonoidalCategoryStruct FibFam where
  tensorObj := fibFamTensorObj
  whiskerLeft := fibFamWhiskerLeft
  whiskerRight := fibFamWhiskerRight
  tensorHom := fibFamTensorHom
  tensorUnit := fibFamUnit
  associator := fibFamAssociator
  leftUnitor := fibFamLeftUnitor
  rightUnitor := fibFamRightUnitor

private theorem fibFam_tensorHom_def {X₁ Y₁ X₂ Y₂ : FibFam} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by
  ext c ⟨⟨a₁, b₁⟩, ⟨h₁⟩, i₁, j₁⟩ ⟨⟨a₂, b₂⟩, ⟨h₂⟩, i₂, j₂⟩
  change fibFamTensorHom f g c _ _ =
    (fibFamTensorHom f (𝟙 X₂) ≫ fibFamTensorHom (𝟙 Y₁) g) c _ _
  simp only [fibFamTensorHom, FibFam.comp_apply]
  rw [sum_fibFamTensorIdx (G := fun a' b' i' j' =>
    (homEntry f a₁ a' i₁ i' * homEntry (𝟙 X₂) b₁ b' j₁ j') *
      (homEntry (𝟙 Y₁) a' a₂ i' i₂ * homEntry g b' b₂ j' j₂))]
  have hterm : ∀ a' b',
      (∑ i' : Y₁.idx a', ∑ j' : X₂.idx b',
        (homEntry f a₁ a' i₁ i' * homEntry (𝟙 X₂) b₁ b' j₁ j') *
          (homEntry (𝟙 Y₁) a' a₂ i' i₂ * homEntry g b' b₂ j' j₂)) =
        (∑ i' : Y₁.idx a', homEntry f a₁ a' i₁ i' * homEntry (𝟙 Y₁) a' a₂ i' i₂) *
          (∑ j' : X₂.idx b', homEntry (𝟙 X₂) b₁ b' j₁ j' * homEntry g b' b₂ j' j₂) := by
    intro a' b'
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    ring
  simp_rw [hterm]
  by_cases ha : a₁ = a₂ <;> by_cases hb : b₁ = b₂
  · subst ha hb
    rw [Finset.sum_eq_single a₁]
    · rw [Finset.sum_eq_single b₁]
      · simp [h₁]
      · intro b' _ hne; split_ifs <;> simp [sum_homEntry_id_left, hne.symm]
      · intro hm; exact (hm (Finset.mem_univ b₁)).elim
    · intro a' _ hne
      refine Finset.sum_eq_zero fun b' _ => ?_
      split_ifs <;> simp [sum_homEntry_id_right, hne.symm]
    · intro hm; exact (hm (Finset.mem_univ a₁)).elim
  · have hzero : (∑ a' : FibObject, ∑ b' : FibObject,
        if FibAdmB a' b' c = true then
          (∑ i' : Y₁.idx a', homEntry f a₁ a' i₁ i' * homEntry (𝟙 Y₁) a' a₂ i' i₂) *
            (∑ j' : X₂.idx b', homEntry (𝟙 X₂) b₁ b' j₁ j' * homEntry g b' b₂ j' j₂)
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => ?_
      split_ifs
      · rw [sum_homEntry_id_left]
        split_ifs with hb1
        · subst hb1; simp [homEntry_ne _ hb]
        · simp
      · rfl
    rw [hzero]
    simp [homEntry_ne _ hb]
  · have hzero : (∑ a' : FibObject, ∑ b' : FibObject,
        if FibAdmB a' b' c = true then
          (∑ i' : Y₁.idx a', homEntry f a₁ a' i₁ i' * homEntry (𝟙 Y₁) a' a₂ i' i₂) *
            (∑ j' : X₂.idx b', homEntry (𝟙 X₂) b₁ b' j₁ j' * homEntry g b' b₂ j' j₂)
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => ?_
      split_ifs
      · rw [sum_homEntry_id_right]
        split_ifs with ha1
        · subst ha1; simp [homEntry_ne _ ha]
        · simp
      · rfl
    rw [hzero]
    simp [homEntry_ne _ ha]
  · have hzero : (∑ a' : FibObject, ∑ b' : FibObject,
        if FibAdmB a' b' c = true then
          (∑ i' : Y₁.idx a', homEntry f a₁ a' i₁ i' * homEntry (𝟙 Y₁) a' a₂ i' i₂) *
            (∑ j' : X₂.idx b', homEntry (𝟙 X₂) b₁ b' j₁ j' * homEntry g b' b₂ j' j₂)
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => ?_
      split_ifs
      · rw [sum_homEntry_id_right]
        split_ifs with ha1
        · subst ha1; simp [homEntry_ne _ ha]
        · simp
      · rfl
    rw [hzero]
    simp [homEntry_ne _ ha]

private theorem fibFam_tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : FibFam}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  ext c ⟨⟨a₁, b₁⟩, ⟨h₁⟩, i₁, j₁⟩ ⟨⟨a₃, b₃⟩, ⟨h₃⟩, i₃, j₃⟩
  change (fibFamTensorHom f₁ f₂ ≫ fibFamTensorHom g₁ g₂) c _ _ =
    fibFamTensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) c _ _
  simp only [fibFamTensorHom, FibFam.comp_apply]
  rw [sum_fibFamTensorIdx (G := fun a₂ b₂ i₂ j₂ =>
    (homEntry f₁ a₁ a₂ i₁ i₂ * homEntry f₂ b₁ b₂ j₁ j₂) *
      (homEntry g₁ a₂ a₃ i₂ i₃ * homEntry g₂ b₂ b₃ j₂ j₃))]
  have hterm : ∀ a₂ b₂,
      (∑ i₂ : Y₁.idx a₂, ∑ j₂ : Y₂.idx b₂,
        (homEntry f₁ a₁ a₂ i₁ i₂ * homEntry f₂ b₁ b₂ j₁ j₂) *
          (homEntry g₁ a₂ a₃ i₂ i₃ * homEntry g₂ b₂ b₃ j₂ j₃)) =
        (∑ i₂ : Y₁.idx a₂, homEntry f₁ a₁ a₂ i₁ i₂ * homEntry g₁ a₂ a₃ i₂ i₃) *
          (∑ j₂ : Y₂.idx b₂, homEntry f₂ b₁ b₂ j₁ j₂ * homEntry g₂ b₂ b₃ j₂ j₃) := by
    intro a₂ b₂
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i₂ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    ring
  simp_rw [hterm]
  by_cases ha : a₁ = a₃ <;> by_cases hb : b₁ = b₃
  · subst ha hb
    rw [Finset.sum_eq_single a₁]
    · rw [Finset.sum_eq_single b₁]
      · simp [h₁]
      · intro b₂ _ hne; split_ifs <;> simp [sum_homEntry_mul, hne.symm]
      · intro hm; exact (hm (Finset.mem_univ b₁)).elim
    · intro a₂ _ hne
      refine Finset.sum_eq_zero fun b₂ _ => ?_
      split_ifs <;> simp [sum_homEntry_mul, hne.symm]
    · intro hm; exact (hm (Finset.mem_univ a₁)).elim
  · have hzero : (∑ a₂ : FibObject, ∑ b₂ : FibObject,
        if FibAdmB a₂ b₂ c = true then
          (∑ i₂ : Y₁.idx a₂, homEntry f₁ a₁ a₂ i₁ i₂ * homEntry g₁ a₂ a₃ i₂ i₃) *
            (∑ j₂ : Y₂.idx b₂, homEntry f₂ b₁ b₂ j₁ j₂ * homEntry g₂ b₂ b₃ j₂ j₃)
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun a₂ _ => Finset.sum_eq_zero fun b₂ _ => ?_
      split_ifs
      · simp only [sum_homEntry_mul]
        split_ifs <;> simp_all [homEntry_ne]
      · rfl
    rw [hzero]
    simp [homEntry_ne _ hb]
  · have hzero : (∑ a₂ : FibObject, ∑ b₂ : FibObject,
        if FibAdmB a₂ b₂ c = true then
          (∑ i₂ : Y₁.idx a₂, homEntry f₁ a₁ a₂ i₁ i₂ * homEntry g₁ a₂ a₃ i₂ i₃) *
            (∑ j₂ : Y₂.idx b₂, homEntry f₂ b₁ b₂ j₁ j₂ * homEntry g₂ b₂ b₃ j₂ j₃)
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun a₂ _ => Finset.sum_eq_zero fun b₂ _ => ?_
      split_ifs
      · rw [sum_homEntry_mul]
        split_ifs with ha1
        · subst ha1; simp [homEntry_ne _ ha]
        · simp
      · rfl
    rw [hzero]
    simp [homEntry_ne _ ha]
  · have hzero : (∑ a₂ : FibObject, ∑ b₂ : FibObject,
        if FibAdmB a₂ b₂ c = true then
          (∑ i₂ : Y₁.idx a₂, homEntry f₁ a₁ a₂ i₁ i₂ * homEntry g₁ a₂ a₃ i₂ i₃) *
            (∑ j₂ : Y₂.idx b₂, homEntry f₂ b₁ b₂ j₁ j₂ * homEntry g₂ b₂ b₃ j₂ j₃)
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun a₂ _ => Finset.sum_eq_zero fun b₂ _ => ?_
      split_ifs
      · rw [sum_homEntry_mul]
        split_ifs with ha1
        · subst ha1; simp [homEntry_ne _ ha]
        · simp
      · rfl
    rw [hzero]
    simp [homEntry_ne _ ha]

@[simp] theorem homEntry_tensor_same {A₁ A₂ B₁ B₂ : FibFam}
    (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (c : FibObject)
    (x : (fibFamTensorObj A₁ B₁).idx c) (y : (fibFamTensorObj A₂ B₂).idx c) :
    homEntry (fibFamTensorHom f g) c c x y =
      homEntry f x.1.1 y.1.1 x.2.2.1 y.2.2.1 * homEntry g x.1.2 y.1.2 x.2.2.2 y.2.2.2 := by
  rcases x with ⟨⟨a₁, b₁⟩, _, i₁, j₁⟩
  rcases y with ⟨⟨a₂, b₂⟩, _, i₂, j₂⟩
  simp [homEntry_same, fibFamTensorHom]

private theorem sum_fib_homEntry_id_left {A : FibFam} (s₁ : FibObject) (i₁ : A.idx s₁)
    (G : ∀ s₂ : FibObject, A.idx s₂ → ℂ) :
    (∑ s₂ : FibObject, ∑ i₂ : A.idx s₂, homEntry (𝟙 A) s₁ s₂ i₁ i₂ * G s₂ i₂) = G s₁ i₁ := by
  rw [Finset.sum_eq_single s₁]
  · simp [homEntry_same, FibFam.id_apply]
  · intro s₂ _ hne; simp [homEntry_ne _ hne.symm]
  · intro hm; exact (hm (Finset.mem_univ s₁)).elim

private theorem sum_fib_homEntry_id_right {A : FibFam} (s₂ : FibObject) (i₂ : A.idx s₂)
    (G : ∀ s₁ : FibObject, A.idx s₁ → ℂ) :
    (∑ s₁ : FibObject, ∑ i₁ : A.idx s₁, G s₁ i₁ * homEntry (𝟙 A) s₁ s₂ i₁ i₂) = G s₂ i₂ := by
  rw [Finset.sum_eq_single s₂]
  · simp [homEntry_same, FibFam.id_apply, eq_comm]
  · intro s₁ _ hne; simp [homEntry_ne _ hne]
  · intro hm; exact (hm (Finset.mem_univ s₂)).elim

private theorem sum_homEntry_mul_id_eq_zero {A B : FibFam} (f : A ⟶ B) {s₁ s₃ : FibObject}
    (h : s₁ ≠ s₃) (s₂ : FibObject) (i₁ : A.idx s₁) (i₃ : B.idx s₃) :
    (∑ i₂ : B.idx s₂, homEntry f s₁ s₂ i₁ i₂ * homEntry (𝟙 B) s₂ s₃ i₂ i₃) = 0 := by
  rw [sum_homEntry_id_right, homEntry_ne _ h, ite_self]

private theorem sum_id_mul_homEntry_eq_zero {A B : FibFam} (g : A ⟶ B) {s₁ s₃ : FibObject}
    (h : s₁ ≠ s₃) (s₂ : FibObject) (i₁ : A.idx s₁) (i₃ : B.idx s₃) :
    (∑ i₂ : A.idx s₂, homEntry (𝟙 A) s₁ s₂ i₁ i₂ * homEntry g s₂ s₃ i₂ i₃) = 0 := by
  rw [sum_homEntry_id_left, homEntry_ne _ h, ite_self]

private theorem fibFam_id_tensorHom_id (X₁ X₂ : FibFam) :
    𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂) := by
  ext c x y
  exact tensorIdx_id_eq x y

private theorem fibFam_whiskerLeft_id (X Y : FibFam) :
    X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) :=
  fibFam_id_tensorHom_id X Y

private theorem fibFam_id_whiskerRight (X Y : FibFam) :
    𝟙 X ▷ Y = 𝟙 (X ⊗ Y) :=
  fibFam_id_tensorHom_id X Y

private theorem fibFam_associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : FibFam}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
  ext t ⟨⟨e, c₁⟩, ⟨he₂⟩, ⟨⟨a₁, b₁⟩, ⟨he₁⟩, i₁, j₁⟩, k₁⟩
    ⟨⟨a₂, f⟩, ⟨hf₂⟩, i₂, ⟨⟨b₂, c₂⟩, ⟨hf₁⟩, j₂, k₂⟩⟩
  simp only [FibFam.comp_apply]
  change (∑ z : (fibFamTensorObj (fibFamTensorObj Y₁ Y₂) Y₃).idx t,
      (homEntry (fibFamTensorHom f₁ f₂) e z.1.1 ⟨⟨a₁, b₁⟩, ⟨he₁⟩, i₁, j₁⟩ z.2.2.1 *
        homEntry f₃ c₁ z.1.2 k₁ z.2.2.2) *
      (fibFSym z.2.2.1.1.1 z.2.2.1.1.2 z.1.2 t z.1.1 f *
        homEntry (𝟙 Y₁) z.2.2.1.1.1 a₂ z.2.2.1.2.2.1 i₂ *
        homEntry (𝟙 Y₂) z.2.2.1.1.2 b₂ z.2.2.1.2.2.2 j₂ *
        homEntry (𝟙 Y₃) z.1.2 c₂ z.2.2.2 k₂)) =
    ∑ w : (fibFamTensorObj X₁ (fibFamTensorObj X₂ X₃)).idx t,
      (fibFSym a₁ b₁ c₁ t e w.1.2 *
        homEntry (𝟙 X₁) a₁ w.1.1 i₁ w.2.2.1 *
        homEntry (𝟙 X₂) b₁ w.2.2.2.1.1 j₁ w.2.2.2.2.2.1 *
        homEntry (𝟙 X₃) c₁ w.2.2.2.1.2 k₁ w.2.2.2.2.2.2) *
      (homEntry f₁ w.1.1 a₂ w.2.2.1 i₂ *
        homEntry (fibFamTensorHom f₂ f₃) w.1.2 f w.2.2.2 ⟨⟨b₂, c₂⟩, ⟨hf₁⟩, j₂, k₂⟩)
  rw [sum_fibFamTensorIdx (A := fibFamTensorObj Y₁ Y₂) (B := Y₃) (c := t)
    (G := fun e' c' xy' k' =>
    (homEntry (fibFamTensorHom f₁ f₂) e e' ⟨⟨a₁, b₁⟩, ⟨he₁⟩, i₁, j₁⟩ xy' *
      homEntry f₃ c₁ c' k₁ k') *
    (fibFSym xy'.1.1 xy'.1.2 c' t e' f *
      homEntry (𝟙 Y₁) xy'.1.1 a₂ xy'.2.2.1 i₂ *
      homEntry (𝟙 Y₂) xy'.1.2 b₂ xy'.2.2.2 j₂ *
      homEntry (𝟙 Y₃) c' c₂ k' k₂))]
  rw [sum_fibFamTensorIdx (A := X₁) (B := fibFamTensorObj X₂ X₃) (c := t)
    (G := fun a' f' i' yz' =>
    (fibFSym a₁ b₁ c₁ t e f' *
      homEntry (𝟙 X₁) a₁ a' i₁ i' *
      homEntry (𝟙 X₂) b₁ yz'.1.1 j₁ yz'.2.2.1 *
      homEntry (𝟙 X₃) c₁ yz'.1.2 k₁ yz'.2.2.2) *
    (homEntry f₁ a' a₂ i' i₂ *
      homEntry (fibFamTensorHom f₂ f₃) f' f yz' ⟨⟨b₂, c₂⟩, ⟨hf₁⟩, j₂, k₂⟩))]
  rw [Finset.sum_eq_single e]
  swap
  · intro e' _ hne
    refine Finset.sum_eq_zero fun c' _ => ?_
    split_ifs <;> simp [homEntry_ne _ hne.symm]
  swap
  · intro hm; exact (hm (Finset.mem_univ e)).elim
  conv_rhs =>
    rw [Finset.sum_congr rfl fun a' _ => Finset.sum_eq_single f (fun f' _ hne => by
      split_ifs <;> simp [homEntry_ne _ hne]) (fun hm => (hm (Finset.mem_univ f)).elim)]
  simp only [homEntry_tensor_same]
  have hL : ∀ c' : FibObject,
      (∑ k' : Y₃.idx c', ∑ xy' : (fibFamTensorObj Y₁ Y₂).idx e,
        (homEntry f₁ a₁ xy'.1.1 i₁ xy'.2.2.1 * homEntry f₂ b₁ xy'.1.2 j₁ xy'.2.2.2 *
          homEntry f₃ c₁ c' k₁ k') *
        (fibFSym xy'.1.1 xy'.1.2 c' t e f *
          homEntry (𝟙 Y₁) xy'.1.1 a₂ xy'.2.2.1 i₂ *
          homEntry (𝟙 Y₂) xy'.1.2 b₂ xy'.2.2.2 j₂ *
          homEntry (𝟙 Y₃) c' c₂ k' k₂)) =
        (∑ k' : Y₃.idx c', homEntry f₃ c₁ c' k₁ k' * homEntry (𝟙 Y₃) c' c₂ k' k₂) *
          ∑ a' : FibObject, ∑ b' : FibObject,
            if FibAdmB a' b' e = true then
              fibFSym a' b' c' t e f *
                (∑ i' : Y₁.idx a', homEntry f₁ a₁ a' i₁ i' * homEntry (𝟙 Y₁) a' a₂ i' i₂) *
                (∑ j' : Y₂.idx b', homEntry f₂ b₁ b' j₁ j' * homEntry (𝟙 Y₂) b' b₂ j' j₂)
            else 0 := by
    intro c'
    conv_lhs =>
      arg 2
      ext k'
      rw [sum_fibFamTensorIdx (A := Y₁) (B := Y₂) (c := e) (G := fun a' b' i' j' =>
        (homEntry f₁ a₁ a' i₁ i' * homEntry f₂ b₁ b' j₁ j' * homEntry f₃ c₁ c' k₁ k') *
          (fibFSym a' b' c' t e f *
            homEntry (𝟙 Y₁) a' a₂ i' i₂ * homEntry (𝟙 Y₂) b' b₂ j' j₂ *
            homEntry (𝟙 Y₃) c' c₂ k' k₂))]
    have hpull : ∀ k' : Y₃.idx c',
        (∑ a' : FibObject, ∑ b' : FibObject,
          if FibAdmB a' b' e = true then
            ∑ i' : Y₁.idx a', ∑ j' : Y₂.idx b',
              (homEntry f₁ a₁ a' i₁ i' * homEntry f₂ b₁ b' j₁ j' * homEntry f₃ c₁ c' k₁ k') *
                (fibFSym a' b' c' t e f *
                  homEntry (𝟙 Y₁) a' a₂ i' i₂ * homEntry (𝟙 Y₂) b' b₂ j' j₂ *
                  homEntry (𝟙 Y₃) c' c₂ k' k₂)
          else 0) =
        (homEntry f₃ c₁ c' k₁ k' * homEntry (𝟙 Y₃) c' c₂ k' k₂) *
          ∑ a' : FibObject, ∑ b' : FibObject,
            if FibAdmB a' b' e = true then
              fibFSym a' b' c' t e f *
                (∑ i' : Y₁.idx a', homEntry f₁ a₁ a' i₁ i' * homEntry (𝟙 Y₁) a' a₂ i' i₂) *
                (∑ j' : Y₂.idx b', homEntry f₂ b₁ b' j₁ j' * homEntry (𝟙 Y₂) b' b₂ j' j₂)
            else 0 := by
      intro k'
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      split_ifs
      · simp only [Finset.mul_sum, Finset.sum_mul]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i' _ => ?_
        refine Finset.sum_congr rfl fun j' _ => ?_
        ring
      · simp
    simp_rw [hpull]
    rw [← Finset.sum_mul]
  have hR : ∀ a' : FibObject,
      (∑ i' : X₁.idx a', ∑ yz' : (fibFamTensorObj X₂ X₃).idx f,
        (fibFSym a₁ b₁ c₁ t e f *
          homEntry (𝟙 X₁) a₁ a' i₁ i' *
          homEntry (𝟙 X₂) b₁ yz'.1.1 j₁ yz'.2.2.1 *
          homEntry (𝟙 X₃) c₁ yz'.1.2 k₁ yz'.2.2.2) *
        (homEntry f₁ a' a₂ i' i₂ *
          (homEntry f₂ yz'.1.1 b₂ yz'.2.2.1 j₂ * homEntry f₃ yz'.1.2 c₂ yz'.2.2.2 k₂))) =
        fibFSym a₁ b₁ c₁ t e f *
          (∑ i' : X₁.idx a', homEntry (𝟙 X₁) a₁ a' i₁ i' * homEntry f₁ a' a₂ i' i₂) *
          ∑ b' : FibObject, ∑ c' : FibObject,
            if FibAdmB b' c' f = true then
              (∑ j' : X₂.idx b', homEntry (𝟙 X₂) b₁ b' j₁ j' * homEntry f₂ b' b₂ j' j₂) *
              (∑ k' : X₃.idx c', homEntry (𝟙 X₃) c₁ c' k₁ k' * homEntry f₃ c' c₂ k' k₂)
            else 0 := by
    intro a'
    conv_lhs =>
      arg 2
      ext i'
      rw [sum_fibFamTensorIdx (A := X₂) (B := X₃) (c := f) (G := fun b' c' j' k' =>
        (fibFSym a₁ b₁ c₁ t e f *
          homEntry (𝟙 X₁) a₁ a' i₁ i' * homEntry (𝟙 X₂) b₁ b' j₁ j' *
          homEntry (𝟙 X₃) c₁ c' k₁ k') *
        (homEntry f₁ a' a₂ i' i₂ *
          (homEntry f₂ b' b₂ j' j₂ * homEntry f₃ c' c₂ k' k₂)))]
    have hpull : ∀ i' : X₁.idx a',
        (∑ b' : FibObject, ∑ c' : FibObject,
          if FibAdmB b' c' f = true then
            ∑ j' : X₂.idx b', ∑ k' : X₃.idx c',
              (fibFSym a₁ b₁ c₁ t e f *
                homEntry (𝟙 X₁) a₁ a' i₁ i' * homEntry (𝟙 X₂) b₁ b' j₁ j' *
                homEntry (𝟙 X₃) c₁ c' k₁ k') *
              (homEntry f₁ a' a₂ i' i₂ *
                (homEntry f₂ b' b₂ j' j₂ * homEntry f₃ c' c₂ k' k₂))
          else 0) =
        (fibFSym a₁ b₁ c₁ t e f * (homEntry (𝟙 X₁) a₁ a' i₁ i' * homEntry f₁ a' a₂ i' i₂)) *
          ∑ b' : FibObject, ∑ c' : FibObject,
            if FibAdmB b' c' f = true then
              (∑ j' : X₂.idx b', homEntry (𝟙 X₂) b₁ b' j₁ j' * homEntry f₂ b' b₂ j' j₂) *
              (∑ k' : X₃.idx c', homEntry (𝟙 X₃) c₁ c' k₁ k' * homEntry f₃ c' c₂ k' k₂)
            else 0 := by
      intro i'
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      split_ifs
      · simp only [Finset.mul_sum, Finset.sum_mul]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j' _ => ?_
        refine Finset.sum_congr rfl fun k' _ => ?_
        ring
      · simp
    simp_rw [hpull]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hL' := fun c' => by
    have h := hL c'
    rw [Finset.sum_comm] at h
    exact h
  simp_rw [hL', hR]
  by_cases htri : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂
  · rcases htri with ⟨rfl, rfl, rfl⟩
    rw [Finset.sum_eq_single c₁]
    swap; · intro c' _ hne; split_ifs <;> simp [sum_homEntry_id_right, hne.symm]
    swap; · intro hm; exact (hm (Finset.mem_univ c₁)).elim
    rw [ite_eq_left he₂, Finset.sum_eq_single a₁]
    swap
    · intro a' _ hne
      refine Finset.sum_eq_zero fun b' _ => ?_
      split_ifs <;> simp [sum_homEntry_id_right, hne.symm]
    swap; · intro hm; exact (hm (Finset.mem_univ a₁)).elim
    rw [Finset.sum_eq_single b₁]
    swap; · intro b' _ hne; split_ifs <;> simp [sum_homEntry_id_right, hne.symm]
    swap; · intro hm; exact (hm (Finset.mem_univ b₁)).elim
    rw [ite_eq_left he₁]
    symm
    rw [Finset.sum_eq_single a₁]
    swap; · intro a' _ hne; split_ifs <;> simp [sum_homEntry_id_left, hne.symm]
    swap; · intro hm; exact (hm (Finset.mem_univ a₁)).elim
    rw [ite_eq_left hf₂, Finset.sum_eq_single b₁]
    swap; · intro b' _ hne; simp [homEntry_ne _ hne.symm]
    swap; · intro hm; exact (hm (Finset.mem_univ b₁)).elim
    rw [Finset.sum_eq_single c₁]
    swap; · intro c' _ hne; split_ifs <;> simp [sum_homEntry_id_left, hne.symm]
    swap; · intro hm; exact (hm (Finset.mem_univ c₁)).elim
    rw [ite_eq_left hf₁]
    simp only [homEntry_same]
    simp only [← FibFam.comp_apply, Category.id_comp, Category.comp_id]
    ring
  · have hzL : (∑ c' : FibObject,
        if FibAdmB e c' t = true then
          (∑ k' : Y₃.idx c', homEntry f₃ c₁ c' k₁ k' * homEntry (𝟙 Y₃) c' c₂ k' k₂) *
            ∑ a' : FibObject, ∑ b' : FibObject,
              if FibAdmB a' b' e = true then
                fibFSym a' b' c' t e f *
                  (∑ i' : Y₁.idx a', homEntry f₁ a₁ a' i₁ i' * homEntry (𝟙 Y₁) a' a₂ i' i₂) *
                  (∑ j' : Y₂.idx b', homEntry f₂ b₁ b' j₁ j' * homEntry (𝟙 Y₂) b' b₂ j' j₂)
              else 0
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun c' _ => ?_
      split_ifs <;> try rfl
      by_cases hc : c₁ = c₂
      · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun a' _ =>
          Finset.sum_eq_zero fun b' _ => ?_)
        split_ifs <;> try rfl
        by_cases ha : a₁ = a₂
        · have hb : b₁ ≠ b₂ := fun h => htri ⟨ha, h, hc⟩
          exact mul_eq_zero_of_right _ (sum_homEntry_mul_id_eq_zero f₂ hb b' j₁ j₂)
        · exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (sum_homEntry_mul_id_eq_zero f₁ ha a' i₁ i₂)) _
      · exact mul_eq_zero_of_left (sum_homEntry_mul_id_eq_zero f₃ hc c' k₁ k₂) _
    have hzR : (∑ a' : FibObject,
        if FibAdmB a' f t = true then
          fibFSym a₁ b₁ c₁ t e f *
            (∑ i' : X₁.idx a', homEntry (𝟙 X₁) a₁ a' i₁ i' * homEntry f₁ a' a₂ i' i₂) *
            ∑ b' : FibObject, ∑ c' : FibObject,
              if FibAdmB b' c' f = true then
                (∑ j' : X₂.idx b', homEntry (𝟙 X₂) b₁ b' j₁ j' * homEntry f₂ b' b₂ j' j₂) *
                (∑ k' : X₃.idx c', homEntry (𝟙 X₃) c₁ c' k₁ k' * homEntry f₃ c' c₂ k' k₂)
              else 0
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun a' _ => ?_
      split_ifs <;> try rfl
      by_cases ha : a₁ = a₂
      · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b' _ =>
          Finset.sum_eq_zero fun c' _ => ?_)
        split_ifs <;> try rfl
        by_cases hb : b₁ = b₂
        · have hc : c₁ ≠ c₂ := fun h => htri ⟨ha, hb, h⟩
          exact mul_eq_zero_of_right _ (sum_id_mul_homEntry_eq_zero f₃ hc c' k₁ k₂)
        · exact mul_eq_zero_of_left (sum_id_mul_homEntry_eq_zero f₂ hb b' j₁ j₂) _
      · exact mul_eq_zero_of_left
          (mul_eq_zero_of_right _ (sum_id_mul_homEntry_eq_zero f₁ ha a' i₁ i₂)) _
    rw [hzL, hzR]

private theorem fibFam_leftUnitor_naturality {X Y : FibFam} (f : X ⟶ Y) :
    (𝟙_ FibFam) ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  ext c ⟨⟨u, b₁⟩, ⟨hb₁⟩, p, i₁⟩ i₂
  cases u
  · cases p
    have hbc : b₁ = c := (fibAdmB_unit_left b₁ c).mp hb₁
    subst b₁
    change (∑ y : (fibFamTensorObj fibFamUnit Y).idx c,
        (homEntry (𝟙 fibFamUnit) .unit y.1.1 PUnit.unit y.2.2.1 *
          homEntry f c y.1.2 i₁ y.2.2.2) *
        homEntry (𝟙 Y) y.1.2 c y.2.2.2 i₂) =
      ∑ x' : X.idx c, homEntry (𝟙 X) c c i₁ x' * f c x' i₂
    rw [← Equiv.sum_comp (fibFamLeftUnitIndexEquiv Y c).symm]
    change (∑ j : Y.idx c,
      (homEntry (𝟙 fibFamUnit) .unit .unit PUnit.unit PUnit.unit *
        homEntry f c c i₁ j) * homEntry (𝟙 Y) c c j i₂) = _
    simp [homEntry_same, FibFam.id_apply, fibFamUnit]
  · exact p.elim

private theorem fibFam_rightUnitor_naturality {X Y : FibFam} (f : X ⟶ Y) :
    f ▷ (𝟙_ FibFam) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  ext c ⟨⟨a₁, u⟩, ⟨ha₁⟩, i₁, p⟩ i₂
  cases u
  · cases p
    have hac : a₁ = c := (fibAdmB_unit_right a₁ c).mp ha₁
    subst a₁
    change (∑ y : (fibFamTensorObj Y fibFamUnit).idx c,
        (homEntry f c y.1.1 i₁ y.2.2.1 *
          homEntry (𝟙 fibFamUnit) .unit y.1.2 PUnit.unit y.2.2.2) *
        homEntry (𝟙 Y) y.1.1 c y.2.2.1 i₂) =
      ∑ x' : X.idx c, homEntry (𝟙 X) c c i₁ x' * f c x' i₂
    rw [← Equiv.sum_comp (fibFamRightUnitIndexEquiv Y c).symm]
    change (∑ j : Y.idx c,
      (homEntry f c c i₁ j *
        homEntry (𝟙 fibFamUnit) .unit .unit PUnit.unit PUnit.unit) *
        homEntry (𝟙 Y) c c j i₂) = _
    simp [homEntry_same, FibFam.id_apply, fibFamUnit]
  · exact p.elim

private theorem fibFam_triangle (X Y : FibFam) :
    (α_ X (𝟙_ FibFam) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  ext t ⟨⟨e, y⟩, ⟨he₂⟩, ⟨⟨x, u⟩, ⟨he₁⟩, i, p⟩, j⟩ ⟨⟨x', y'⟩, ⟨hx'⟩, i', j'⟩
  cases u
  · cases p
    have hex : e = x := ((fibAdmB_unit_right x e).mp he₁).symm
    subst e
    change (∑ w : (fibFamTensorObj X (fibFamTensorObj fibFamUnit Y)).idx t,
        (fibFSym x .unit y t x w.1.2 *
          homEntry (𝟙 X) x w.1.1 i w.2.2.1 *
          homEntry (𝟙 fibFamUnit) .unit w.2.2.2.1.1 PUnit.unit w.2.2.2.2.2.1 *
          homEntry (𝟙 Y) y w.2.2.2.1.2 j w.2.2.2.2.2.2) *
        (homEntry (𝟙 X) w.1.1 x' w.2.2.1 i' *
          homEntry (fibFamLeftUnitor Y).hom w.1.2 y' w.2.2.2 j')) =
      homEntry (fibFamRightUnitor X).hom x x' ⟨⟨x, .unit⟩, ⟨he₁⟩, i, PUnit.unit⟩ i' *
        homEntry (𝟙 Y) y y' j j'
    rw [sum_fibFamTensorIdx (G := fun x'' f i'' (uy'' : (fibFamTensorObj fibFamUnit Y).idx f) =>
      (fibFSym x .unit y t x f *
        homEntry (𝟙 X) x x'' i i'' *
        homEntry (𝟙 fibFamUnit) .unit uy''.1.1 PUnit.unit uy''.2.2.1 *
        homEntry (𝟙 Y) y uy''.1.2 j uy''.2.2.2) *
      (homEntry (𝟙 X) x'' x' i'' i' *
        homEntry (fibFamLeftUnitor Y).hom f y' uy'' j'))]
    rw [Finset.sum_eq_single x]
    swap
    · intro x'' _ hne
      refine Finset.sum_eq_zero fun f _ => ?_
      split_ifs <;> simp [homEntry_ne _ hne.symm]
    swap; · intro hm; exact (hm (Finset.mem_univ x)).elim
    rw [Finset.sum_eq_single y]
    swap
    · intro f _ hne
      split_ifs <;> try rfl
      refine Finset.sum_eq_zero fun i'' _ => Finset.sum_eq_zero fun uy'' _ => ?_
      rcases uy'' with ⟨⟨u'', y''⟩, ⟨hy''⟩, p'', j''⟩
      cases u''
      · have huf : y'' = f := (fibAdmB_unit_left y'' f).mp hy''
        subst huf
        simp [homEntry_ne _ hne.symm]
      · exact p''.elim
    swap; · intro hm; exact (hm (Finset.mem_univ y)).elim
    rw [ite_eq_left he₂, fibFSym_unit_middle x y t he₂]
    have hL : (∑ i'' : X.idx x, ∑ uy'' : (fibFamTensorObj fibFamUnit Y).idx y,
        (1 * homEntry (𝟙 X) x x i i'' *
          homEntry (𝟙 fibFamUnit) .unit uy''.1.1 PUnit.unit uy''.2.2.1 *
          homEntry (𝟙 Y) y uy''.1.2 j uy''.2.2.2) *
        (homEntry (𝟙 X) x x' i'' i' * homEntry (fibFamLeftUnitor Y).hom y y' uy'' j')) =
        homEntry (𝟙 X) x x' i i' * homEntry (𝟙 Y) y y' j j' := by
      have hinner : ∀ i'' : X.idx x,
          (∑ uy'' : (fibFamTensorObj fibFamUnit Y).idx y,
            (1 * homEntry (𝟙 X) x x i i'' *
              homEntry (𝟙 fibFamUnit) .unit uy''.1.1 PUnit.unit uy''.2.2.1 *
              homEntry (𝟙 Y) y uy''.1.2 j uy''.2.2.2) *
            (homEntry (𝟙 X) x x' i'' i' * homEntry (fibFamLeftUnitor Y).hom y y' uy'' j')) =
          (homEntry (𝟙 X) x x i i'' * homEntry (𝟙 X) x x' i'' i') *
            homEntry (𝟙 Y) y y' j j' := by
        intro i''
        rw [← Equiv.sum_comp (fibFamLeftUnitIndexEquiv Y y).symm]
        change (∑ j'' : Y.idx y,
          (1 * homEntry (𝟙 X) x x i i'' *
            homEntry (𝟙 fibFamUnit) .unit .unit PUnit.unit PUnit.unit *
            homEntry (𝟙 Y) y y j j'') *
          (homEntry (𝟙 X) x x' i'' i' *
            homEntry (fibFamLeftUnitor Y).hom y y'
              ((fibFamLeftUnitIndexEquiv Y y).symm j'') j')) = _
        have hunit (j'' : Y.idx y) :
            homEntry (fibFamLeftUnitor Y).hom y y'
              ((fibFamLeftUnitIndexEquiv Y y).symm j'') j' =
              homEntry (𝟙 Y) y y' j'' j' := by
          by_cases h : y = y'
          · subst y'
            simp [homEntry, fibFamLeftUnitor, fibFamLeftUnitIndexEquiv, FibFam.id_apply]
          · simp [homEntry_ne _ h]
        simp_rw [hunit]
        have hu : homEntry (𝟙 fibFamUnit) .unit .unit PUnit.unit PUnit.unit = 1 := by
          simp [homEntry_same, FibFam.id_apply, fibFamUnit]
        rw [hu]
        calc (∑ j'' : Y.idx y,
            (1 * homEntry (𝟙 X) x x i i'' * 1 * homEntry (𝟙 Y) y y j j'') *
              (homEntry (𝟙 X) x x' i'' i' * homEntry (𝟙 Y) y y' j'' j'))
          _ = (homEntry (𝟙 X) x x i i'' * homEntry (𝟙 X) x x' i'' i') *
              ∑ j'' : Y.idx y, homEntry (𝟙 Y) y y j j'' * homEntry (𝟙 Y) y y' j'' j' := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun j'' _ => ?_
                ring
          _ = _ := by simp
      simp_rw [hinner]
      rw [← Finset.sum_mul, sum_homEntry_id_left, ite_eq_left rfl]
    rw [hL]
    simp [homEntry, fibFamRightUnitor]
  · exact p.elim

@[simp] theorem homEntry_associator_same (A B C : FibFam) (t : FibObject)
    (x : (fibFamTensorObj (fibFamTensorObj A B) C).idx t)
    (y : (fibFamTensorObj A (fibFamTensorObj B C)).idx t) :
    homEntry (fibFamAssociator A B C).hom t t x y =
      fibFSym x.2.2.1.1.1 x.2.2.1.1.2 x.1.2 t x.1.1 y.1.2 *
        homEntry (𝟙 A) x.2.2.1.1.1 y.1.1 x.2.2.1.2.2.1 y.2.2.1 *
        homEntry (𝟙 B) x.2.2.1.1.2 y.2.2.2.1.1 x.2.2.1.2.2.2 y.2.2.2.2.2.1 *
        homEntry (𝟙 C) x.1.2 y.2.2.2.1.2 x.2.2.2 y.2.2.2.2.2.2 := by
  rcases x with ⟨⟨e, c⟩, _, ⟨⟨a, b⟩, _, i, j⟩, k⟩
  rcases y with ⟨⟨a', f⟩, _, i', ⟨⟨b', c'⟩, _, j', k'⟩⟩
  simp [homEntry, fibFamAssociator]

@[simp] theorem homEntry_associator_inv_same (A B C : FibFam) (t : FibObject)
    (x : (fibFamTensorObj A (fibFamTensorObj B C)).idx t)
    (y : (fibFamTensorObj (fibFamTensorObj A B) C).idx t) :
    homEntry (fibFamAssociator A B C).inv t t x y =
      fibFSym y.2.2.1.1.1 y.2.2.1.1.2 y.1.2 t y.1.1 x.1.2 *
        homEntry (𝟙 A) x.1.1 y.2.2.1.1.1 x.2.2.1 y.2.2.1.2.2.1 *
        homEntry (𝟙 B) x.2.2.2.1.1 y.2.2.1.1.2 x.2.2.2.2.2.1 y.2.2.1.2.2.2 *
        homEntry (𝟙 C) x.2.2.2.1.2 y.1.2 x.2.2.2.2.2.2 y.2.2.2 := by
  rcases x with ⟨⟨a', f⟩, _, i', ⟨⟨b', c'⟩, _, j', k'⟩⟩
  rcases y with ⟨⟨e, c⟩, _, ⟨⟨a, b⟩, _, i, j⟩, k⟩
  simp [homEntry, fibFamAssociator]

private theorem fibFam_pentagon_tail (W X Y Z : FibFam) {t g₁ d₁ : FibObject}
    (hg₁ : FibAdmB g₁ d₁ t = true)
    (wxy₁ : (fibFamTensorObj W (fibFamTensorObj X Y)).idx g₁) (l₁ : Z.idx d₁)
    {a' r b' s c' d' : FibObject}
    (hr : FibAdmB a' r t = true) (hs : FibAdmB b' s r = true) (hcd' : FibAdmB c' d' s = true)
    (i' : W.idx a') (j' : X.idx b') (k' : Y.idx c') (l' : Z.idx d') :
    ((α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom) t
        ⟨⟨g₁, d₁⟩, ⟨hg₁⟩, wxy₁, l₁⟩
        ⟨⟨a', r⟩, ⟨hr⟩, i', ⟨⟨b', s⟩, ⟨hs⟩, j', ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩⟩⟩ =
      fibFSym wxy₁.1.1 wxy₁.1.2 d₁ t g₁ r *
        fibFSym wxy₁.2.2.2.1.1 wxy₁.2.2.2.1.2 d₁ r wxy₁.1.2 s *
        homEntry (𝟙 W) wxy₁.1.1 a' wxy₁.2.2.1 i' *
        homEntry (𝟙 X) wxy₁.2.2.2.1.1 b' wxy₁.2.2.2.2.2.1 j' *
        homEntry (𝟙 Y) wxy₁.2.2.2.1.2 c' wxy₁.2.2.2.2.2.2 k' *
        homEntry (𝟙 Z) d₁ d' l₁ l' := by
  rcases wxy₁ with ⟨⟨a₁, m₁⟩, ⟨hm₁⟩, i₁, ⟨⟨b₁, c₁⟩, ⟨hbc₁⟩, j₁, k₁⟩⟩
  simp only [FibFam.comp_apply]
  change (∑ z₂ : (fibFamTensorObj W (fibFamTensorObj (fibFamTensorObj X Y) Z)).idx t,
      (fibFSym a₁ m₁ d₁ t g₁ z₂.1.2 *
        homEntry (𝟙 W) a₁ z₂.1.1 i₁ z₂.2.2.1 *
        homEntry (𝟙 (fibFamTensorObj X Y)) m₁ z₂.2.2.2.1.1 ⟨⟨b₁, c₁⟩, ⟨hbc₁⟩, j₁, k₁⟩
          z₂.2.2.2.2.2.1 *
        homEntry (𝟙 Z) d₁ z₂.2.2.2.1.2 l₁ z₂.2.2.2.2.2.2) *
      (homEntry (𝟙 W) z₂.1.1 a' z₂.2.2.1 i' *
        homEntry (fibFamAssociator X Y Z).hom z₂.1.2 r z₂.2.2.2
          ⟨⟨b', s⟩, ⟨hs⟩, j', ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩⟩)) = _
  rw [sum_fibFamTensorIdx (A := W) (B := fibFamTensorObj (fibFamTensorObj X Y) Z) (c := t)
    (G := fun a₂ r₂ i₂ xy₂ =>
    (fibFSym a₁ m₁ d₁ t g₁ r₂ *
      homEntry (𝟙 W) a₁ a₂ i₁ i₂ *
      homEntry (𝟙 (fibFamTensorObj X Y)) m₁ xy₂.1.1 ⟨⟨b₁, c₁⟩, ⟨hbc₁⟩, j₁, k₁⟩ xy₂.2.2.1 *
      homEntry (𝟙 Z) d₁ xy₂.1.2 l₁ xy₂.2.2.2) *
    (homEntry (𝟙 W) a₂ a' i₂ i' *
      homEntry (fibFamAssociator X Y Z).hom r₂ r xy₂
        ⟨⟨b', s⟩, ⟨hs⟩, j', ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩⟩))]
  rw [Finset.sum_eq_single a']
  swap
  · intro a₂ _ hne
    refine Finset.sum_eq_zero fun r₂ _ => ?_
    split_ifs <;> simp [homEntry_ne _ hne]
  swap
  · intro hm; exact (hm (Finset.mem_univ a')).elim
  rw [Finset.sum_eq_single r]
  swap
  · intro r₂ _ hne; split_ifs <;> simp [homEntry_ne _ hne]
  swap
  · intro hm; exact (hm (Finset.mem_univ r)).elim
  rw [ite_eq_left hr]
  have hmid : ∀ i₂ : W.idx a',
      (∑ xy₂ : (fibFamTensorObj (fibFamTensorObj X Y) Z).idx r,
        (fibFSym a₁ m₁ d₁ t g₁ r *
          homEntry (𝟙 W) a₁ a' i₁ i₂ *
          homEntry (𝟙 (fibFamTensorObj X Y)) m₁ xy₂.1.1 ⟨⟨b₁, c₁⟩, ⟨hbc₁⟩, j₁, k₁⟩ xy₂.2.2.1 *
          homEntry (𝟙 Z) d₁ xy₂.1.2 l₁ xy₂.2.2.2) *
        (homEntry (𝟙 W) a' a' i₂ i' *
          homEntry (fibFamAssociator X Y Z).hom r r xy₂
            ⟨⟨b', s⟩, ⟨hs⟩, j', ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩⟩)) =
      (homEntry (𝟙 W) a₁ a' i₁ i₂ * homEntry (𝟙 W) a' a' i₂ i') *
        (fibFSym a₁ m₁ d₁ t g₁ r * fibFSym b₁ c₁ d₁ r m₁ s *
          homEntry (𝟙 X) b₁ b' j₁ j' * homEntry (𝟙 Y) c₁ c' k₁ k' *
          homEntry (𝟙 Z) d₁ d' l₁ l') := by
    intro i₂
    simp only [homEntry_associator_same]
    by_cases hmd : FibAdmB m₁ d₁ r = true
    · rw [sum_fibFamTensorIdx (G := fun m₂ d₂ bc₂ l₂ =>
        (fibFSym a₁ m₁ d₁ t g₁ r *
          homEntry (𝟙 W) a₁ a' i₁ i₂ *
          homEntry (𝟙 (fibFamTensorObj X Y)) m₁ m₂ ⟨⟨b₁, c₁⟩, ⟨hbc₁⟩, j₁, k₁⟩ bc₂ *
          homEntry (𝟙 Z) d₁ d₂ l₁ l₂) *
        (homEntry (𝟙 W) a' a' i₂ i' *
          (fibFSym bc₂.1.1 bc₂.1.2 d₂ r m₂ s *
            homEntry (𝟙 X) bc₂.1.1 b' bc₂.2.2.1 j' *
            homEntry (𝟙 Y) bc₂.1.2 c' bc₂.2.2.2 k' *
            homEntry (𝟙 Z) d₂ d' l₂ l')))]
      rw [Finset.sum_eq_single m₁]
      swap
      · intro m₂ _ hne
        refine Finset.sum_eq_zero fun d₂ _ => ?_
        split_ifs <;> simp [homEntry_ne _ hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ m₁)).elim
      rw [Finset.sum_eq_single d₁]
      swap
      · intro d₂ _ hne; split_ifs <;> simp [homEntry_ne _ hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ d₁)).elim
      rw [ite_eq_left hmd]
      rw [Finset.sum_eq_single ⟨⟨b₁, c₁⟩, ⟨hbc₁⟩, j₁, k₁⟩]
      swap
      · intro bc₂ _ hne
        refine Finset.sum_eq_zero fun l₂ _ => ?_
        simp [homEntry_same, FibFam.id_apply, hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ _)).elim
      simp only [homEntry_same, FibFam.id_apply, ↓reduceIte, mul_one]
      simp only [← FibFam.id_apply, ← homEntry_same]
      calc (∑ l₂ : Z.idx d₁,
            (fibFSym a₁ m₁ d₁ t g₁ r * homEntry (𝟙 W) a₁ a' i₁ i₂ *
              homEntry (𝟙 Z) d₁ d₁ l₁ l₂) *
            (homEntry (𝟙 W) a' a' i₂ i' *
              (fibFSym b₁ c₁ d₁ r m₁ s * homEntry (𝟙 X) b₁ b' j₁ j' *
                homEntry (𝟙 Y) c₁ c' k₁ k' * homEntry (𝟙 Z) d₁ d' l₂ l')))
        = (∑ l₂ : Z.idx d₁, homEntry (𝟙 Z) d₁ d₁ l₁ l₂ * homEntry (𝟙 Z) d₁ d' l₂ l') *
            ((homEntry (𝟙 W) a₁ a' i₁ i₂ * homEntry (𝟙 W) a' a' i₂ i') *
              (fibFSym a₁ m₁ d₁ t g₁ r * fibFSym b₁ c₁ d₁ r m₁ s *
                homEntry (𝟙 X) b₁ b' j₁ j' * homEntry (𝟙 Y) c₁ c' k₁ k')) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun l₂ _ => ?_
            ring
      _ = homEntry (𝟙 Z) d₁ d' l₁ l' *
            ((homEntry (𝟙 W) a₁ a' i₁ i₂ * homEntry (𝟙 W) a' a' i₂ i') *
              (fibFSym a₁ m₁ d₁ t g₁ r * fibFSym b₁ c₁ d₁ r m₁ s *
                homEntry (𝟙 X) b₁ b' j₁ j' * homEntry (𝟙 Y) c₁ c' k₁ k')) := by
          rw [sum_homEntry_id_left, ite_eq_left rfl]
      _ = _ := by ring
    · have hz : fibFSym a₁ m₁ d₁ t g₁ r = 0 := fibFSym_zero_of_adm (by simp [hmd])
      simp [hz]
  simp_rw [hmid]
  rw [← Finset.sum_mul, sum_homEntry_id_right]
  by_cases ha : a₁ = a'
  · simp [ha]; ring
  · simp [ha, homEntry_ne _ ha]

private theorem fibFam_pentagon_rhs_tail (W X Y Z : FibFam) {t : FibObject}
    {g₀ d₀ e₀ c₀ a₀ b₀ : FibObject}
    (hg₀ : FibAdmB g₀ d₀ t = true) (he₀ : FibAdmB e₀ c₀ g₀ = true) (hab₀ : FibAdmB a₀ b₀ e₀ = true)
    (i₀ : W.idx a₀) (j₀ : X.idx b₀) (k₀ : Y.idx c₀) (l₀ : Z.idx d₀)
    {a' r' b' s' c' d' : FibObject}
    (hr' : FibAdmB a' r' t = true) (hs' : FibAdmB b' s' r' = true) (hcd' : FibAdmB c' d' s' = true)
    (i' : W.idx a') (j' : X.idx b') (k' : Y.idx c') (l' : Z.idx d') :
    ((α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom) t
        ⟨⟨g₀, d₀⟩, ⟨hg₀⟩, ⟨⟨e₀, c₀⟩, ⟨he₀⟩, ⟨⟨a₀, b₀⟩, ⟨hab₀⟩, i₀, j₀⟩, k₀⟩, l₀⟩
        ⟨⟨a', r'⟩, ⟨hr'⟩, i', ⟨⟨b', s'⟩, ⟨hs'⟩, j', ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩⟩⟩ =
      fibFSym e₀ c₀ d₀ t g₀ s' * fibFSym a₀ b₀ s' t e₀ r' *
        homEntry (𝟙 W) a₀ a' i₀ i' * homEntry (𝟙 X) b₀ b' j₀ j' *
        homEntry (𝟙 Y) c₀ c' k₀ k' * homEntry (𝟙 Z) d₀ d' l₀ l' := by
  simp only [FibFam.comp_apply]
  change (∑ z : (fibFamTensorObj (fibFamTensorObj W X) (fibFamTensorObj Y Z)).idx t,
    (fibFSym e₀ c₀ d₀ t g₀ z.1.2 *
      homEntry (𝟙 (fibFamTensorObj W X)) e₀ z.1.1 ⟨⟨a₀, b₀⟩, ⟨hab₀⟩, i₀, j₀⟩ z.2.2.1 *
      homEntry (𝟙 Y) c₀ z.2.2.2.1.1 k₀ z.2.2.2.2.2.1 *
      homEntry (𝟙 Z) d₀ z.2.2.2.1.2 l₀ z.2.2.2.2.2.2) *
    (fibFSym z.2.2.1.1.1 z.2.2.1.1.2 z.1.2 t z.1.1 r' *
      homEntry (𝟙 W) z.2.2.1.1.1 a' z.2.2.1.2.2.1 i' *
      homEntry (𝟙 X) z.2.2.1.1.2 b' z.2.2.1.2.2.2 j' *
      homEntry (𝟙 (fibFamTensorObj Y Z)) z.1.2 s' z.2.2.2
        ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩)) = _
  rw [sum_fibFamTensorIdx (A := fibFamTensorObj W X) (B := fibFamTensorObj Y Z) (c := t)
    (G := fun e₂ s₂ wx₂ yz₂ =>
    (fibFSym e₀ c₀ d₀ t g₀ s₂ *
      homEntry (𝟙 (fibFamTensorObj W X)) e₀ e₂ ⟨⟨a₀, b₀⟩, ⟨hab₀⟩, i₀, j₀⟩ wx₂ *
      homEntry (𝟙 Y) c₀ yz₂.1.1 k₀ yz₂.2.2.1 *
      homEntry (𝟙 Z) d₀ yz₂.1.2 l₀ yz₂.2.2.2) *
    (fibFSym wx₂.1.1 wx₂.1.2 s₂ t e₂ r' *
      homEntry (𝟙 W) wx₂.1.1 a' wx₂.2.2.1 i' *
      homEntry (𝟙 X) wx₂.1.2 b' wx₂.2.2.2 j' *
      homEntry (𝟙 (fibFamTensorObj Y Z)) s₂ s' yz₂ ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩))]
  rw [Finset.sum_eq_single e₀]
  swap
  · intro e₂ _ hne
    refine Finset.sum_eq_zero fun s₂ _ => ?_
    split_ifs <;> simp [homEntry_ne _ hne.symm]
  swap
  · intro hm; exact (hm (Finset.mem_univ e₀)).elim
  rw [Finset.sum_eq_single s']
  swap
  · intro s₂ _ hne; split_ifs <;> simp [homEntry_ne _ hne]
  swap
  · intro hm; exact (hm (Finset.mem_univ s')).elim
  by_cases hes : FibAdmB e₀ s' t = true
  · rw [ite_eq_left hes]
    have hsum_wx :
        (∑ wx₂ : (fibFamTensorObj W X).idx e₀, ∑ yz₂ : (fibFamTensorObj Y Z).idx s',
          (fibFSym e₀ c₀ d₀ t g₀ s' *
            homEntry (𝟙 (fibFamTensorObj W X)) e₀ e₀ ⟨⟨a₀, b₀⟩, ⟨hab₀⟩, i₀, j₀⟩ wx₂ *
            homEntry (𝟙 Y) c₀ yz₂.1.1 k₀ yz₂.2.2.1 *
            homEntry (𝟙 Z) d₀ yz₂.1.2 l₀ yz₂.2.2.2) *
          (fibFSym wx₂.1.1 wx₂.1.2 s' t e₀ r' *
            homEntry (𝟙 W) wx₂.1.1 a' wx₂.2.2.1 i' *
            homEntry (𝟙 X) wx₂.1.2 b' wx₂.2.2.2 j' *
            homEntry (𝟙 (fibFamTensorObj Y Z)) s' s' yz₂ ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩)) =
        fibFSym e₀ c₀ d₀ t g₀ s' * fibFSym a₀ b₀ s' t e₀ r' *
          homEntry (𝟙 W) a₀ a' i₀ i' * homEntry (𝟙 X) b₀ b' j₀ j' *
          homEntry (𝟙 Y) c₀ c' k₀ k' * homEntry (𝟙 Z) d₀ d' l₀ l' := by
      rw [Finset.sum_eq_single ⟨⟨a₀, b₀⟩, ⟨hab₀⟩, i₀, j₀⟩]
      swap
      · intro wx₂ _ hne
        refine Finset.sum_eq_zero fun yz₂ _ => ?_
        simp [homEntry_same, FibFam.id_apply, hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ _)).elim
      rw [Finset.sum_eq_single ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩]
      swap
      · intro yz₂ _ hne
        simp [homEntry_same, FibFam.id_apply, hne]
      swap
      · intro hm; exact (hm (Finset.mem_univ _)).elim
      simp only [homEntry_same, FibFam.id_apply, ↓reduceIte, mul_one]
      ring
    exact hsum_wx
  · rw [ite_eq_right hes]
    have hz : fibFSym e₀ c₀ d₀ t g₀ s' = 0 := fibFSym_zero_of_adm (by simp [hes])
    simp [hz]

private theorem fibFam_pentagon (W X Y Z : FibFam) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  ext t ⟨⟨g₀, d₀⟩, ⟨hg₀⟩, ⟨⟨e₀, c₀⟩, ⟨he₀⟩, ⟨⟨a₀, b₀⟩, ⟨hab₀⟩, i₀, j₀⟩, k₀⟩, l₀⟩
    ⟨⟨a', r'⟩, ⟨hr'⟩, i', ⟨⟨b', s'⟩, ⟨hs'⟩, j', ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩⟩⟩
  simp only [FibFam.comp_apply]
  have hrhs := fibFam_pentagon_rhs_tail W X Y Z hg₀ he₀ hab₀ i₀ j₀ k₀ l₀ hr' hs' hcd' i' j' k' l'
  simp only [FibFam.comp_apply] at hrhs
  rw [hrhs]
  change (∑ z₁ : (fibFamTensorObj (fibFamTensorObj W (fibFamTensorObj X Y)) Z).idx t,
      (homEntry (fibFamAssociator W X Y).hom g₀ z₁.1.1
          ⟨⟨e₀, c₀⟩, ⟨he₀⟩, ⟨⟨a₀, b₀⟩, ⟨hab₀⟩, i₀, j₀⟩, k₀⟩ z₁.2.2.1 *
        homEntry (𝟙 Z) d₀ z₁.1.2 l₀ z₁.2.2.2) *
      ((α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom) t z₁
        ⟨⟨a', r'⟩, ⟨hr'⟩, i', ⟨⟨b', s'⟩, ⟨hs'⟩, j', ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩⟩⟩) = _
  have htail : ∀ z₁ : (fibFamTensorObj (fibFamTensorObj W (fibFamTensorObj X Y)) Z).idx t,
      ((α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom) t z₁
        ⟨⟨a', r'⟩, ⟨hr'⟩, i', ⟨⟨b', s'⟩, ⟨hs'⟩, j', ⟨⟨c', d'⟩, ⟨hcd'⟩, k', l'⟩⟩⟩ =
      fibFSym z₁.2.2.1.1.1 z₁.2.2.1.1.2 z₁.1.2 t z₁.1.1 r' *
        fibFSym z₁.2.2.1.2.2.2.1.1 z₁.2.2.1.2.2.2.1.2 z₁.1.2 r' z₁.2.2.1.1.2 s' *
        homEntry (𝟙 W) z₁.2.2.1.1.1 a' z₁.2.2.1.2.2.1 i' *
        homEntry (𝟙 X) z₁.2.2.1.2.2.2.1.1 b' z₁.2.2.1.2.2.2.2.2.1 j' *
        homEntry (𝟙 Y) z₁.2.2.1.2.2.2.1.2 c' z₁.2.2.1.2.2.2.2.2.2 k' *
        homEntry (𝟙 Z) z₁.1.2 d' z₁.2.2.2 l' := by
    rintro ⟨⟨g₁, d₁⟩, ⟨hg₁⟩, wxy₁, l₁⟩
    exact fibFam_pentagon_tail W X Y Z hg₁ wxy₁ l₁ hr' hs' hcd' i' j' k' l'
  simp_rw [htail]
  rw [sum_fibFamTensorIdx (A := fibFamTensorObj W (fibFamTensorObj X Y)) (B := Z) (c := t) (G := fun g₁ d₁ wxy₁ l₁ =>
    (homEntry (fibFamAssociator W X Y).hom g₀ g₁
        ⟨⟨e₀, c₀⟩, ⟨he₀⟩, ⟨⟨a₀, b₀⟩, ⟨hab₀⟩, i₀, j₀⟩, k₀⟩ wxy₁ *
      homEntry (𝟙 Z) d₀ d₁ l₀ l₁) *
    (fibFSym wxy₁.1.1 wxy₁.1.2 d₁ t g₁ r' *
      fibFSym wxy₁.2.2.2.1.1 wxy₁.2.2.2.1.2 d₁ r' wxy₁.1.2 s' *
      homEntry (𝟙 W) wxy₁.1.1 a' wxy₁.2.2.1 i' *
      homEntry (𝟙 X) wxy₁.2.2.2.1.1 b' wxy₁.2.2.2.2.2.1 j' *
      homEntry (𝟙 Y) wxy₁.2.2.2.1.2 c' wxy₁.2.2.2.2.2.2 k' *
      homEntry (𝟙 Z) d₁ d' l₁ l'))]
  rw [Finset.sum_eq_single g₀]
  swap
  · intro g₁ _ hne
    refine Finset.sum_eq_zero fun d₁ _ => ?_
    split_ifs <;> simp [homEntry_ne _ hne.symm]
  swap
  · intro hm; exact (hm (Finset.mem_univ g₀)).elim
  rw [Finset.sum_eq_single d₀]
  swap
  · intro d₁ _ hne; split_ifs <;> simp [homEntry_ne _ hne.symm]
  swap
  · intro hm; exact (hm (Finset.mem_univ d₀)).elim
  rw [ite_eq_left hg₀]
  simp only [homEntry_associator_same]
  have hwxy : ∀ l₁ : Z.idx d₀,
      (∑ wxy₁ : (fibFamTensorObj W (fibFamTensorObj X Y)).idx g₀,
        ((fibFSym a₀ b₀ c₀ g₀ e₀ wxy₁.1.2 *
            homEntry (𝟙 W) a₀ wxy₁.1.1 i₀ wxy₁.2.2.1 *
            homEntry (𝟙 X) b₀ wxy₁.2.2.2.1.1 j₀ wxy₁.2.2.2.2.2.1 *
            homEntry (𝟙 Y) c₀ wxy₁.2.2.2.1.2 k₀ wxy₁.2.2.2.2.2.2) *
          homEntry (𝟙 Z) d₀ d₀ l₀ l₁) *
        (fibFSym wxy₁.1.1 wxy₁.1.2 d₀ t g₀ r' *
          fibFSym wxy₁.2.2.2.1.1 wxy₁.2.2.2.1.2 d₀ r' wxy₁.1.2 s' *
          homEntry (𝟙 W) wxy₁.1.1 a' wxy₁.2.2.1 i' *
          homEntry (𝟙 X) wxy₁.2.2.2.1.1 b' wxy₁.2.2.2.2.2.1 j' *
          homEntry (𝟙 Y) wxy₁.2.2.2.1.2 c' wxy₁.2.2.2.2.2.2 k' *
          homEntry (𝟙 Z) d₀ d' l₁ l')) =
      (homEntry (𝟙 Z) d₀ d₀ l₀ l₁ * homEntry (𝟙 Z) d₀ d' l₁ l') *
        (fibFSym e₀ c₀ d₀ t g₀ s' * fibFSym a₀ b₀ s' t e₀ r' *
          homEntry (𝟙 W) a₀ a' i₀ i' * homEntry (𝟙 X) b₀ b' j₀ j' *
          homEntry (𝟙 Y) c₀ c' k₀ k') := by
    intro l₁
    rw [sum_fibFamTensorIdx (A := W) (B := fibFamTensorObj X Y) (c := g₀) (G := fun a₁ m₁ i₁ xy₁ =>
      ((fibFSym a₀ b₀ c₀ g₀ e₀ m₁ *
          homEntry (𝟙 W) a₀ a₁ i₀ i₁ *
          homEntry (𝟙 X) b₀ xy₁.1.1 j₀ xy₁.2.2.1 *
          homEntry (𝟙 Y) c₀ xy₁.1.2 k₀ xy₁.2.2.2) *
        homEntry (𝟙 Z) d₀ d₀ l₀ l₁) *
      (fibFSym a₁ m₁ d₀ t g₀ r' *
        fibFSym xy₁.1.1 xy₁.1.2 d₀ r' m₁ s' *
        homEntry (𝟙 W) a₁ a' i₁ i' *
        homEntry (𝟙 X) xy₁.1.1 b' xy₁.2.2.1 j' *
        homEntry (𝟙 Y) xy₁.1.2 c' xy₁.2.2.2 k' *
        homEntry (𝟙 Z) d₀ d' l₁ l'))]
    rw [Finset.sum_eq_single a₀]
    swap
    · intro a₁ _ hne
      refine Finset.sum_eq_zero fun m₁ _ => ?_
      split_ifs <;> simp [homEntry_ne _ hne.symm]
    swap
    · intro hm; exact (hm (Finset.mem_univ a₀)).elim
    have hmterm : ∀ m₁ : FibObject,
        (if FibAdmB a₀ m₁ g₀ = true then
          ∑ i₁ : W.idx a₀, ∑ xy₁ : (fibFamTensorObj X Y).idx m₁,
            ((fibFSym a₀ b₀ c₀ g₀ e₀ m₁ *
                homEntry (𝟙 W) a₀ a₀ i₀ i₁ *
                homEntry (𝟙 X) b₀ xy₁.1.1 j₀ xy₁.2.2.1 *
                homEntry (𝟙 Y) c₀ xy₁.1.2 k₀ xy₁.2.2.2) *
              homEntry (𝟙 Z) d₀ d₀ l₀ l₁) *
            (fibFSym a₀ m₁ d₀ t g₀ r' *
              fibFSym xy₁.1.1 xy₁.1.2 d₀ r' m₁ s' *
              homEntry (𝟙 W) a₀ a' i₁ i' *
              homEntry (𝟙 X) xy₁.1.1 b' xy₁.2.2.1 j' *
              homEntry (𝟙 Y) xy₁.1.2 c' xy₁.2.2.2 k' *
              homEntry (𝟙 Z) d₀ d' l₁ l')
        else 0) =
        (homEntry (𝟙 Z) d₀ d₀ l₀ l₁ * homEntry (𝟙 Z) d₀ d' l₁ l') *
          (fibFSym a₀ b₀ c₀ g₀ e₀ m₁ * fibFSym a₀ m₁ d₀ t g₀ r' *
            fibFSym b₀ c₀ d₀ r' m₁ s') *
          homEntry (𝟙 W) a₀ a' i₀ i' * homEntry (𝟙 X) b₀ b' j₀ j' *
          homEntry (𝟙 Y) c₀ c' k₀ k' := by
      intro m₁
      by_cases ham : FibAdmB a₀ m₁ g₀ = true
      · rw [ite_eq_left ham]
        have hxy : ∀ i₁ : W.idx a₀,
            (∑ xy₁ : (fibFamTensorObj X Y).idx m₁,
              ((fibFSym a₀ b₀ c₀ g₀ e₀ m₁ *
                  homEntry (𝟙 W) a₀ a₀ i₀ i₁ *
                  homEntry (𝟙 X) b₀ xy₁.1.1 j₀ xy₁.2.2.1 *
                  homEntry (𝟙 Y) c₀ xy₁.1.2 k₀ xy₁.2.2.2) *
                homEntry (𝟙 Z) d₀ d₀ l₀ l₁) *
              (fibFSym a₀ m₁ d₀ t g₀ r' *
                fibFSym xy₁.1.1 xy₁.1.2 d₀ r' m₁ s' *
                homEntry (𝟙 W) a₀ a' i₁ i' *
                homEntry (𝟙 X) xy₁.1.1 b' xy₁.2.2.1 j' *
                homEntry (𝟙 Y) xy₁.1.2 c' xy₁.2.2.2 k' *
                homEntry (𝟙 Z) d₀ d' l₁ l')) =
            (homEntry (𝟙 W) a₀ a₀ i₀ i₁ * homEntry (𝟙 W) a₀ a' i₁ i') *
              ((homEntry (𝟙 Z) d₀ d₀ l₀ l₁ * homEntry (𝟙 Z) d₀ d' l₁ l') *
                (fibFSym a₀ b₀ c₀ g₀ e₀ m₁ * fibFSym a₀ m₁ d₀ t g₀ r' *
                  fibFSym b₀ c₀ d₀ r' m₁ s') *
                homEntry (𝟙 X) b₀ b' j₀ j' * homEntry (𝟙 Y) c₀ c' k₀ k') := by
          intro i₁
          rw [sum_fibFamTensorIdx (A := X) (B := Y) (c := m₁) (G := fun b₁ c₁ j₁ k₁ =>
            ((fibFSym a₀ b₀ c₀ g₀ e₀ m₁ *
                homEntry (𝟙 W) a₀ a₀ i₀ i₁ *
                homEntry (𝟙 X) b₀ b₁ j₀ j₁ *
                homEntry (𝟙 Y) c₀ c₁ k₀ k₁) *
              homEntry (𝟙 Z) d₀ d₀ l₀ l₁) *
            (fibFSym a₀ m₁ d₀ t g₀ r' *
              fibFSym b₁ c₁ d₀ r' m₁ s' *
              homEntry (𝟙 W) a₀ a' i₁ i' *
              homEntry (𝟙 X) b₁ b' j₁ j' *
              homEntry (𝟙 Y) c₁ c' k₁ k' *
              homEntry (𝟙 Z) d₀ d' l₁ l'))]
          rw [Finset.sum_eq_single b₀]
          swap
          · intro b₁ _ hne
            refine Finset.sum_eq_zero fun c₁ _ => ?_
            split_ifs <;> simp [homEntry_ne _ hne.symm]
          swap
          · intro hm; exact (hm (Finset.mem_univ b₀)).elim
          rw [Finset.sum_eq_single c₀]
          swap
          · intro c₁ _ hne; split_ifs <;> simp [homEntry_ne _ hne.symm]
          swap
          · intro hm; exact (hm (Finset.mem_univ c₀)).elim
          by_cases hbc : FibAdmB b₀ c₀ m₁ = true
          · rw [ite_eq_left hbc]
            have hjk :
                (∑ j₁ : X.idx b₀, ∑ k₁ : Y.idx c₀,
                  ((fibFSym a₀ b₀ c₀ g₀ e₀ m₁ *
                      homEntry (𝟙 W) a₀ a₀ i₀ i₁ *
                      homEntry (𝟙 X) b₀ b₀ j₀ j₁ *
                      homEntry (𝟙 Y) c₀ c₀ k₀ k₁) *
                    homEntry (𝟙 Z) d₀ d₀ l₀ l₁) *
                  (fibFSym a₀ m₁ d₀ t g₀ r' *
                    fibFSym b₀ c₀ d₀ r' m₁ s' *
                    homEntry (𝟙 W) a₀ a' i₁ i' *
                    homEntry (𝟙 X) b₀ b' j₁ j' *
                    homEntry (𝟙 Y) c₀ c' k₁ k' *
                    homEntry (𝟙 Z) d₀ d' l₁ l')) =
                (∑ j₁ : X.idx b₀, homEntry (𝟙 X) b₀ b₀ j₀ j₁ * homEntry (𝟙 X) b₀ b' j₁ j') *
                  (∑ k₁ : Y.idx c₀, homEntry (𝟙 Y) c₀ c₀ k₀ k₁ * homEntry (𝟙 Y) c₀ c' k₁ k') *
                  ((homEntry (𝟙 W) a₀ a₀ i₀ i₁ * homEntry (𝟙 W) a₀ a' i₁ i') *
                    (homEntry (𝟙 Z) d₀ d₀ l₀ l₁ * homEntry (𝟙 Z) d₀ d' l₁ l') *
                    (fibFSym a₀ b₀ c₀ g₀ e₀ m₁ * fibFSym a₀ m₁ d₀ t g₀ r' *
                      fibFSym b₀ c₀ d₀ r' m₁ s')) := by
              rw [Finset.sum_mul]
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j₁ _ => ?_
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun k₁ _ => ?_
              ring
            rw [hjk, sum_homEntry_id_left, sum_homEntry_id_left, ite_eq_left rfl, ite_eq_left rfl]
            ring
          · rw [ite_eq_right hbc]
            have hz : fibFSym a₀ b₀ c₀ g₀ e₀ m₁ = 0 := fibFSym_zero_of_adm (by simp [hbc])
            simp [hz]
        simp_rw [hxy]
        rw [← Finset.sum_mul, sum_homEntry_id_left, ite_eq_left rfl]
        ring
      · rw [ite_eq_right ham]
        have hz : fibFSym a₀ b₀ c₀ g₀ e₀ m₁ = 0 := fibFSym_zero_of_adm (by simp [ham])
        simp [hz]
    simp_rw [hmterm]
    calc
      (∑ m₁ : FibObject,
          (homEntry (𝟙 Z) d₀ d₀ l₀ l₁ * homEntry (𝟙 Z) d₀ d' l₁ l') *
            (fibFSym a₀ b₀ c₀ g₀ e₀ m₁ * fibFSym a₀ m₁ d₀ t g₀ r' *
              fibFSym b₀ c₀ d₀ r' m₁ s') *
            homEntry (𝟙 W) a₀ a' i₀ i' * homEntry (𝟙 X) b₀ b' j₀ j' *
            homEntry (𝟙 Y) c₀ c' k₀ k')
      = (∑ m₁ : FibObject, fibFSym a₀ b₀ c₀ g₀ e₀ m₁ * fibFSym a₀ m₁ d₀ t g₀ r' *
            fibFSym b₀ c₀ d₀ r' m₁ s') *
          (homEntry (𝟙 Z) d₀ d₀ l₀ l₁ * homEntry (𝟙 Z) d₀ d' l₁ l') *
          homEntry (𝟙 W) a₀ a' i₀ i' * homEntry (𝟙 X) b₀ b' j₀ j' *
          homEntry (𝟙 Y) c₀ c' k₀ k' := by
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        ring
      _ = _ := by
        rw [fibFSym_pentagon a₀ b₀ c₀ d₀ t e₀ g₀ s' r']
        ring
  calc
    (∑ x : (fibFamTensorObj W (fibFamTensorObj X Y)).idx g₀, ∑ x_1 : Z.idx d₀,
        ((fibFSym a₀ b₀ c₀ g₀ e₀ x.1.2 *
            homEntry (𝟙 W) a₀ x.1.1 i₀ x.2.2.1 *
            homEntry (𝟙 X) b₀ x.2.2.2.1.1 j₀ x.2.2.2.2.2.1 *
            homEntry (𝟙 Y) c₀ x.2.2.2.1.2 k₀ x.2.2.2.2.2.2) *
          homEntry (𝟙 Z) d₀ d₀ l₀ x_1) *
        (fibFSym x.1.1 x.1.2 d₀ t g₀ r' *
          fibFSym x.2.2.2.1.1 x.2.2.2.1.2 d₀ r' x.1.2 s' *
          homEntry (𝟙 W) x.1.1 a' x.2.2.1 i' *
          homEntry (𝟙 X) x.2.2.2.1.1 b' x.2.2.2.2.2.1 j' *
          homEntry (𝟙 Y) x.2.2.2.1.2 c' x.2.2.2.2.2.2 k' *
          homEntry (𝟙 Z) d₀ d' x_1 l'))
      = ∑ l₁ : Z.idx d₀, ∑ wxy₁ : (fibFamTensorObj W (fibFamTensorObj X Y)).idx g₀,
        ((fibFSym a₀ b₀ c₀ g₀ e₀ wxy₁.1.2 *
            homEntry (𝟙 W) a₀ wxy₁.1.1 i₀ wxy₁.2.2.1 *
            homEntry (𝟙 X) b₀ wxy₁.2.2.2.1.1 j₀ wxy₁.2.2.2.2.2.1 *
            homEntry (𝟙 Y) c₀ wxy₁.2.2.2.1.2 k₀ wxy₁.2.2.2.2.2.2) *
          homEntry (𝟙 Z) d₀ d₀ l₀ l₁) *
        (fibFSym wxy₁.1.1 wxy₁.1.2 d₀ t g₀ r' *
          fibFSym wxy₁.2.2.2.1.1 wxy₁.2.2.2.1.2 d₀ r' wxy₁.1.2 s' *
          homEntry (𝟙 W) wxy₁.1.1 a' wxy₁.2.2.1 i' *
          homEntry (𝟙 X) wxy₁.2.2.2.1.1 b' wxy₁.2.2.2.2.2.1 j' *
          homEntry (𝟙 Y) wxy₁.2.2.2.1.2 c' wxy₁.2.2.2.2.2.2 k' *
          homEntry (𝟙 Z) d₀ d' l₁ l') := Finset.sum_comm
    _ = ∑ l₁ : Z.idx d₀,
        (homEntry (𝟙 Z) d₀ d₀ l₀ l₁ * homEntry (𝟙 Z) d₀ d' l₁ l') *
          (fibFSym e₀ c₀ d₀ t g₀ s' * fibFSym a₀ b₀ s' t e₀ r' *
            homEntry (𝟙 W) a₀ a' i₀ i' * homEntry (𝟙 X) b₀ b' j₀ j' *
            homEntry (𝟙 Y) c₀ c' k₀ k') := by
      refine Finset.sum_congr rfl fun l₁ _ => hwxy l₁
    _ = homEntry (𝟙 Z) d₀ d' l₀ l' *
        (fibFSym e₀ c₀ d₀ t g₀ s' * fibFSym a₀ b₀ s' t e₀ r' *
          homEntry (𝟙 W) a₀ a' i₀ i' * homEntry (𝟙 X) b₀ b' j₀ j' *
          homEntry (𝟙 Y) c₀ c' k₀ k') := by
      rw [← Finset.sum_mul, sum_homEntry_id_left, ite_eq_left rfl]
    _ = _ := by ring

instance : MonoidalCategory.{0} FibFam where
  tensorHom_def := fibFam_tensorHom_def
  id_tensorHom_id := fibFam_id_tensorHom_id
  tensorHom_comp_tensorHom := fibFam_tensorHom_comp_tensorHom
  whiskerLeft_id := fibFam_whiskerLeft_id
  id_whiskerRight := fibFam_id_whiskerRight
  associator_naturality := fibFam_associator_naturality
  leftUnitor_naturality := fibFam_leftUnitor_naturality
  rightUnitor_naturality := fibFam_rightUnitor_naturality
  pentagon := fibFam_pentagon
  triangle := fibFam_triangle

/-- Braiding isomorphism `A ⊗ B ≅ B ⊗ A` in `FibFam` weighted by `R`-symbols `fibRSym`. -/
def fibFamBraiding (A B : FibFam) :
    fibFamTensorObj A B ≅ fibFamTensorObj B A where
  hom d
    | ⟨⟨a, b⟩, _, i, j⟩, ⟨⟨b', a'⟩, _, j', i'⟩ =>
      fibRSym a b d * homEntry (𝟙 A) a a' i i' * homEntry (𝟙 B) b b' j j'
  inv d
    | ⟨⟨b', a'⟩, _, j', i'⟩, ⟨⟨a, b⟩, _, i, j⟩ =>
      fibRSymInv a b d * homEntry (𝟙 B) b' b j' j * homEntry (𝟙 A) a' a i' i
  hom_inv_id := by
    ext d ⟨⟨a₁, b₁⟩, ⟨h₁⟩, i₁, j₁⟩ ⟨⟨a₂, b₂⟩, ⟨h₂⟩, i₂, j₂⟩
    change (∑ x : (fibFamTensorObj B A).idx d,
      (fibRSym a₁ b₁ d * homEntry (𝟙 A) a₁ x.1.2 i₁ x.2.2.2 *
        homEntry (𝟙 B) b₁ x.1.1 j₁ x.2.2.1) *
      (fibRSymInv a₂ b₂ d * homEntry (𝟙 B) x.1.1 b₂ x.2.2.1 j₂ *
        homEntry (𝟙 A) x.1.2 a₂ x.2.2.2 i₂)) = _
    rw [sum_fibFamTensorIdx (G := fun b' a' j' i' =>
      (fibRSym a₁ b₁ d * homEntry (𝟙 A) a₁ a' i₁ i' * homEntry (𝟙 B) b₁ b' j₁ j') *
      (fibRSymInv a₂ b₂ d * homEntry (𝟙 B) b' b₂ j' j₂ * homEntry (𝟙 A) a' a₂ i' i₂))]
    have hpull : ∀ b' a',
        (∑ j' : B.idx b', ∑ i' : A.idx a',
          (fibRSym a₁ b₁ d * homEntry (𝟙 A) a₁ a' i₁ i' * homEntry (𝟙 B) b₁ b' j₁ j') *
          (fibRSymInv a₂ b₂ d * homEntry (𝟙 B) b' b₂ j' j₂ * homEntry (𝟙 A) a' a₂ i' i₂)) =
        (fibRSym a₁ b₁ d * fibRSymInv a₂ b₂ d) *
          (∑ i' : A.idx a', homEntry (𝟙 A) a₁ a' i₁ i' * homEntry (𝟙 A) a' a₂ i' i₂) *
          (∑ j' : B.idx b', homEntry (𝟙 B) b₁ b' j₁ j' * homEntry (𝟙 B) b' b₂ j' j₂) := by
      intro b' a'
      calc (∑ j' : B.idx b', ∑ i' : A.idx a',
            (fibRSym a₁ b₁ d * homEntry (𝟙 A) a₁ a' i₁ i' * homEntry (𝟙 B) b₁ b' j₁ j') *
            (fibRSymInv a₂ b₂ d * homEntry (𝟙 B) b' b₂ j' j₂ * homEntry (𝟙 A) a' a₂ i' i₂))
        = ∑ i' : A.idx a', ∑ j' : B.idx b',
            (fibRSym a₁ b₁ d * homEntry (𝟙 A) a₁ a' i₁ i' * homEntry (𝟙 B) b₁ b' j₁ j') *
            (fibRSymInv a₂ b₂ d * homEntry (𝟙 B) b' b₂ j' j₂ * homEntry (𝟙 A) a' a₂ i' i₂) :=
          Finset.sum_comm
      _ = _ := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i' _ => ?_
          refine Finset.sum_congr rfl fun j' _ => ?_
          ring
    simp_rw [hpull]
    by_cases ha : a₁ = a₂ <;> by_cases hb : b₁ = b₂
    · subst ha hb
      rw [Finset.sum_eq_single b₁]
      swap
      · intro b' _ hne
        refine Finset.sum_eq_zero fun a' _ => ?_
        split_ifs <;> simp [sum_homEntry_id_left, hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ b₁)).elim
      rw [Finset.sum_eq_single a₁]
      swap
      · intro a' _ hne; split_ifs <;> simp [sum_homEntry_id_left, hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ a₁)).elim
      have hba : FibAdmB b₁ a₁ d = true := by simpa [fibAdmB_comm] using h₁
      rw [ite_eq_left hba, sum_homEntry_id_left, sum_homEntry_id_left, ite_eq_left rfl, ite_eq_left rfl]
      simp only [homEntry_same, FibFam.id_apply]
      have hR := fibRSym_mul_inv a₁ b₁ d h₁
      by_cases hi : i₁ = i₂ <;> by_cases hj : j₁ = j₂
      · subst hi hj
        have hproof : h₁ = h₂ := Subsingleton.elim _ _
        cases hproof
        simp [hR]
      · have hne : (⟨(a₁, b₁), ⟨h₁⟩, i₁, j₁⟩ : (fibFamTensorObj A B).idx d) ≠ ⟨(a₁, b₁), ⟨h₂⟩, i₂, j₂⟩ := by
          intro h; cases h; exact hj rfl
        simp [hR, hj, hne]
      · have hne : (⟨(a₁, b₁), ⟨h₁⟩, i₁, j₁⟩ : (fibFamTensorObj A B).idx d) ≠ ⟨(a₁, b₁), ⟨h₂⟩, i₂, j₂⟩ := by
          intro h; cases h; exact hi rfl
        simp [hR, hi, hne]
      · have hne : (⟨(a₁, b₁), ⟨h₁⟩, i₁, j₁⟩ : (fibFamTensorObj A B).idx d) ≠ ⟨(a₁, b₁), ⟨h₂⟩, i₂, j₂⟩ := by
          intro h; cases h; exact hi rfl
        simp [hR, hi, hne]
    · rw [Finset.sum_eq_zero]
      · simp only [FibFam.id_apply]
        split_ifs with heq
        · cases heq; exact absurd rfl hb
        · rfl
      · intro b' _
        refine Finset.sum_eq_zero fun a' _ => ?_
        have hz : homEntry (𝟙 B) b₁ b₂ j₁ j₂ = 0 := homEntry_ne (𝟙 B) hb j₁ j₂
        split_ifs <;> try rfl
        by_cases hb1 : b₁ = b'
        · subst hb1; simp [sum_homEntry_id_left, hz]
        · simp [sum_homEntry_id_left, hb1]
    · rw [Finset.sum_eq_zero]
      · simp only [FibFam.id_apply]
        split_ifs with heq
        · cases heq; exact absurd rfl ha
        · rfl
      · intro b' _
        refine Finset.sum_eq_zero fun a' _ => ?_
        have hz : homEntry (𝟙 A) a₁ a₂ i₁ i₂ = 0 := homEntry_ne (𝟙 A) ha i₁ i₂
        split_ifs <;> try rfl
        by_cases ha1 : a₁ = a'
        · subst ha1; simp [sum_homEntry_id_left, hz]
        · simp [sum_homEntry_id_left, ha1]
    · rw [Finset.sum_eq_zero]
      · simp only [FibFam.id_apply]
        split_ifs with heq
        · cases heq; exact absurd rfl ha
        · rfl
      · intro b' _
        refine Finset.sum_eq_zero fun a' _ => ?_
        have hz : homEntry (𝟙 A) a₁ a₂ i₁ i₂ = 0 := homEntry_ne (𝟙 A) ha i₁ i₂
        split_ifs <;> try rfl
        by_cases ha1 : a₁ = a'
        · subst ha1; simp [sum_homEntry_id_left, hz]
        · simp [sum_homEntry_id_left, ha1]
  inv_hom_id := by
    ext d ⟨⟨b₁, a₁⟩, ⟨h₁⟩, j₁, i₁⟩ ⟨⟨b₂, a₂⟩, ⟨h₂⟩, j₂, i₂⟩
    change (∑ x : (fibFamTensorObj A B).idx d,
      (fibRSymInv x.1.1 x.1.2 d * homEntry (𝟙 B) b₁ x.1.2 j₁ x.2.2.2 *
        homEntry (𝟙 A) a₁ x.1.1 i₁ x.2.2.1) *
      (fibRSym x.1.1 x.1.2 d * homEntry (𝟙 A) x.1.1 a₂ x.2.2.1 i₂ *
        homEntry (𝟙 B) x.1.2 b₂ x.2.2.2 j₂)) = _
    rw [sum_fibFamTensorIdx (G := fun a' b' i' j' =>
      (fibRSymInv a' b' d * homEntry (𝟙 B) b₁ b' j₁ j' * homEntry (𝟙 A) a₁ a' i₁ i') *
      (fibRSym a' b' d * homEntry (𝟙 A) a' a₂ i' i₂ * homEntry (𝟙 B) b' b₂ j' j₂))]
    have hpull : ∀ a' b',
        (∑ i' : A.idx a', ∑ j' : B.idx b',
          (fibRSymInv a' b' d * homEntry (𝟙 B) b₁ b' j₁ j' * homEntry (𝟙 A) a₁ a' i₁ i') *
          (fibRSym a' b' d * homEntry (𝟙 A) a' a₂ i' i₂ * homEntry (𝟙 B) b' b₂ j' j₂)) =
        (fibRSymInv a' b' d * fibRSym a' b' d) *
          (∑ i' : A.idx a', homEntry (𝟙 A) a₁ a' i₁ i' * homEntry (𝟙 A) a' a₂ i' i₂) *
          (∑ j' : B.idx b', homEntry (𝟙 B) b₁ b' j₁ j' * homEntry (𝟙 B) b' b₂ j' j₂) := by
      intro a' b'
      simp only [Finset.mul_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i' _ => ?_
      refine Finset.sum_congr rfl fun j' _ => ?_
      ring
    simp_rw [hpull]
    by_cases ha : a₁ = a₂ <;> by_cases hb : b₁ = b₂
    · subst ha hb
      rw [Finset.sum_eq_single a₁]
      swap
      · intro a' _ hne
        refine Finset.sum_eq_zero fun b' _ => ?_
        split_ifs <;> simp [sum_homEntry_id_left, hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ a₁)).elim
      rw [Finset.sum_eq_single b₁]
      swap
      · intro b' _ hne; split_ifs <;> simp [sum_homEntry_id_left, hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ b₁)).elim
      have hab : FibAdmB a₁ b₁ d = true := by simpa [fibAdmB_comm] using h₁
      rw [ite_eq_left hab, sum_homEntry_id_left, sum_homEntry_id_left, ite_eq_left rfl, ite_eq_left rfl]
      simp only [homEntry_same, FibFam.id_apply]
      have hR := fibRSym_inv_mul a₁ b₁ d hab
      by_cases hj : j₁ = j₂ <;> by_cases hi : i₁ = i₂
      · subst hj hi
        have hproof : h₁ = h₂ := Subsingleton.elim _ _
        cases hproof
        simp [hR]
      · have hne : (⟨(b₁, a₁), ⟨h₁⟩, j₁, i₁⟩ : (fibFamTensorObj B A).idx d) ≠ ⟨(b₁, a₁), ⟨h₂⟩, j₂, i₂⟩ := by
          intro h; cases h; exact hi rfl
        simp [hR, hi, hne]
      · have hne : (⟨(b₁, a₁), ⟨h₁⟩, j₁, i₁⟩ : (fibFamTensorObj B A).idx d) ≠ ⟨(b₁, a₁), ⟨h₂⟩, j₂, i₂⟩ := by
          intro h; cases h; exact hj rfl
        simp [hR, hj, hne]
      · have hne : (⟨(b₁, a₁), ⟨h₁⟩, j₁, i₁⟩ : (fibFamTensorObj B A).idx d) ≠ ⟨(b₁, a₁), ⟨h₂⟩, j₂, i₂⟩ := by
          intro h; cases h; exact hj rfl
        simp [hR, hj, hne]
    · rw [Finset.sum_eq_zero]
      · simp only [FibFam.id_apply]
        split_ifs with heq
        · cases heq; exact absurd rfl hb
        · rfl
      · intro a' _
        refine Finset.sum_eq_zero fun b' _ => ?_
        have hz : homEntry (𝟙 B) b₁ b₂ j₁ j₂ = 0 := homEntry_ne (𝟙 B) hb j₁ j₂
        split_ifs <;> try rfl
        by_cases hb1 : b₁ = b'
        · subst hb1; simp [sum_homEntry_id_left, hz]
        · simp [sum_homEntry_id_left, hb1]
    · rw [Finset.sum_eq_zero]
      · simp only [FibFam.id_apply]
        split_ifs with heq
        · cases heq; exact absurd rfl ha
        · rfl
      · intro a' _
        refine Finset.sum_eq_zero fun b' _ => ?_
        have hz : homEntry (𝟙 A) a₁ a₂ i₁ i₂ = 0 := homEntry_ne (𝟙 A) ha i₁ i₂
        split_ifs <;> try rfl
        by_cases ha1 : a₁ = a'
        · subst ha1; simp [sum_homEntry_id_left, hz]
        · simp [sum_homEntry_id_left, ha1]
    · rw [Finset.sum_eq_zero]
      · simp only [FibFam.id_apply]
        split_ifs with heq
        · cases heq; exact absurd rfl ha
        · rfl
      · intro a' _
        refine Finset.sum_eq_zero fun b' _ => ?_
        have hz : homEntry (𝟙 A) a₁ a₂ i₁ i₂ = 0 := homEntry_ne (𝟙 A) ha i₁ i₂
        split_ifs <;> try rfl
        by_cases ha1 : a₁ = a'
        · subst ha1; simp [sum_homEntry_id_left, hz]
        · simp [sum_homEntry_id_left, ha1]

@[simp] theorem homEntry_braiding_same (A B : FibFam) (d : FibObject)
    (x : (fibFamTensorObj A B).idx d) (y : (fibFamTensorObj B A).idx d) :
    homEntry (fibFamBraiding A B).hom d d x y =
      fibRSym x.1.1 x.1.2 d *
        homEntry (𝟙 A) x.1.1 y.1.2 x.2.2.1 y.2.2.2 *
        homEntry (𝟙 B) x.1.2 y.1.1 x.2.2.2 y.2.2.1 := by
  rcases x with ⟨⟨a, b⟩, _, i, j⟩
  rcases y with ⟨⟨b', a'⟩, _, j', i'⟩
  simp [homEntry, fibFamBraiding]

private theorem fibFam_braiding_naturality_right (X : FibFam) {Y Z : FibFam} (f : Y ⟶ Z) :
    X ◁ f ≫ (fibFamBraiding X Z).hom = (fibFamBraiding X Y).hom ≫ f ▷ X := by
  ext d ⟨⟨a₁, b₁⟩, ⟨h₁⟩, i₁, j₁⟩ ⟨⟨c₂, a₂⟩, ⟨h₂⟩, k₂, i₂⟩
  simp only [FibFam.comp_apply]
  change (∑ z : (fibFamTensorObj X Z).idx d,
      (homEntry (𝟙 X) a₁ z.1.1 i₁ z.2.2.1 * homEntry f b₁ z.1.2 j₁ z.2.2.2) *
      (fibRSym z.1.1 z.1.2 d * homEntry (𝟙 X) z.1.1 a₂ z.2.2.1 i₂ *
        homEntry (𝟙 Z) z.1.2 c₂ z.2.2.2 k₂)) =
    ∑ w : (fibFamTensorObj Y X).idx d,
      (fibRSym a₁ b₁ d * homEntry (𝟙 X) a₁ w.1.2 i₁ w.2.2.2 *
        homEntry (𝟙 Y) b₁ w.1.1 j₁ w.2.2.1) *
        (homEntry f w.1.1 c₂ w.2.2.1 k₂ * homEntry (𝟙 X) w.1.2 a₂ w.2.2.2 i₂)
  rw [sum_fibFamTensorIdx (G := fun a' c' i' k' =>
    (homEntry (𝟙 X) a₁ a' i₁ i' * homEntry f b₁ c' j₁ k') *
    (fibRSym a' c' d * homEntry (𝟙 X) a' a₂ i' i₂ * homEntry (𝟙 Z) c' c₂ k' k₂))]
  rw [sum_fibFamTensorIdx (G := fun b' a' j' i' =>
    (fibRSym a₁ b₁ d * homEntry (𝟙 X) a₁ a' i₁ i' * homEntry (𝟙 Y) b₁ b' j₁ j') *
    (homEntry f b' c₂ j' k₂ * homEntry (𝟙 X) a' a₂ i' i₂))]
  by_cases ha : a₁ = a₂ <;> by_cases hbc : b₁ = c₂
  · subst ha hbc
    rw [Finset.sum_eq_single a₁]
    swap
    · intro a' _ hne
      refine Finset.sum_eq_zero fun c' _ => ?_
      split_ifs <;> simp [homEntry_ne _ hne]
    swap
    · intro hm; exact (hm (Finset.mem_univ a₁)).elim
    rw [Finset.sum_eq_single b₁]
    swap
    · intro c' _ hne; split_ifs <;> simp [homEntry_ne _ hne.symm]
    swap
    · intro hm; exact (hm (Finset.mem_univ b₁)).elim
    rw [ite_eq_left h₁]
    symm
    rw [Finset.sum_eq_single b₁]
    swap
    · intro b' _ hne
      refine Finset.sum_eq_zero fun a' _ => ?_
      split_ifs <;> simp [homEntry_ne _ hne]
    swap
    · intro hm; exact (hm (Finset.mem_univ b₁)).elim
    rw [Finset.sum_eq_single a₁]
    swap
    · intro a' _ hne; split_ifs <;> simp [homEntry_ne _ hne]
    swap
    · intro hm; exact (hm (Finset.mem_univ a₁)).elim
    rw [ite_eq_left h₂]
    have hL : (∑ i' : X.idx a₁, ∑ k' : Z.idx b₁,
          (homEntry (𝟙 X) a₁ a₁ i₁ i' * homEntry f b₁ b₁ j₁ k') *
          (fibRSym a₁ b₁ d * homEntry (𝟙 X) a₁ a₁ i' i₂ * homEntry (𝟙 Z) b₁ b₁ k' k₂)) =
        fibRSym a₁ b₁ d *
          (∑ i' : X.idx a₁, homEntry (𝟙 X) a₁ a₁ i₁ i' * homEntry (𝟙 X) a₁ a₁ i' i₂) *
          (∑ k' : Z.idx b₁, homEntry f b₁ b₁ j₁ k' * homEntry (𝟙 Z) b₁ b₁ k' k₂) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i' _ => ?_
      refine Finset.sum_congr rfl fun k' _ => ?_
      ring
    have hR : (∑ j' : Y.idx b₁, ∑ i' : X.idx a₁,
          (fibRSym a₁ b₁ d * homEntry (𝟙 X) a₁ a₁ i₁ i' * homEntry (𝟙 Y) b₁ b₁ j₁ j') *
          (homEntry f b₁ b₁ j' k₂ * homEntry (𝟙 X) a₁ a₁ i' i₂)) =
        fibRSym a₁ b₁ d *
          (∑ i' : X.idx a₁, homEntry (𝟙 X) a₁ a₁ i₁ i' * homEntry (𝟙 X) a₁ a₁ i' i₂) *
          (∑ j' : Y.idx b₁, homEntry (𝟙 Y) b₁ b₁ j₁ j' * homEntry f b₁ b₁ j' k₂) := by
      calc (∑ j' : Y.idx b₁, ∑ i' : X.idx a₁,
            (fibRSym a₁ b₁ d * homEntry (𝟙 X) a₁ a₁ i₁ i' * homEntry (𝟙 Y) b₁ b₁ j₁ j') *
            (homEntry f b₁ b₁ j' k₂ * homEntry (𝟙 X) a₁ a₁ i' i₂))
        = ∑ i' : X.idx a₁, ∑ j' : Y.idx b₁,
            (fibRSym a₁ b₁ d * homEntry (𝟙 X) a₁ a₁ i₁ i' * homEntry (𝟙 Y) b₁ b₁ j₁ j') *
            (homEntry f b₁ b₁ j' k₂ * homEntry (𝟙 X) a₁ a₁ i' i₂) := Finset.sum_comm
      _ = _ := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i' _ => ?_
          refine Finset.sum_congr rfl fun j' _ => ?_
          ring
    rw [hL, hR]
    simp only [sum_homEntry_id_right, sum_homEntry_id_left, ite_true]
  all_goals
    have hzL : (∑ a' : FibObject, ∑ c' : FibObject,
          if FibAdmB a' c' d = true then
            ∑ i' : X.idx a', ∑ k' : Z.idx c',
              (homEntry (𝟙 X) a₁ a' i₁ i' * homEntry f b₁ c' j₁ k') *
              (fibRSym a' c' d * homEntry (𝟙 X) a' a₂ i' i₂ * homEntry (𝟙 Z) c' c₂ k' k₂)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun c' _ => ?_
      split_ifs <;> try rfl
      refine Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun k' _ => ?_
      by_cases ha1 : a₁ = a'
      · by_cases ha2 : a' = a₂
        · subst ha1 ha2
          by_cases hbc1 : b₁ = c'
          · subst hbc1
            first
            | exact (ha rfl).elim
            | simp [homEntry_ne _ hbc]
          · simp [homEntry_ne _ hbc1]
        · simp [homEntry_ne _ ha2]
      · simp [homEntry_ne _ ha1]
    have hzR : (∑ b' : FibObject, ∑ a' : FibObject,
          if FibAdmB b' a' d = true then
            ∑ j' : Y.idx b', ∑ i' : X.idx a',
              (fibRSym a₁ b₁ d * homEntry (𝟙 X) a₁ a' i₁ i' * homEntry (𝟙 Y) b₁ b' j₁ j') *
              (homEntry f b' c₂ j' k₂ * homEntry (𝟙 X) a' a₂ i' i₂)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun a' _ => ?_
      split_ifs <;> try rfl
      refine Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun i' _ => ?_
      by_cases ha1 : a₁ = a'
      · by_cases ha2 : a' = a₂
        · subst ha1 ha2
          by_cases hbc1 : b₁ = b'
          · subst hbc1
            first
            | exact (ha rfl).elim
            | simp [homEntry_ne _ hbc]
          · simp [homEntry_ne _ hbc1]
        · simp [homEntry_ne _ ha2]
      · simp [homEntry_ne _ ha1]
    rw [hzL, hzR]

private theorem fibFam_braiding_naturality_left {X Y : FibFam} (f : X ⟶ Y) (Z : FibFam) :
    f ▷ Z ≫ (fibFamBraiding Y Z).hom = (fibFamBraiding X Z).hom ≫ Z ◁ f := by
  ext d ⟨⟨a₁, c₁⟩, ⟨h₁⟩, i₁, k₁⟩ ⟨⟨c₂, b₂⟩, ⟨h₂⟩, k₂, j₂⟩
  simp only [FibFam.comp_apply]
  change (∑ z : (fibFamTensorObj Y Z).idx d,
      (homEntry f a₁ z.1.1 i₁ z.2.2.1 * homEntry (𝟙 Z) c₁ z.1.2 k₁ z.2.2.2) *
      (fibRSym z.1.1 z.1.2 d * homEntry (𝟙 Y) z.1.1 b₂ z.2.2.1 j₂ *
        homEntry (𝟙 Z) z.1.2 c₂ z.2.2.2 k₂)) =
    ∑ w : (fibFamTensorObj Z X).idx d,
      (fibRSym a₁ c₁ d * homEntry (𝟙 X) a₁ w.1.2 i₁ w.2.2.2 *
        homEntry (𝟙 Z) c₁ w.1.1 k₁ w.2.2.1) *
        (homEntry (𝟙 Z) w.1.1 c₂ w.2.2.1 k₂ * homEntry f w.1.2 b₂ w.2.2.2 j₂)
  rw [sum_fibFamTensorIdx (G := fun b' c' j' k' =>
    (homEntry f a₁ b' i₁ j' * homEntry (𝟙 Z) c₁ c' k₁ k') *
    (fibRSym b' c' d * homEntry (𝟙 Y) b' b₂ j' j₂ * homEntry (𝟙 Z) c' c₂ k' k₂))]
  rw [sum_fibFamTensorIdx (G := fun c' a' k' i' =>
    (fibRSym a₁ c₁ d * homEntry (𝟙 X) a₁ a' i₁ i' * homEntry (𝟙 Z) c₁ c' k₁ k') *
    (homEntry (𝟙 Z) c' c₂ k' k₂ * homEntry f a' b₂ i' j₂))]
  by_cases hab : a₁ = b₂ <;> by_cases hc : c₁ = c₂
  · subst hab hc
    rw [Finset.sum_eq_single a₁]
    swap
    · intro b' _ hne
      refine Finset.sum_eq_zero fun c' _ => ?_
      split_ifs <;> simp [homEntry_ne _ hne.symm]
    swap
    · intro hm; exact (hm (Finset.mem_univ a₁)).elim
    rw [Finset.sum_eq_single c₁]
    swap
    · intro c' _ hne; split_ifs <;> simp [homEntry_ne _ hne]
    swap
    · intro hm; exact (hm (Finset.mem_univ c₁)).elim
    rw [ite_eq_left h₁]
    symm
    rw [Finset.sum_eq_single c₁]
    swap
    · intro c' _ hne
      refine Finset.sum_eq_zero fun a' _ => ?_
      split_ifs <;> simp [homEntry_ne _ hne]
    swap
    · intro hm; exact (hm (Finset.mem_univ c₁)).elim
    rw [Finset.sum_eq_single a₁]
    swap
    · intro a' _ hne; split_ifs <;> simp [homEntry_ne _ hne]
    swap
    · intro hm; exact (hm (Finset.mem_univ a₁)).elim
    rw [ite_eq_left h₂]
    have hL : (∑ j' : Y.idx a₁, ∑ k' : Z.idx c₁,
          (homEntry f a₁ a₁ i₁ j' * homEntry (𝟙 Z) c₁ c₁ k₁ k') *
          (fibRSym a₁ c₁ d * homEntry (𝟙 Y) a₁ a₁ j' j₂ * homEntry (𝟙 Z) c₁ c₁ k' k₂)) =
        fibRSym a₁ c₁ d *
          (∑ j' : Y.idx a₁, homEntry f a₁ a₁ i₁ j' * homEntry (𝟙 Y) a₁ a₁ j' j₂) *
          (∑ k' : Z.idx c₁, homEntry (𝟙 Z) c₁ c₁ k₁ k' * homEntry (𝟙 Z) c₁ c₁ k' k₂) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ => ?_
      refine Finset.sum_congr rfl fun k' _ => ?_
      ring
    have hR : (∑ k' : Z.idx c₁, ∑ i' : X.idx a₁,
          (fibRSym a₁ c₁ d * homEntry (𝟙 X) a₁ a₁ i₁ i' * homEntry (𝟙 Z) c₁ c₁ k₁ k') *
          (homEntry (𝟙 Z) c₁ c₁ k' k₂ * homEntry f a₁ a₁ i' j₂)) =
        fibRSym a₁ c₁ d *
          (∑ i' : X.idx a₁, homEntry (𝟙 X) a₁ a₁ i₁ i' * homEntry f a₁ a₁ i' j₂) *
          (∑ k' : Z.idx c₁, homEntry (𝟙 Z) c₁ c₁ k₁ k' * homEntry (𝟙 Z) c₁ c₁ k' k₂) := by
      calc (∑ k' : Z.idx c₁, ∑ i' : X.idx a₁,
            (fibRSym a₁ c₁ d * homEntry (𝟙 X) a₁ a₁ i₁ i' * homEntry (𝟙 Z) c₁ c₁ k₁ k') *
            (homEntry (𝟙 Z) c₁ c₁ k' k₂ * homEntry f a₁ a₁ i' j₂))
        = ∑ i' : X.idx a₁, ∑ k' : Z.idx c₁,
            (fibRSym a₁ c₁ d * homEntry (𝟙 X) a₁ a₁ i₁ i' * homEntry (𝟙 Z) c₁ c₁ k₁ k') *
            (homEntry (𝟙 Z) c₁ c₁ k' k₂ * homEntry f a₁ a₁ i' j₂) := Finset.sum_comm
      _ = _ := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i' _ => ?_
          refine Finset.sum_congr rfl fun k' _ => ?_
          ring
    rw [hL, hR]
    simp only [sum_homEntry_id_right, sum_homEntry_id_left, ite_true]
  all_goals
    have hzL : (∑ b' : FibObject, ∑ c' : FibObject,
          if FibAdmB b' c' d = true then
            ∑ j' : Y.idx b', ∑ k' : Z.idx c',
              (homEntry f a₁ b' i₁ j' * homEntry (𝟙 Z) c₁ c' k₁ k') *
              (fibRSym b' c' d * homEntry (𝟙 Y) b' b₂ j' j₂ * homEntry (𝟙 Z) c' c₂ k' k₂)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun c' _ => ?_
      split_ifs <;> try rfl
      refine Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun k' _ => ?_
      by_cases hc1 : c₁ = c'
      · by_cases hc2 : c' = c₂
        · subst hc1 hc2
          by_cases hab1 : a₁ = b'
          · subst hab1
            first
            | exact (hc rfl).elim
            | simp [homEntry_ne _ hab]
          · simp [homEntry_ne _ hab1]
        · simp [homEntry_ne _ hc2]
      · simp [homEntry_ne _ hc1]
    have hzR : (∑ c' : FibObject, ∑ a' : FibObject,
          if FibAdmB c' a' d = true then
            ∑ k' : Z.idx c', ∑ i' : X.idx a',
              (fibRSym a₁ c₁ d * homEntry (𝟙 X) a₁ a' i₁ i' * homEntry (𝟙 Z) c₁ c' k₁ k') *
              (homEntry (𝟙 Z) c' c₂ k' k₂ * homEntry f a' b₂ i' j₂)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun c' _ => Finset.sum_eq_zero fun a' _ => ?_
      split_ifs <;> try rfl
      refine Finset.sum_eq_zero fun k' _ => Finset.sum_eq_zero fun i' _ => ?_
      by_cases hc1 : c₁ = c'
      · by_cases hc2 : c' = c₂
        · subst hc1 hc2
          by_cases hab1 : a₁ = a'
          · subst hab1
            first
            | exact (hc rfl).elim
            | simp [homEntry_ne _ hab]
          · simp [homEntry_ne _ hab1]
        · simp [homEntry_ne _ hc2]
      · simp [homEntry_ne _ hc1]
    rw [hzL, hzR]

private theorem fibFam_hex_fwd_tail (X Y Z : FibFam) {t : FibObject}
    (z₁ : (fibFamTensorObj X (fibFamTensorObj Y Z)).idx t)
    {b' g c' a' : FibObject} (hg₂ : FibAdmB b' g t = true) (hg₁ : FibAdmB c' a' g = true)
    (j' : Y.idx b') (k' : Z.idx c') (i' : X.idx a') :
    ((fibFamBraiding X (fibFamTensorObj Y Z)).hom ≫ (α_ Y Z X).hom) t z₁
        ⟨⟨b', g⟩, ⟨hg₂⟩, j', ⟨⟨c', a'⟩, ⟨hg₁⟩, k', i'⟩⟩ =
      fibRSym z₁.1.1 z₁.1.2 t *
        fibFSym z₁.2.2.2.1.1 z₁.2.2.2.1.2 z₁.1.1 t z₁.1.2 g *
        homEntry (𝟙 X) z₁.1.1 a' z₁.2.2.1 i' *
        homEntry (𝟙 Y) z₁.2.2.2.1.1 b' z₁.2.2.2.2.2.1 j' *
        homEntry (𝟙 Z) z₁.2.2.2.1.2 c' z₁.2.2.2.2.2.2 k' := by
  rcases z₁ with ⟨⟨a₁, f⟩, ⟨hf⟩, i₁, ⟨⟨b₁, c₁⟩, ⟨hbc₁⟩, j₁, k₁⟩⟩
  simp only [FibFam.comp_apply]
  change (∑ z₂ : (fibFamTensorObj (fibFamTensorObj Y Z) X).idx t,
      (fibRSym a₁ f t * homEntry (𝟙 X) a₁ z₂.1.2 i₁ z₂.2.2.2 *
        homEntry (𝟙 (fibFamTensorObj Y Z)) f z₂.1.1 ⟨⟨b₁, c₁⟩, ⟨hbc₁⟩, j₁, k₁⟩ z₂.2.2.1) *
      (fibFSym z₂.2.2.1.1.1 z₂.2.2.1.1.2 z₂.1.2 t z₂.1.1 g *
        homEntry (𝟙 Y) z₂.2.2.1.1.1 b' z₂.2.2.1.2.2.1 j' *
        homEntry (𝟙 Z) z₂.2.2.1.1.2 c' z₂.2.2.1.2.2.2 k' *
        homEntry (𝟙 X) z₂.1.2 a' z₂.2.2.2 i')) = _
  rw [sum_fibFamTensorIdx (A := fibFamTensorObj Y Z) (B := X) (c := t) (G := fun f₂ a₂ yz₂ i₂ =>
    (fibRSym a₁ f t * homEntry (𝟙 X) a₁ a₂ i₁ i₂ *
      homEntry (𝟙 (fibFamTensorObj Y Z)) f f₂ ⟨⟨b₁, c₁⟩, ⟨hbc₁⟩, j₁, k₁⟩ yz₂) *
    (fibFSym yz₂.1.1 yz₂.1.2 a₂ t f₂ g *
      homEntry (𝟙 Y) yz₂.1.1 b' yz₂.2.2.1 j' *
      homEntry (𝟙 Z) yz₂.1.2 c' yz₂.2.2.2 k' *
      homEntry (𝟙 X) a₂ a' i₂ i'))]
  rw [Finset.sum_eq_single f]
  swap
  · intro f₂ _ hne
    refine Finset.sum_eq_zero fun a₂ _ => ?_
    split_ifs <;> simp [homEntry_ne _ hne.symm]
  swap
  · intro hm; exact (hm (Finset.mem_univ f)).elim
  rw [Finset.sum_eq_single a₁]
  swap
  · intro a₂ _ hne; split_ifs <;> simp [homEntry_ne _ hne.symm]
  swap
  · intro hm; exact (hm (Finset.mem_univ a₁)).elim
  have hfa : FibAdmB f a₁ t = true := by simpa [fibAdmB_comm] using hf
  rw [ite_eq_left hfa]
  rw [Finset.sum_eq_single ⟨⟨b₁, c₁⟩, ⟨hbc₁⟩, j₁, k₁⟩]
  swap
  · intro yz₂ _ hne
    refine Finset.sum_eq_zero fun i₂ _ => ?_
    simp [homEntry_same, FibFam.id_apply, hne.symm]
  swap
  · intro hm; exact (hm (Finset.mem_univ _)).elim
  simp only [homEntry_same, FibFam.id_apply, ↓reduceIte, mul_one]
  simp only [← FibFam.id_apply, ← homEntry_same]
  calc
    (∑ i₂ : X.idx a₁,
        (fibRSym a₁ f t * homEntry (𝟙 X) a₁ a₁ i₁ i₂) *
        (fibFSym b₁ c₁ a₁ t f g * homEntry (𝟙 Y) b₁ b' j₁ j' *
          homEntry (𝟙 Z) c₁ c' k₁ k' * homEntry (𝟙 X) a₁ a' i₂ i'))
    = (∑ i₂ : X.idx a₁, homEntry (𝟙 X) a₁ a₁ i₁ i₂ * homEntry (𝟙 X) a₁ a' i₂ i') *
        (fibRSym a₁ f t * fibFSym b₁ c₁ a₁ t f g *
          homEntry (𝟙 Y) b₁ b' j₁ j' * homEntry (𝟙 Z) c₁ c' k₁ k') := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i₂ _ => ?_
      ring
    _ = _ := by
      rw [sum_homEntry_id_left, ite_eq_left rfl]
      ring

private theorem fibFam_hex_fwd_rhs_tail (X Y Z : FibFam) {t : FibObject}
    (z₁ : (fibFamTensorObj (fibFamTensorObj Y X) Z).idx t)
    {b' g c' a' : FibObject} (hg₂ : FibAdmB b' g t = true) (hg₁ : FibAdmB c' a' g = true)
    (j' : Y.idx b') (k' : Z.idx c') (i' : X.idx a') :
    ((α_ Y X Z).hom ≫ Y ◁ (fibFamBraiding X Z).hom) t z₁
        ⟨⟨b', g⟩, ⟨hg₂⟩, j', ⟨⟨c', a'⟩, ⟨hg₁⟩, k', i'⟩⟩ =
      fibFSym z₁.2.2.1.1.1 z₁.2.2.1.1.2 z₁.1.2 t z₁.1.1 g *
        fibRSym a' c' g *
        homEntry (𝟙 Y) z₁.2.2.1.1.1 b' z₁.2.2.1.2.2.1 j' *
        homEntry (𝟙 X) z₁.2.2.1.1.2 a' z₁.2.2.1.2.2.2 i' *
        homEntry (𝟙 Z) z₁.1.2 c' z₁.2.2.2 k' := by
  rcases z₁ with ⟨⟨e₁, c₁⟩, ⟨he₂⟩, ⟨⟨b₁, a₁⟩, ⟨he₁⟩, j₁, i₁⟩, k₁⟩
  simp only [FibFam.comp_apply]
  change (∑ z₂ : (fibFamTensorObj Y (fibFamTensorObj X Z)).idx t,
      (fibFSym b₁ a₁ c₁ t e₁ z₂.1.2 *
        homEntry (𝟙 Y) b₁ z₂.1.1 j₁ z₂.2.2.1 *
        homEntry (𝟙 X) a₁ z₂.2.2.2.1.1 i₁ z₂.2.2.2.2.2.1 *
        homEntry (𝟙 Z) c₁ z₂.2.2.2.1.2 k₁ z₂.2.2.2.2.2.2) *
      (homEntry (𝟙 Y) z₂.1.1 b' z₂.2.2.1 j' *
        homEntry (fibFamBraiding X Z).hom z₂.1.2 g z₂.2.2.2 ⟨⟨c', a'⟩, ⟨hg₁⟩, k', i'⟩)) = _
  rw [sum_fibFamTensorIdx (A := Y) (B := fibFamTensorObj X Z) (c := t) (G := fun b₂ g₂ j₂ xz₂ =>
    (fibFSym b₁ a₁ c₁ t e₁ g₂ *
      homEntry (𝟙 Y) b₁ b₂ j₁ j₂ *
      homEntry (𝟙 X) a₁ xz₂.1.1 i₁ xz₂.2.2.1 *
      homEntry (𝟙 Z) c₁ xz₂.1.2 k₁ xz₂.2.2.2) *
    (homEntry (𝟙 Y) b₂ b' j₂ j' *
      homEntry (fibFamBraiding X Z).hom g₂ g xz₂ ⟨⟨c', a'⟩, ⟨hg₁⟩, k', i'⟩))]
  rw [Finset.sum_eq_single b']
  swap
  · intro b₂ _ hne
    refine Finset.sum_eq_zero fun g₂ _ => ?_
    split_ifs <;> simp [homEntry_ne _ hne]
  swap
  · intro hm; exact (hm (Finset.mem_univ b')).elim
  rw [Finset.sum_eq_single g]
  swap
  · intro g₂ _ hne; split_ifs <;> simp [homEntry_ne _ hne]
  swap
  · intro hm; exact (hm (Finset.mem_univ g)).elim
  rw [ite_eq_left hg₂]
  have hinner : ∀ j₂ : Y.idx b',
      (∑ xz₂ : (fibFamTensorObj X Z).idx g,
        (fibFSym b₁ a₁ c₁ t e₁ g *
          homEntry (𝟙 Y) b₁ b' j₁ j₂ *
          homEntry (𝟙 X) a₁ xz₂.1.1 i₁ xz₂.2.2.1 *
          homEntry (𝟙 Z) c₁ xz₂.1.2 k₁ xz₂.2.2.2) *
        (homEntry (𝟙 Y) b' b' j₂ j' *
          homEntry (fibFamBraiding X Z).hom g g xz₂ ⟨⟨c', a'⟩, ⟨hg₁⟩, k', i'⟩)) =
      (homEntry (𝟙 Y) b₁ b' j₁ j₂ * homEntry (𝟙 Y) b' b' j₂ j') *
        (fibFSym b₁ a₁ c₁ t e₁ g * fibRSym a' c' g *
          homEntry (𝟙 X) a₁ a' i₁ i' * homEntry (𝟙 Z) c₁ c' k₁ k') := by
    intro j₂
    simp only [homEntry_braiding_same]
    rw [sum_fibFamTensorIdx (A := X) (B := Z) (c := g) (G := fun a₂ c₂ i₂ k₂ =>
      (fibFSym b₁ a₁ c₁ t e₁ g *
        homEntry (𝟙 Y) b₁ b' j₁ j₂ *
        homEntry (𝟙 X) a₁ a₂ i₁ i₂ *
        homEntry (𝟙 Z) c₁ c₂ k₁ k₂) *
      (homEntry (𝟙 Y) b' b' j₂ j' *
        (fibRSym a₂ c₂ g * homEntry (𝟙 X) a₂ a' i₂ i' * homEntry (𝟙 Z) c₂ c' k₂ k')))]
    rw [Finset.sum_eq_single a']
    swap
    · intro a₂ _ hne
      refine Finset.sum_eq_zero fun c₂ _ => ?_
      split_ifs <;> simp [homEntry_ne _ hne]
    swap
    · intro hm; exact (hm (Finset.mem_univ a')).elim
    rw [Finset.sum_eq_single c']
    swap
    · intro c₂ _ hne; split_ifs <;> simp [homEntry_ne _ hne]
    swap
    · intro hm; exact (hm (Finset.mem_univ c')).elim
    have hac : FibAdmB a' c' g = true := by simpa [fibAdmB_comm] using hg₁
    rw [ite_eq_left hac]
    calc
      (∑ i₂ : X.idx a', ∑ k₂ : Z.idx c',
          (fibFSym b₁ a₁ c₁ t e₁ g * homEntry (𝟙 Y) b₁ b' j₁ j₂ *
            homEntry (𝟙 X) a₁ a' i₁ i₂ * homEntry (𝟙 Z) c₁ c' k₁ k₂) *
          (homEntry (𝟙 Y) b' b' j₂ j' *
            (fibRSym a' c' g * homEntry (𝟙 X) a' a' i₂ i' * homEntry (𝟙 Z) c' c' k₂ k')))
      = (∑ i₂ : X.idx a', homEntry (𝟙 X) a₁ a' i₁ i₂ * homEntry (𝟙 X) a' a' i₂ i') *
          (∑ k₂ : Z.idx c', homEntry (𝟙 Z) c₁ c' k₁ k₂ * homEntry (𝟙 Z) c' c' k₂ k') *
          ((homEntry (𝟙 Y) b₁ b' j₁ j₂ * homEntry (𝟙 Y) b' b' j₂ j') *
            (fibFSym b₁ a₁ c₁ t e₁ g * fibRSym a' c' g)) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i₂ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k₂ _ => ?_
        ring
      _ = _ := by
        rw [sum_homEntry_id_right, sum_homEntry_id_right]
        by_cases ha : a₁ = a' <;> by_cases hc : c₁ = c'
        · subst ha hc; simp only [ite_true]; ring
        all_goals simp [ha, hc, homEntry_ne]
  simp_rw [hinner]
  rw [← Finset.sum_mul, sum_homEntry_id_right]
  by_cases hb : b₁ = b'
  · simp [hb]; ring
  · simp [hb, homEntry_ne _ hb]

private theorem fibFam_hexagon_forward (X Y Z : FibFam) :
    (α_ X Y Z).hom ≫ (fibFamBraiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      ((fibFamBraiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (fibFamBraiding X Z).hom) := by
  dsimp only [CategoryTheory.MonoidalCategory.tensorObj,
    CategoryTheory.MonoidalCategory.associator,
    CategoryTheory.MonoidalCategory.whiskerRight,
    CategoryTheory.MonoidalCategory.whiskerLeft]
  ext t ⟨⟨e, c⟩, ⟨he₂⟩, ⟨⟨a, b⟩, ⟨he₁⟩, i, j⟩, k⟩
    ⟨⟨b', g⟩, ⟨hg₂⟩, j', ⟨⟨c', a'⟩, ⟨hg₁⟩, k', i'⟩⟩
  rw [FibFam.comp_apply, FibFam.comp_apply]
  have hL :
      (∑ z₁ : (fibFamTensorObj X (fibFamTensorObj Y Z)).idx t,
        (fibFamAssociator X Y Z).hom t
          ⟨⟨e, c⟩, ⟨he₂⟩, ⟨⟨a, b⟩, ⟨he₁⟩, i, j⟩, k⟩ z₁ *
        ((fibFamBraiding X (fibFamTensorObj Y Z)).hom ≫ (fibFamAssociator Y Z X).hom) t z₁
          ⟨⟨b', g⟩, ⟨hg₂⟩, j', ⟨⟨c', a'⟩, ⟨hg₁⟩, k', i'⟩⟩) =
      (∑ f : FibObject, fibFSym a b c t e f * fibRSym a f t * fibFSym b c a t f g) *
        homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k' := by
    have htail : ∀ z₁,
        ((fibFamBraiding X (fibFamTensorObj Y Z)).hom ≫ (fibFamAssociator Y Z X).hom) t z₁
          ⟨⟨b', g⟩, ⟨hg₂⟩, j', ⟨⟨c', a'⟩, ⟨hg₁⟩, k', i'⟩⟩ =
        fibRSym z₁.1.1 z₁.1.2 t *
          fibFSym z₁.2.2.2.1.1 z₁.2.2.2.1.2 z₁.1.1 t z₁.1.2 g *
          homEntry (𝟙 X) z₁.1.1 a' z₁.2.2.1 i' *
          homEntry (𝟙 Y) z₁.2.2.2.1.1 b' z₁.2.2.2.2.2.1 j' *
          homEntry (𝟙 Z) z₁.2.2.2.1.2 c' z₁.2.2.2.2.2.2 k' :=
      fun z₁ => fibFam_hex_fwd_tail X Y Z z₁ hg₂ hg₁ j' k' i'
    simp_rw [htail]
    dsimp only [fibFamAssociator]
    rw [sum_fibFamTensorIdx (A := X) (B := fibFamTensorObj Y Z) (c := t) (G := fun a₁ f i₁ yz₁ =>
      (fibFSym a b c t e f *
        homEntry (𝟙 X) a a₁ i i₁ *
        homEntry (𝟙 Y) b yz₁.1.1 j yz₁.2.2.1 *
        homEntry (𝟙 Z) c yz₁.1.2 k yz₁.2.2.2) *
      (fibRSym a₁ f t *
        fibFSym yz₁.1.1 yz₁.1.2 a₁ t f g *
        homEntry (𝟙 X) a₁ a' i₁ i' *
        homEntry (𝟙 Y) yz₁.1.1 b' yz₁.2.2.1 j' *
        homEntry (𝟙 Z) yz₁.1.2 c' yz₁.2.2.2 k'))]
    rw [Finset.sum_eq_single a]
    swap
    · intro a₁ _ hne
      refine Finset.sum_eq_zero fun f _ => ?_
      split_ifs <;> simp [homEntry_ne _ hne.symm]
    swap
    · intro hm; exact (hm (Finset.mem_univ a)).elim
    have hfterm : ∀ f : FibObject,
        (if FibAdmB a f t = true then
          ∑ i₁ : X.idx a, ∑ yz₁ : (fibFamTensorObj Y Z).idx f,
            (fibFSym a b c t e f *
              homEntry (𝟙 X) a a i i₁ *
              homEntry (𝟙 Y) b yz₁.1.1 j yz₁.2.2.1 *
              homEntry (𝟙 Z) c yz₁.1.2 k yz₁.2.2.2) *
            (fibRSym a f t *
              fibFSym yz₁.1.1 yz₁.1.2 a t f g *
              homEntry (𝟙 X) a a' i₁ i' *
              homEntry (𝟙 Y) yz₁.1.1 b' yz₁.2.2.1 j' *
              homEntry (𝟙 Z) yz₁.1.2 c' yz₁.2.2.2 k')
        else 0) =
        (fibFSym a b c t e f * fibRSym a f t * fibFSym b c a t f g) *
          homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k' := by
      intro f
      by_cases haf : FibAdmB a f t = true
      · rw [ite_eq_left haf]
        have hyz : ∀ i₁ : X.idx a,
            (∑ yz₁ : (fibFamTensorObj Y Z).idx f,
              (fibFSym a b c t e f *
                homEntry (𝟙 X) a a i i₁ *
                homEntry (𝟙 Y) b yz₁.1.1 j yz₁.2.2.1 *
                homEntry (𝟙 Z) c yz₁.1.2 k yz₁.2.2.2) *
              (fibRSym a f t *
                fibFSym yz₁.1.1 yz₁.1.2 a t f g *
                homEntry (𝟙 X) a a' i₁ i' *
                homEntry (𝟙 Y) yz₁.1.1 b' yz₁.2.2.1 j' *
                homEntry (𝟙 Z) yz₁.1.2 c' yz₁.2.2.2 k')) =
            (homEntry (𝟙 X) a a i i₁ * homEntry (𝟙 X) a a' i₁ i') *
              (fibFSym a b c t e f * fibRSym a f t * fibFSym b c a t f g *
                homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k') := by
          intro i₁
          rw [sum_fibFamTensorIdx (A := Y) (B := Z) (c := f) (G := fun b₁ c₁ j₁ k₁ =>
            (fibFSym a b c t e f *
              homEntry (𝟙 X) a a i i₁ *
              homEntry (𝟙 Y) b b₁ j j₁ *
              homEntry (𝟙 Z) c c₁ k k₁) *
            (fibRSym a f t *
              fibFSym b₁ c₁ a t f g *
              homEntry (𝟙 X) a a' i₁ i' *
              homEntry (𝟙 Y) b₁ b' j₁ j' *
              homEntry (𝟙 Z) c₁ c' k₁ k'))]
          rw [Finset.sum_eq_single b]
          swap
          · intro b₁ _ hne
            refine Finset.sum_eq_zero fun c₁ _ => ?_
            split_ifs <;> simp [homEntry_ne _ hne.symm]
          swap
          · intro hm; exact (hm (Finset.mem_univ b)).elim
          rw [Finset.sum_eq_single c]
          swap
          · intro c₁ _ hne; split_ifs <;> simp [homEntry_ne _ hne.symm]
          swap
          · intro hm; exact (hm (Finset.mem_univ c)).elim
          by_cases hbc : FibAdmB b c f = true
          · rw [ite_eq_left hbc]
            calc
              (∑ j₁ : Y.idx b, ∑ k₁ : Z.idx c,
                  (fibFSym a b c t e f * homEntry (𝟙 X) a a i i₁ *
                    homEntry (𝟙 Y) b b j j₁ * homEntry (𝟙 Z) c c k k₁) *
                  (fibRSym a f t * fibFSym b c a t f g *
                    homEntry (𝟙 X) a a' i₁ i' * homEntry (𝟙 Y) b b' j₁ j' *
                    homEntry (𝟙 Z) c c' k₁ k'))
              = (∑ j₁ : Y.idx b, homEntry (𝟙 Y) b b j j₁ * homEntry (𝟙 Y) b b' j₁ j') *
                  (∑ k₁ : Z.idx c, homEntry (𝟙 Z) c c k k₁ * homEntry (𝟙 Z) c c' k₁ k') *
                  ((homEntry (𝟙 X) a a i i₁ * homEntry (𝟙 X) a a' i₁ i') *
                    (fibFSym a b c t e f * fibRSym a f t * fibFSym b c a t f g)) := by
                rw [Finset.sum_mul, Finset.sum_mul]
                refine Finset.sum_congr rfl fun j₁ _ => ?_
                rw [Finset.mul_sum, Finset.sum_mul]
                refine Finset.sum_congr rfl fun k₁ _ => ?_
                ring
              _ = _ := by
                rw [sum_homEntry_id_left, sum_homEntry_id_left, ite_eq_left rfl, ite_eq_left rfl]
                ring
          · rw [ite_eq_right hbc]
            have hz : fibFSym a b c t e f = 0 := fibFSym_zero_of_adm (by simp [hbc])
            simp [hz]
        simp_rw [hyz]
        rw [← Finset.sum_mul, sum_homEntry_id_left, ite_eq_left rfl]
        ring
      · rw [ite_eq_right haf]
        have hz : fibFSym a b c t e f = 0 := fibFSym_zero_of_adm (by simp [haf])
        simp [hz]
    simp_rw [hfterm]
    simp only [Finset.sum_mul]
  have hR :
      (∑ z₁ : (fibFamTensorObj (fibFamTensorObj Y X) Z).idx t,
        (fibFamWhiskerRight (fibFamBraiding X Y).hom Z) t
          ⟨⟨e, c⟩, ⟨he₂⟩, ⟨⟨a, b⟩, ⟨he₁⟩, i, j⟩, k⟩ z₁ *
        ((fibFamAssociator Y X Z).hom ≫ fibFamWhiskerLeft Y (fibFamBraiding X Z).hom) t z₁
          ⟨⟨b', g⟩, ⟨hg₂⟩, j', ⟨⟨c', a'⟩, ⟨hg₁⟩, k', i'⟩⟩) =
      (fibRSym a b e * fibFSym b a c t e g * fibRSym a' c' g) *
        homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k' := by
    have htail : ∀ z₁,
        ((fibFamAssociator Y X Z).hom ≫ fibFamWhiskerLeft Y (fibFamBraiding X Z).hom) t z₁
          ⟨⟨b', g⟩, ⟨hg₂⟩, j', ⟨⟨c', a'⟩, ⟨hg₁⟩, k', i'⟩⟩ =
        fibFSym z₁.2.2.1.1.1 z₁.2.2.1.1.2 z₁.1.2 t z₁.1.1 g *
          fibRSym a' c' g *
          homEntry (𝟙 Y) z₁.2.2.1.1.1 b' z₁.2.2.1.2.2.1 j' *
          homEntry (𝟙 X) z₁.2.2.1.1.2 a' z₁.2.2.1.2.2.2 i' *
          homEntry (𝟙 Z) z₁.1.2 c' z₁.2.2.2 k' :=
      fun z₁ => fibFam_hex_fwd_rhs_tail X Y Z z₁ hg₂ hg₁ j' k' i'
    simp_rw [htail]
    dsimp only [CategoryTheory.MonoidalCategory.whiskerRight, fibFamWhiskerRight, fibFamTensorHom]
    rw [sum_fibFamTensorIdx (A := fibFamTensorObj Y X) (B := Z) (c := t) (G := fun e₁ c₁ yx₁ k₁ =>
      (homEntry (fibFamBraiding X Y).hom e e₁ ⟨⟨a, b⟩, ⟨he₁⟩, i, j⟩ yx₁ *
        homEntry (𝟙 Z) c c₁ k k₁) *
      (fibFSym yx₁.1.1 yx₁.1.2 c₁ t e₁ g *
        fibRSym a' c' g *
        homEntry (𝟙 Y) yx₁.1.1 b' yx₁.2.2.1 j' *
        homEntry (𝟙 X) yx₁.1.2 a' yx₁.2.2.2 i' *
        homEntry (𝟙 Z) c₁ c' k₁ k'))]
    rw [Finset.sum_eq_single e]
    swap
    · intro e₁ _ hne
      refine Finset.sum_eq_zero fun c₁ _ => ?_
      split_ifs <;> simp [homEntry_ne _ hne.symm]
    swap
    · intro hm; exact (hm (Finset.mem_univ e)).elim
    rw [Finset.sum_eq_single c]
    swap
    · intro c₁ _ hne; split_ifs <;> simp [homEntry_ne _ hne.symm]
    swap
    · intro hm; exact (hm (Finset.mem_univ c)).elim
    rw [ite_eq_left he₂]
    simp only [homEntry_braiding_same]
    rw [Finset.sum_comm]
    have hyx : ∀ k₁ : Z.idx c,
        (∑ yx₁ : (fibFamTensorObj Y X).idx e,
          ((fibRSym a b e * homEntry (𝟙 X) a yx₁.1.2 i yx₁.2.2.2 *
              homEntry (𝟙 Y) b yx₁.1.1 j yx₁.2.2.1) *
            homEntry (𝟙 Z) c c k k₁) *
          (fibFSym yx₁.1.1 yx₁.1.2 c t e g *
            fibRSym a' c' g *
            homEntry (𝟙 Y) yx₁.1.1 b' yx₁.2.2.1 j' *
            homEntry (𝟙 X) yx₁.1.2 a' yx₁.2.2.2 i' *
            homEntry (𝟙 Z) c c' k₁ k')) =
        (homEntry (𝟙 Z) c c k k₁ * homEntry (𝟙 Z) c c' k₁ k') *
          ((fibRSym a b e * fibFSym b a c t e g * fibRSym a' c' g) *
            homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j') := by
      intro k₁
      rw [sum_fibFamTensorIdx (A := Y) (B := X) (c := e) (G := fun b₁ a₁ j₁ i₁ =>
        ((fibRSym a b e * homEntry (𝟙 X) a a₁ i i₁ * homEntry (𝟙 Y) b b₁ j j₁) *
          homEntry (𝟙 Z) c c k k₁) *
        (fibFSym b₁ a₁ c t e g * fibRSym a' c' g *
          homEntry (𝟙 Y) b₁ b' j₁ j' * homEntry (𝟙 X) a₁ a' i₁ i' *
          homEntry (𝟙 Z) c c' k₁ k'))]
      rw [Finset.sum_eq_single b]
      swap
      · intro b₁ _ hne
        refine Finset.sum_eq_zero fun a₁ _ => ?_
        split_ifs <;> simp [homEntry_ne _ hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ b)).elim
      rw [Finset.sum_eq_single a]
      swap
      · intro a₁ _ hne; split_ifs <;> simp [homEntry_ne _ hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ a)).elim
      have hba : FibAdmB b a e = true := by simpa [fibAdmB_comm] using he₁
      rw [ite_eq_left hba]
      calc
        (∑ j₁ : Y.idx b, ∑ i₁ : X.idx a,
            ((fibRSym a b e * homEntry (𝟙 X) a a i i₁ * homEntry (𝟙 Y) b b j j₁) *
              homEntry (𝟙 Z) c c k k₁) *
            (fibFSym b a c t e g * fibRSym a' c' g *
              homEntry (𝟙 Y) b b' j₁ j' * homEntry (𝟙 X) a a' i₁ i' *
              homEntry (𝟙 Z) c c' k₁ k'))
        = (∑ j₁ : Y.idx b, homEntry (𝟙 Y) b b j j₁ * homEntry (𝟙 Y) b b' j₁ j') *
            (∑ i₁ : X.idx a, homEntry (𝟙 X) a a i i₁ * homEntry (𝟙 X) a a' i₁ i') *
            ((homEntry (𝟙 Z) c c k k₁ * homEntry (𝟙 Z) c c' k₁ k') *
              (fibRSym a b e * fibFSym b a c t e g * fibRSym a' c' g)) := by
          rw [Finset.sum_mul]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j₁ _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i₁ _ => ?_
          ring
        _ = _ := by
          rw [sum_homEntry_id_left, sum_homEntry_id_left, ite_eq_left rfl, ite_eq_left rfl]
          ring
    simp_rw [hyx]
    rw [← Finset.sum_mul, sum_homEntry_id_left, ite_eq_left rfl]
    ring
  have hMN :
      ((∑ f : FibObject, fibFSym a b c t e f * fibRSym a f t * fibFSym b c a t f g) *
        homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k') =
      (fibRSym a b e * fibFSym b a c t e g * fibRSym a' c' g) *
        homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k' := by
    by_cases ha : a = a' <;> by_cases hb : b = b' <;> by_cases hc : c = c'
    · subst ha hb hc
      rw [fibFSym_hexagon_forward]
    all_goals simp [homEntry_ne, ha, hb, hc]
  simpa only [homEntry_same] using hL.trans (hMN.trans hR.symm)

private theorem fibFam_hex_rev_lhs_tail (X Y Z : FibFam) {t : FibObject}
    (z₁ : (fibFamTensorObj (fibFamTensorObj X Y) Z).idx t)
    {h b' c' a' : FibObject} (hh₂ : FibAdmB h b' t = true) (hh₁ : FibAdmB c' a' h = true)
    (k' : Z.idx c') (i' : X.idx a') (j' : Y.idx b') :
    ((fibFamBraiding (fibFamTensorObj X Y) Z).hom ≫ (α_ Z X Y).inv) t z₁
        ⟨⟨h, b'⟩, ⟨hh₂⟩, ⟨⟨c', a'⟩, ⟨hh₁⟩, k', i'⟩, j'⟩ =
      fibRSym z₁.1.1 z₁.1.2 t *
        fibFSym z₁.1.2 z₁.2.2.1.1.1 z₁.2.2.1.1.2 t h z₁.1.1 *
        homEntry (𝟙 X) z₁.2.2.1.1.1 a' z₁.2.2.1.2.2.1 i' *
        homEntry (𝟙 Y) z₁.2.2.1.1.2 b' z₁.2.2.1.2.2.2 j' *
        homEntry (𝟙 Z) z₁.1.2 c' z₁.2.2.2 k' := by
  rcases z₁ with ⟨⟨e, c₁⟩, ⟨he⟩, ⟨⟨a₁, b₁⟩, ⟨hab₁⟩, i₁, j₁⟩, k₁⟩
  simp only [FibFam.comp_apply]
  change (∑ z₂ : (fibFamTensorObj Z (fibFamTensorObj X Y)).idx t,
      (fibRSym e c₁ t *
        homEntry (𝟙 (fibFamTensorObj X Y)) e z₂.1.2 ⟨⟨a₁, b₁⟩, ⟨hab₁⟩, i₁, j₁⟩ z₂.2.2.2 *
        homEntry (𝟙 Z) c₁ z₂.1.1 k₁ z₂.2.2.1) *
      (fibFSym c' a' b' t h z₂.1.2 *
        homEntry (𝟙 Z) z₂.1.1 c' z₂.2.2.1 k' *
        homEntry (𝟙 X) z₂.2.2.2.1.1 a' z₂.2.2.2.2.2.1 i' *
        homEntry (𝟙 Y) z₂.2.2.2.1.2 b' z₂.2.2.2.2.2.2 j')) = _
  rw [sum_fibFamTensorIdx (A := Z) (B := fibFamTensorObj X Y) (c := t) (G := fun c₂ e₂ k₂ xy₂ =>
    (fibRSym e c₁ t *
      homEntry (𝟙 (fibFamTensorObj X Y)) e e₂ ⟨⟨a₁, b₁⟩, ⟨hab₁⟩, i₁, j₁⟩ xy₂ *
      homEntry (𝟙 Z) c₁ c₂ k₁ k₂) *
    (fibFSym c' a' b' t h e₂ *
      homEntry (𝟙 Z) c₂ c' k₂ k' *
      homEntry (𝟙 X) xy₂.1.1 a' xy₂.2.2.1 i' *
      homEntry (𝟙 Y) xy₂.1.2 b' xy₂.2.2.2 j'))]
  rw [Finset.sum_eq_single c₁]
  swap
  · intro c₂ _ hne
    refine Finset.sum_eq_zero fun e₂ _ => ?_
    split_ifs <;> try rfl
    refine Finset.sum_eq_zero fun k₂ _ => Finset.sum_eq_zero fun xy₂ _ => ?_
    simp [homEntry_ne _ hne.symm]
  swap
  · intro hm; exact (hm (Finset.mem_univ c₁)).elim
  rw [Finset.sum_eq_single e]
  swap
  · intro e₂ _ hne
    split_ifs <;> try rfl
    refine Finset.sum_eq_zero fun k₂ _ => Finset.sum_eq_zero fun xy₂ _ => ?_
    simp [homEntry_ne _ hne.symm]
  swap
  · intro hm; exact (hm (Finset.mem_univ e)).elim
  have hce : FibAdmB c₁ e t = true := by simpa [fibAdmB_comm] using he
  rw [ite_eq_left hce]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single ⟨⟨a₁, b₁⟩, ⟨hab₁⟩, i₁, j₁⟩]
  swap
  · intro xy₂ _ hne
    refine Finset.sum_eq_zero fun k₂ _ => ?_
    simp [homEntry_same, FibFam.id_apply, hne.symm]
  swap
  · intro hm; exact (hm (Finset.mem_univ _)).elim
  have hid : homEntry (𝟙 (fibFamTensorObj X Y)) e e ⟨⟨a₁, b₁⟩, ⟨hab₁⟩, i₁, j₁⟩ ⟨⟨a₁, b₁⟩, ⟨hab₁⟩, i₁, j₁⟩ = 1 := by
    simp [homEntry_same, FibFam.id_apply]
  simp_rw [hid]
  simp only [mul_one]
  calc
    (∑ k₂ : Z.idx c₁,
        (fibRSym e c₁ t * homEntry (𝟙 Z) c₁ c₁ k₁ k₂) *
        (fibFSym c' a' b' t h e * homEntry (𝟙 Z) c₁ c' k₂ k' *
          homEntry (𝟙 X) a₁ a' i₁ i' * homEntry (𝟙 Y) b₁ b' j₁ j'))
    = (∑ k₂ : Z.idx c₁, homEntry (𝟙 Z) c₁ c₁ k₁ k₂ * homEntry (𝟙 Z) c₁ c' k₂ k') *
        (fibRSym e c₁ t * fibFSym c' a' b' t h e *
          homEntry (𝟙 X) a₁ a' i₁ i' * homEntry (𝟙 Y) b₁ b' j₁ j') := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k₂ _ => ?_
      ring
    _ = homEntry (𝟙 Z) c₁ c' k₁ k' *
        (fibRSym e c₁ t * fibFSym c' a' b' t h e *
          homEntry (𝟙 X) a₁ a' i₁ i' * homEntry (𝟙 Y) b₁ b' j₁ j') := by
      rw [sum_homEntry_id_left, ite_eq_left rfl]
    _ = _ := by
      by_cases ha : a₁ = a' <;> by_cases hb : b₁ = b' <;> by_cases hc : c₁ = c'
      · subst ha hb hc; ring
      all_goals simp [homEntry_ne, ha, hb, hc]

private theorem fibFam_hex_rev_rhs_tail (X Y Z : FibFam) {t : FibObject}
    (z₁ : (fibFamTensorObj X (fibFamTensorObj Z Y)).idx t)
    {h b' c' a' : FibObject} (hh₂ : FibAdmB h b' t = true) (hh₁ : FibAdmB c' a' h = true)
    (k' : Z.idx c') (i' : X.idx a') (j' : Y.idx b') :
    ((α_ X Z Y).inv ≫ ((fibFamBraiding X Z).hom ▷ Y)) t z₁
        ⟨⟨h, b'⟩, ⟨hh₂⟩, ⟨⟨c', a'⟩, ⟨hh₁⟩, k', i'⟩, j'⟩ =
      fibFSym a' c' b' t h z₁.1.2 *
        fibRSym a' c' h *
        homEntry (𝟙 X) z₁.1.1 a' z₁.2.2.1 i' *
        homEntry (𝟙 Z) z₁.2.2.2.1.1 c' z₁.2.2.2.2.2.1 k' *
        homEntry (𝟙 Y) z₁.2.2.2.1.2 b' z₁.2.2.2.2.2.2 j' := by
  rcases z₁ with ⟨⟨a₁, f⟩, ⟨hf₂⟩, i₁, ⟨⟨c₁, b₁⟩, ⟨hf₁⟩, k₁, j₁⟩⟩
  simp only [FibFam.comp_apply]
  change (∑ z₂ : (fibFamTensorObj (fibFamTensorObj X Z) Y).idx t,
      (fibFSym z₂.2.2.1.1.1 z₂.2.2.1.1.2 z₂.1.2 t z₂.1.1 f *
        homEntry (𝟙 X) a₁ z₂.2.2.1.1.1 i₁ z₂.2.2.1.2.2.1 *
        homEntry (𝟙 Z) c₁ z₂.2.2.1.1.2 k₁ z₂.2.2.1.2.2.2 *
        homEntry (𝟙 Y) b₁ z₂.1.2 j₁ z₂.2.2.2) *
      (homEntry (fibFamBraiding X Z).hom z₂.1.1 h z₂.2.2.1 ⟨⟨c', a'⟩, ⟨hh₁⟩, k', i'⟩ *
        homEntry (𝟙 Y) z₂.1.2 b' z₂.2.2.2 j')) = _
  rw [sum_fibFamTensorIdx (A := fibFamTensorObj X Z) (B := Y) (c := t) (G := fun h₂ b₂ xz₂ j₂ =>
    (fibFSym xz₂.1.1 xz₂.1.2 b₂ t h₂ f *
      homEntry (𝟙 X) a₁ xz₂.1.1 i₁ xz₂.2.2.1 *
      homEntry (𝟙 Z) c₁ xz₂.1.2 k₁ xz₂.2.2.2 *
      homEntry (𝟙 Y) b₁ b₂ j₁ j₂) *
    (homEntry (fibFamBraiding X Z).hom h₂ h xz₂ ⟨⟨c', a'⟩, ⟨hh₁⟩, k', i'⟩ *
      homEntry (𝟙 Y) b₂ b' j₂ j'))]
  rw [Finset.sum_eq_single h]
  swap
  · intro h₂ _ hne
    refine Finset.sum_eq_zero fun b₂ _ => ?_
    split_ifs <;> simp [homEntry_ne _ hne]
  swap
  · intro hm; exact (hm (Finset.mem_univ h)).elim
  rw [Finset.sum_eq_single b']
  swap
  · intro b₂ _ hne; split_ifs <;> simp [homEntry_ne _ hne]
  swap
  · intro hm; exact (hm (Finset.mem_univ b')).elim
  rw [ite_eq_left hh₂]
  rw [Finset.sum_comm]
  have hinner : ∀ j₂ : Y.idx b',
      (∑ xz₂ : (fibFamTensorObj X Z).idx h,
        (fibFSym xz₂.1.1 xz₂.1.2 b' t h f *
          homEntry (𝟙 X) a₁ xz₂.1.1 i₁ xz₂.2.2.1 *
          homEntry (𝟙 Z) c₁ xz₂.1.2 k₁ xz₂.2.2.2 *
          homEntry (𝟙 Y) b₁ b' j₁ j₂) *
        (homEntry (fibFamBraiding X Z).hom h h xz₂ ⟨⟨c', a'⟩, ⟨hh₁⟩, k', i'⟩ *
          homEntry (𝟙 Y) b' b' j₂ j')) =
      (homEntry (𝟙 Y) b₁ b' j₁ j₂ * homEntry (𝟙 Y) b' b' j₂ j') *
        (fibFSym a' c' b' t h f * fibRSym a' c' h *
          homEntry (𝟙 X) a₁ a' i₁ i' * homEntry (𝟙 Z) c₁ c' k₁ k') := by
    intro j₂
    simp only [homEntry_braiding_same]
    rw [sum_fibFamTensorIdx (A := X) (B := Z) (c := h) (G := fun a₂ c₂ i₂ k₂ =>
      (fibFSym a₂ c₂ b' t h f *
        homEntry (𝟙 X) a₁ a₂ i₁ i₂ *
        homEntry (𝟙 Z) c₁ c₂ k₁ k₂ *
        homEntry (𝟙 Y) b₁ b' j₁ j₂) *
      ((fibRSym a₂ c₂ h * homEntry (𝟙 X) a₂ a' i₂ i' * homEntry (𝟙 Z) c₂ c' k₂ k') *
        homEntry (𝟙 Y) b' b' j₂ j'))]
    rw [Finset.sum_eq_single a']
    swap
    · intro a₂ _ hne
      refine Finset.sum_eq_zero fun c₂ _ => ?_
      split_ifs <;> simp [homEntry_ne _ hne]
    swap
    · intro hm; exact (hm (Finset.mem_univ a')).elim
    rw [Finset.sum_eq_single c']
    swap
    · intro c₂ _ hne; split_ifs <;> simp [homEntry_ne _ hne]
    swap
    · intro hm; exact (hm (Finset.mem_univ c')).elim
    have hac : FibAdmB a' c' h = true := by simpa [fibAdmB_comm] using hh₁
    rw [ite_eq_left hac]
    calc
      (∑ i₂ : X.idx a', ∑ k₂ : Z.idx c',
          (fibFSym a' c' b' t h f * homEntry (𝟙 X) a₁ a' i₁ i₂ *
            homEntry (𝟙 Z) c₁ c' k₁ k₂ * homEntry (𝟙 Y) b₁ b' j₁ j₂) *
          ((fibRSym a' c' h * homEntry (𝟙 X) a' a' i₂ i' * homEntry (𝟙 Z) c' c' k₂ k') *
            homEntry (𝟙 Y) b' b' j₂ j'))
      = (∑ i₂ : X.idx a', homEntry (𝟙 X) a₁ a' i₁ i₂ * homEntry (𝟙 X) a' a' i₂ i') *
          (∑ k₂ : Z.idx c', homEntry (𝟙 Z) c₁ c' k₁ k₂ * homEntry (𝟙 Z) c' c' k₂ k') *
          ((homEntry (𝟙 Y) b₁ b' j₁ j₂ * homEntry (𝟙 Y) b' b' j₂ j') *
            (fibFSym a' c' b' t h f * fibRSym a' c' h)) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i₂ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k₂ _ => ?_
        ring
      _ = _ := by
        rw [sum_homEntry_id_right, sum_homEntry_id_right]
        by_cases ha : a₁ = a' <;> by_cases hc : c₁ = c'
        · subst ha hc; simp only [ite_true]; ring
        all_goals simp [ha, hc, homEntry_ne]
  simp_rw [hinner]
  rw [← Finset.sum_mul, sum_homEntry_id_right]
  by_cases hb : b₁ = b'
  · simp [hb]; ring
  · simp [hb, homEntry_ne _ hb]

private theorem fibFam_hexagon_reverse (X Y Z : FibFam) :
    (α_ X Y Z).inv ≫ (fibFamBraiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (fibFamBraiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((fibFamBraiding X Z).hom ▷ Y) := by
  dsimp only [CategoryTheory.MonoidalCategory.tensorObj,
    CategoryTheory.MonoidalCategory.associator,
    CategoryTheory.MonoidalCategory.whiskerRight,
    CategoryTheory.MonoidalCategory.whiskerLeft]
  ext t ⟨⟨a, f⟩, ⟨hf₂⟩, i, ⟨⟨b, c⟩, ⟨hf₁⟩, j, k⟩⟩
    ⟨⟨h, b'⟩, ⟨hh₂⟩, ⟨⟨c', a'⟩, ⟨hh₁⟩, k', i'⟩, j'⟩
  rw [FibFam.comp_apply, FibFam.comp_apply]
  have hL :
      (∑ z₁ : (fibFamTensorObj (fibFamTensorObj X Y) Z).idx t,
        (fibFamAssociator X Y Z).inv t
          ⟨⟨a, f⟩, ⟨hf₂⟩, i, ⟨⟨b, c⟩, ⟨hf₁⟩, j, k⟩⟩ z₁ *
        ((fibFamBraiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv) t z₁
          ⟨⟨h, b'⟩, ⟨hh₂⟩, ⟨⟨c', a'⟩, ⟨hh₁⟩, k', i'⟩, j'⟩) =
      (∑ e : FibObject, fibFSym a b c t e f * fibRSym e c t * fibFSym c a b t h e) *
        homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k' := by
    have htail : ∀ z₁,
        ((fibFamBraiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv) t z₁
          ⟨⟨h, b'⟩, ⟨hh₂⟩, ⟨⟨c', a'⟩, ⟨hh₁⟩, k', i'⟩, j'⟩ =
        fibRSym z₁.1.1 z₁.1.2 t *
          fibFSym z₁.1.2 z₁.2.2.1.1.1 z₁.2.2.1.1.2 t h z₁.1.1 *
          homEntry (𝟙 X) z₁.2.2.1.1.1 a' z₁.2.2.1.2.2.1 i' *
          homEntry (𝟙 Y) z₁.2.2.1.1.2 b' z₁.2.2.1.2.2.2 j' *
          homEntry (𝟙 Z) z₁.1.2 c' z₁.2.2.2 k' :=
      fun z₁ => fibFam_hex_rev_lhs_tail X Y Z z₁ hh₂ hh₁ k' i' j'
    simp_rw [htail]
    dsimp only [fibFamAssociator]
    rw [sum_fibFamTensorIdx (A := fibFamTensorObj X Y) (B := Z) (c := t) (G := fun e c₁ xy₁ k₁ =>
      (fibFSym xy₁.1.1 xy₁.1.2 c₁ t e f *
        homEntry (𝟙 X) a xy₁.1.1 i xy₁.2.2.1 *
        homEntry (𝟙 Y) b xy₁.1.2 j xy₁.2.2.2 *
        homEntry (𝟙 Z) c c₁ k k₁) *
      (fibRSym e c₁ t *
        fibFSym c₁ xy₁.1.1 xy₁.1.2 t h e *
        homEntry (𝟙 X) xy₁.1.1 a' xy₁.2.2.1 i' *
        homEntry (𝟙 Y) xy₁.1.2 b' xy₁.2.2.2 j' *
        homEntry (𝟙 Z) c₁ c' k₁ k'))]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single c]
    swap
    · intro c₁ _ hne
      refine Finset.sum_eq_zero fun e _ => ?_
      split_ifs <;> try rfl
      refine Finset.sum_eq_zero fun xy₁ _ => Finset.sum_eq_zero fun k₁ _ => ?_
      simp [homEntry_ne _ hne.symm]
    swap
    · intro hm; exact (hm (Finset.mem_univ c)).elim
    have heterm : ∀ e : FibObject,
        (if FibAdmB e c t = true then
          ∑ xy₁ : (fibFamTensorObj X Y).idx e, ∑ k₁ : Z.idx c,
            (fibFSym xy₁.1.1 xy₁.1.2 c t e f *
              homEntry (𝟙 X) a xy₁.1.1 i xy₁.2.2.1 *
              homEntry (𝟙 Y) b xy₁.1.2 j xy₁.2.2.2 *
              homEntry (𝟙 Z) c c k k₁) *
            (fibRSym e c t *
              fibFSym c xy₁.1.1 xy₁.1.2 t h e *
              homEntry (𝟙 X) xy₁.1.1 a' xy₁.2.2.1 i' *
              homEntry (𝟙 Y) xy₁.1.2 b' xy₁.2.2.2 j' *
              homEntry (𝟙 Z) c c' k₁ k')
        else 0) =
        (fibFSym a b c t e f * fibRSym e c t * fibFSym c a b t h e) *
          homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k' := by
      intro e
      by_cases hec : FibAdmB e c t = true
      · rw [ite_eq_left hec]
        rw [Finset.sum_comm]
        have hxy : ∀ k₁ : Z.idx c,
            (∑ xy₁ : (fibFamTensorObj X Y).idx e,
              (fibFSym xy₁.1.1 xy₁.1.2 c t e f *
                homEntry (𝟙 X) a xy₁.1.1 i xy₁.2.2.1 *
                homEntry (𝟙 Y) b xy₁.1.2 j xy₁.2.2.2 *
                homEntry (𝟙 Z) c c k k₁) *
              (fibRSym e c t *
                fibFSym c xy₁.1.1 xy₁.1.2 t h e *
                homEntry (𝟙 X) xy₁.1.1 a' xy₁.2.2.1 i' *
                homEntry (𝟙 Y) xy₁.1.2 b' xy₁.2.2.2 j' *
                homEntry (𝟙 Z) c c' k₁ k')) =
            (homEntry (𝟙 Z) c c k k₁ * homEntry (𝟙 Z) c c' k₁ k') *
              (fibFSym a b c t e f * fibRSym e c t * fibFSym c a b t h e *
                homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j') := by
          intro k₁
          rw [sum_fibFamTensorIdx (A := X) (B := Y) (c := e) (G := fun a₁ b₁ i₁ j₁ =>
            (fibFSym a₁ b₁ c t e f *
              homEntry (𝟙 X) a a₁ i i₁ *
              homEntry (𝟙 Y) b b₁ j j₁ *
              homEntry (𝟙 Z) c c k k₁) *
            (fibRSym e c t *
              fibFSym c a₁ b₁ t h e *
              homEntry (𝟙 X) a₁ a' i₁ i' *
              homEntry (𝟙 Y) b₁ b' j₁ j' *
              homEntry (𝟙 Z) c c' k₁ k'))]
          rw [Finset.sum_eq_single a]
          swap
          · intro a₁ _ hne
            refine Finset.sum_eq_zero fun b₁ _ => ?_
            split_ifs <;> try rfl
            refine Finset.sum_eq_zero fun i₁ _ => Finset.sum_eq_zero fun j₁ _ => ?_
            simp [homEntry_ne _ hne.symm]
          swap
          · intro hm; exact (hm (Finset.mem_univ a)).elim
          rw [Finset.sum_eq_single b]
          swap
          · intro b₁ _ hne
            split_ifs <;> try rfl
            refine Finset.sum_eq_zero fun i₁ _ => Finset.sum_eq_zero fun j₁ _ => ?_
            simp [homEntry_ne _ hne.symm]
          swap
          · intro hm; exact (hm (Finset.mem_univ b)).elim
          by_cases hab : FibAdmB a b e = true
          · rw [ite_eq_left hab]
            calc
              (∑ i₁ : X.idx a, ∑ j₁ : Y.idx b,
                  (fibFSym a b c t e f * homEntry (𝟙 X) a a i i₁ *
                    homEntry (𝟙 Y) b b j j₁ * homEntry (𝟙 Z) c c k k₁) *
                  (fibRSym e c t * fibFSym c a b t h e *
                    homEntry (𝟙 X) a a' i₁ i' * homEntry (𝟙 Y) b b' j₁ j' *
                    homEntry (𝟙 Z) c c' k₁ k'))
              = (∑ i₁ : X.idx a, homEntry (𝟙 X) a a i i₁ * homEntry (𝟙 X) a a' i₁ i') *
                  (∑ j₁ : Y.idx b, homEntry (𝟙 Y) b b j j₁ * homEntry (𝟙 Y) b b' j₁ j') *
                  ((homEntry (𝟙 Z) c c k k₁ * homEntry (𝟙 Z) c c' k₁ k') *
                    (fibFSym a b c t e f * fibRSym e c t * fibFSym c a b t h e)) := by
                rw [Finset.sum_mul, Finset.sum_mul]
                refine Finset.sum_congr rfl fun i₁ _ => ?_
                rw [Finset.mul_sum, Finset.sum_mul]
                refine Finset.sum_congr rfl fun j₁ _ => ?_
                ring
              _ = _ := by
                rw [sum_homEntry_id_left, sum_homEntry_id_left, ite_eq_left rfl, ite_eq_left rfl]
                ring
          · rw [ite_eq_right hab]
            have hz : fibFSym a b c t e f = 0 := fibFSym_zero_of_adm (by simp [hab])
            simp [hz]
        simp_rw [hxy]
        rw [← Finset.sum_mul, sum_homEntry_id_left, ite_eq_left rfl]
        ring
      · rw [ite_eq_right hec]
        have hz : fibFSym a b c t e f = 0 := fibFSym_zero_of_adm (by simp [hec])
        simp [hz]
    simp_rw [heterm]
    simp only [Finset.sum_mul]
  have hR :
      (∑ z₁ : (fibFamTensorObj X (fibFamTensorObj Z Y)).idx t,
        (fibFamWhiskerLeft X (fibFamBraiding Y Z).hom) t
          ⟨⟨a, f⟩, ⟨hf₂⟩, i, ⟨⟨b, c⟩, ⟨hf₁⟩, j, k⟩⟩ z₁ *
        ((α_ X Z Y).inv ≫ ((fibFamBraiding X Z).hom ▷ Y)) t z₁
          ⟨⟨h, b'⟩, ⟨hh₂⟩, ⟨⟨c', a'⟩, ⟨hh₁⟩, k', i'⟩, j'⟩) =
      (fibRSym b c f * fibFSym a' c' b' t h f * fibRSym a' c' h) *
        homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k' := by
    have htail : ∀ z₁,
        ((α_ X Z Y).inv ≫ ((fibFamBraiding X Z).hom ▷ Y)) t z₁
          ⟨⟨h, b'⟩, ⟨hh₂⟩, ⟨⟨c', a'⟩, ⟨hh₁⟩, k', i'⟩, j'⟩ =
        fibFSym a' c' b' t h z₁.1.2 *
          fibRSym a' c' h *
          homEntry (𝟙 X) z₁.1.1 a' z₁.2.2.1 i' *
          homEntry (𝟙 Z) z₁.2.2.2.1.1 c' z₁.2.2.2.2.2.1 k' *
          homEntry (𝟙 Y) z₁.2.2.2.1.2 b' z₁.2.2.2.2.2.2 j' :=
      fun z₁ => fibFam_hex_rev_rhs_tail X Y Z z₁ hh₂ hh₁ k' i' j'
    simp_rw [htail]
    dsimp only [fibFamWhiskerLeft, fibFamTensorHom]
    rw [sum_fibFamTensorIdx (A := X) (B := fibFamTensorObj Z Y) (c := t) (G := fun a₁ f₁ i₁ zy₁ =>
      (homEntry (𝟙 X) a a₁ i i₁ *
        homEntry (fibFamBraiding Y Z).hom f f₁ ⟨⟨b, c⟩, ⟨hf₁⟩, j, k⟩ zy₁) *
      (fibFSym a' c' b' t h f₁ *
        fibRSym a' c' h *
        homEntry (𝟙 X) a₁ a' i₁ i' *
        homEntry (𝟙 Z) zy₁.1.1 c' zy₁.2.2.1 k' *
        homEntry (𝟙 Y) zy₁.1.2 b' zy₁.2.2.2 j'))]
    rw [Finset.sum_eq_single a]
    swap
    · intro a₁ _ hne
      refine Finset.sum_eq_zero fun f₁ _ => ?_
      split_ifs <;> try rfl
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x_1 _ => ?_
      simp [homEntry_ne _ hne.symm]
    swap
    · intro hm; exact (hm (Finset.mem_univ a)).elim
    rw [Finset.sum_eq_single f]
    swap
    · intro f₁ _ hne
      split_ifs <;> try rfl
      refine Finset.sum_eq_zero fun x _ => ?_
      simp [homEntry_ne _ hne.symm]
    swap
    · intro hm; exact (hm (Finset.mem_univ f)).elim
    rw [ite_eq_left hf₂]
    simp only [homEntry_braiding_same]
    have hinner : ∀ i₁ : X.idx a,
        (∑ zy₁ : (fibFamTensorObj Z Y).idx f,
          (homEntry (𝟙 X) a a i i₁ *
            (fibRSym b c f * homEntry (𝟙 Y) b zy₁.1.2 j zy₁.2.2.2 *
              homEntry (𝟙 Z) c zy₁.1.1 k zy₁.2.2.1)) *
          (fibFSym a' c' b' t h f *
            fibRSym a' c' h *
            homEntry (𝟙 X) a a' i₁ i' *
            homEntry (𝟙 Z) zy₁.1.1 c' zy₁.2.2.1 k' *
            homEntry (𝟙 Y) zy₁.1.2 b' zy₁.2.2.2 j')) =
        (homEntry (𝟙 X) a a i i₁ * homEntry (𝟙 X) a a' i₁ i') *
          (fibRSym b c f * fibFSym a' c' b' t h f * fibRSym a' c' h *
            homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k') := by
      intro i₁
      rw [sum_fibFamTensorIdx (A := Z) (B := Y) (c := f) (G := fun c₁ b₁ k₁ j₁ =>
        (homEntry (𝟙 X) a a i i₁ *
          (fibRSym b c f * homEntry (𝟙 Y) b b₁ j j₁ * homEntry (𝟙 Z) c c₁ k k₁)) *
        (fibFSym a' c' b' t h f *
          fibRSym a' c' h *
          homEntry (𝟙 X) a a' i₁ i' *
          homEntry (𝟙 Z) c₁ c' k₁ k' *
          homEntry (𝟙 Y) b₁ b' j₁ j'))]
      rw [Finset.sum_eq_single c]
      swap
      · intro c₁ _ hne
        refine Finset.sum_eq_zero fun b₁ _ => ?_
        split_ifs <;> try rfl
        refine Finset.sum_eq_zero fun k₁ _ => Finset.sum_eq_zero fun j₁ _ => ?_
        simp [homEntry_ne _ hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ c)).elim
      rw [Finset.sum_eq_single b]
      swap
      · intro b₁ _ hne
        split_ifs <;> try rfl
        refine Finset.sum_eq_zero fun k₁ _ => Finset.sum_eq_zero fun j₁ _ => ?_
        simp [homEntry_ne _ hne.symm]
      swap
      · intro hm; exact (hm (Finset.mem_univ b)).elim
      have hcb : FibAdmB c b f = true := by simpa [fibAdmB_comm] using hf₁
      rw [ite_eq_left hcb]
      calc
        (∑ k₁ : Z.idx c, ∑ j₁ : Y.idx b,
            (homEntry (𝟙 X) a a i i₁ *
              (fibRSym b c f * homEntry (𝟙 Y) b b j j₁ * homEntry (𝟙 Z) c c k k₁)) *
            (fibFSym a' c' b' t h f * fibRSym a' c' h *
              homEntry (𝟙 X) a a' i₁ i' * homEntry (𝟙 Z) c c' k₁ k' *
              homEntry (𝟙 Y) b b' j₁ j'))
        = (∑ k₁ : Z.idx c, homEntry (𝟙 Z) c c k k₁ * homEntry (𝟙 Z) c c' k₁ k') *
            (∑ j₁ : Y.idx b, homEntry (𝟙 Y) b b j j₁ * homEntry (𝟙 Y) b b' j₁ j') *
            ((homEntry (𝟙 X) a a i i₁ * homEntry (𝟙 X) a a' i₁ i') *
              (fibRSym b c f * fibFSym a' c' b' t h f * fibRSym a' c' h)) := by
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k₁ _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j₁ _ => ?_
          ring
        _ = _ := by
          rw [sum_homEntry_id_left, sum_homEntry_id_left, ite_eq_left rfl, ite_eq_left rfl]
          ring
    simp_rw [hinner]
    rw [← Finset.sum_mul, sum_homEntry_id_left, ite_eq_left rfl]
    ring
  have hMN :
      ((∑ e : FibObject, fibFSym a b c t e f * fibRSym e c t * fibFSym c a b t h e) *
        homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k') =
      (fibRSym b c f * fibFSym a' c' b' t h f * fibRSym a' c' h) *
        homEntry (𝟙 X) a a' i i' * homEntry (𝟙 Y) b b' j j' * homEntry (𝟙 Z) c c' k k' := by
    by_cases ha : a = a' <;> by_cases hb : b = b' <;> by_cases hc : c = c'
    · subst ha hb hc
      rw [fibFSym_hexagon_reverse]
    all_goals simp [homEntry_ne, ha, hb, hc]
  exact hL.trans (hMN.trans hR.symm)

instance : BraidedCategory FibFam where
  braiding := fibFamBraiding
  braiding_naturality_right := fibFam_braiding_naturality_right
  braiding_naturality_left := fibFam_braiding_naturality_left
  hexagon_forward := fibFam_hexagon_forward
  hexagon_reverse := fibFam_hexagon_reverse

/-- The double braiding coefficient in the unit channel of two `tau` labels
is not one.  This is a scalar channel calculation; a categorical nonsymmetry
witness additionally requires identifying the corresponding tensor index. -/
theorem fibRSym_tau_unit_square_ne_one :
    fibRSym .tau .tau .unit * fibRSym .tau .tau .unit ≠ 1 := by
  intro h
  have hq2 : YangBaxterProof.q ^ 2 = 1 := by
    simpa [fibRSym, FibAdmB, pow_two] using h
  have hq3 : YangBaxterProof.q ^ 3 = YangBaxterProof.q := by
    calc
      YangBaxterProof.q ^ 3 = YangBaxterProof.q ^ 2 * YangBaxterProof.q := by ring
      _ = YangBaxterProof.q := by rw [hq2, one_mul]
  have hq4 : YangBaxterProof.q ^ 4 = 1 := by
    calc
      YangBaxterProof.q ^ 4 = (YangBaxterProof.q ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hq2]; norm_num
  have hcyclo := YangBaxterProof.cyclotomic_relation
  rw [hq4, hq3, hq2] at hcyclo
  have hq : YangBaxterProof.q = (3 / 2 : ℂ) := by linear_combination -(1 / 2 : ℂ) * hcyclo
  rw [hq] at hq2
  norm_num at hq2

/-- The multiplicity family consisting of one `tau` label. -/
def fibTau : FibFam where
  idx
    | .unit => PEmpty
    | .tau => PUnit
  fintypeIdx
    | .unit => inferInstanceAs (Fintype PEmpty)
    | .tau => inferInstanceAs (Fintype PUnit)
  decEqIdx
    | .unit => inferInstanceAs (DecidableEq PEmpty)
    | .tau => inferInstanceAs (DecidableEq PUnit)

/-- The braiding of the `tau` family is not involutive on its unit fusion channel. -/
theorem fibTau_double_braiding_ne_id :
    (fibFamBraiding fibTau fibTau).hom ≫ (fibFamBraiding fibTau fibTau).hom ≠
      𝟙 (fibFamTensorObj fibTau fibTau) := by
  let z : (fibFamTensorObj fibTau fibTau).idx .unit :=
    ⟨(.tau, .tau), ⟨⟨rfl⟩, PUnit.unit, PUnit.unit⟩⟩
  let : Unique ((fibFamTensorObj fibTau fibTau).idx .unit) := {
    default := z
    uniq v := by
      rcases v with ⟨⟨a, b⟩, ⟨h⟩, i, j⟩
      cases a with
      | unit => exact i.elim
      | tau =>
        cases b with
        | unit => exact j.elim
        | tau => cases i; cases j; rfl }
  intro h
  have hv := congrFun (congrFun (congrFun h .unit) z) z
  change (∑ v : (fibFamTensorObj fibTau fibTau).idx .unit,
    (fibFamBraiding fibTau fibTau).hom .unit z v *
      (fibFamBraiding fibTau fibTau).hom .unit v z) = (if z = z then 1 else 0) at hv
  rw [Fintype.sum_unique] at hv
  have hzd : z = default := Subsingleton.elim _ _
  rw [hzd] at hv
  have hdef : (default : (fibFamTensorObj fibTau fibTau).idx .unit) = z := Subsingleton.elim _ _
  have hval : (fibFamBraiding fibTau fibTau).hom .unit default default = fibRSym .tau .tau .unit := by
    rw [hdef]
    simp [fibFamBraiding, homEntry, FibFam.id_apply, fibTau, z]
  rw [hval, ite_eq_left rfl] at hv
  exact fibRSym_tau_unit_square_ne_one hv

open CategoryTheory Category MonoidalCategory BraidedCategory

def fibFamOfVec (v : FibObject → ℕ) : FibFam where
  idx s := Fin (v s)
  fintypeIdx _ := inferInstance
  decEqIdx _ := inferInstance

/-- The multiplicity vector of the monoidal unit simple object `1`. -/
@[reducible]
def oneVec : FibObject → ℕ
  | FibObject.unit => 1
  | FibObject.tau => 0

/-- The multiplicity vector of the non-trivial simple object `τ`. -/
@[reducible]
def tauVec : FibObject → ℕ
  | FibObject.unit => 0
  | FibObject.tau => 1

/-- Tensor product of multiplicity vectors according to Fibonacci fusion rules:
1 ⊗ 1 = 1, 1 ⊗ τ = τ, τ ⊗ 1 = τ, τ ⊗ τ = 1 ⊕ τ. -/
@[reducible]
def fibVecTensorObj (X Y : FibObject → ℕ) : FibObject → ℕ
  | FibObject.unit => X FibObject.unit * Y FibObject.unit + X FibObject.tau * Y FibObject.tau
  | FibObject.tau  => X FibObject.unit * Y FibObject.tau + X FibObject.tau * Y FibObject.unit +
                      X FibObject.tau * Y FibObject.tau

@[simp] theorem oneVec_unit : oneVec FibObject.unit = 1 := rfl
@[simp] theorem oneVec_tau : oneVec FibObject.tau = 0 := rfl
@[simp] theorem tauVec_unit : tauVec FibObject.unit = 0 := rfl
@[simp] theorem tauVec_tau : tauVec FibObject.tau = 1 := rfl

@[simp] theorem fibVecTensorObj_tau_tau_unit :
    fibVecTensorObj tauVec tauVec FibObject.unit = 1 := rfl

@[simp] theorem fibVecTensorObj_tau_tau_tau :
    fibVecTensorObj tauVec tauVec FibObject.tau = 1 := rfl

private theorem card_plift_bool (b : Bool) :
    Fintype.card (PLift (b = true)) = if b then 1 else 0 := by
  cases b <;> rfl

theorem card_fibFamTensorObj (X Y : FibObject → ℕ) (c : FibObject) :
    Fintype.card ((fibFamTensorObj (fibFamOfVec X) (fibFamOfVec Y)).idx c) = (fibVecTensorObj X Y) c := by
  cases c
  · change Fintype.card (Σ ab : FibObject × FibObject,
        PLift (FibAdmB ab.1 ab.2 .unit = true) × Fin (X ab.1) × Fin (Y ab.2)) = _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin, card_plift_bool]
    rw [Fintype.sum_prod_type, sum_fibObject]
    simp only [sum_fibObject, FibAdmB, ite_true, Bool.false_eq_true, ite_false, one_mul, zero_mul, add_zero, zero_add]
  · change Fintype.card (Σ ab : FibObject × FibObject,
        PLift (FibAdmB ab.1 ab.2 .tau = true) × Fin (X ab.1) × Fin (Y ab.2)) = _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin, card_plift_bool]
    rw [Fintype.sum_prod_type, sum_fibObject]
    simp only [sum_fibObject, FibAdmB, ite_true, Bool.false_eq_true, ite_false, one_mul, zero_mul, zero_add]
    ring

theorem card_fibFamUnit (c : FibObject) :
    Fintype.card (fibFamUnit.idx c) = oneVec c := by
  cases c <;> rfl

/-- Small category on multiplicity vectors. -/
instance fibVecCategory : Category.{0} (FibObject → ℕ) where
  Hom X Y := fibFamOfVec X ⟶ fibFamOfVec Y
  id X := 𝟙 (fibFamOfVec X)
  comp f g := f ≫ g

/-- Faithful embedding functor from multiplicity vectors to `FibFam`. -/
def fibVecFunctor : (FibObject → ℕ) ⥤ FibFam where
  obj := fibFamOfVec
  map f := f

instance : fibVecFunctor.Faithful where
  map_injective := fun h => h

/-- Isomorphism in `FibFam` induced by a family of index equivalences. -/
def fibFamIsoOfEquiv (A B : FibFam) (e : ∀ s, A.idx s ≃ B.idx s) : A ≅ B where
  hom s i j := if e s i = j then 1 else 0
  inv s j i := if (e s).symm j = i then 1 else 0
  hom_inv_id := by
    ext s i₁ i₂
    change (∑ j : B.idx s, (if e s i₁ = j then (1 : ℂ) else 0) * (if (e s).symm j = i₂ then 1 else 0)) =
      if i₁ = i₂ then 1 else 0
    rw [Finset.sum_eq_single (e s i₁)]
    · simp
    · intro j _ hne; simp [Ne.symm hne]
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  inv_hom_id := by
    ext s j₁ j₂
    change (∑ i : A.idx s, (if (e s).symm j₁ = i then (1 : ℂ) else 0) * (if e s i = j₂ then 1 else 0)) =
      if j₁ = j₂ then 1 else 0
    rw [Finset.sum_eq_single ((e s).symm j₁)]
    · simp
    · intro i _ hne; simp [Ne.symm hne]
    · intro hm; exact (hm (Finset.mem_univ _)).elim

def fibVecIsoOfFibFamIso {A B : FibObject → ℕ} (i : fibFamOfVec A ≅ fibFamOfVec B) : A ≅ B where
  hom := i.hom
  inv := i.inv
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

/-- Tensor isomorphism between `F(X) ⊗ F(Y)` and `F(X ⊗ Y)`. -/
def fibVecTensorIso (X Y : FibObject → ℕ) :
    fibFamTensorObj (fibFamOfVec X) (fibFamOfVec Y) ≅ fibFamOfVec (fibVecTensorObj X Y) :=
  fibFamIsoOfEquiv _ _ (fun c => Fintype.equivFinOfCardEq (card_fibFamTensorObj X Y c))

/-- Unit isomorphism between `fibFamUnit` and `F(oneVec)`. -/
def fibVecUnitIso : 𝟙_ FibFam ≅ fibVecFunctor.obj oneVec :=
  fibFamIsoOfEquiv _ _ (fun c => Fintype.equivFinOfCardEq (card_fibFamUnit c))

/-- Monoidal category structure on multiplicity vectors `FibObject → ℕ`. -/
instance fibVecMonoidalCategoryStruct : MonoidalCategoryStruct (FibObject → ℕ) where
  tensorObj := fibVecTensorObj
  whiskerLeft X _ _ f := ((fibVecTensorIso X _).inv ≫ fibFamWhiskerLeft (fibFamOfVec X) f ≫ (fibVecTensorIso X _).hom : fibFamOfVec (fibVecTensorObj X _) ⟶ fibFamOfVec (fibVecTensorObj X _))
  whiskerRight f Y := ((fibVecTensorIso _ Y).inv ≫ fibFamWhiskerRight f (fibFamOfVec Y) ≫ (fibVecTensorIso _ Y).hom : fibFamOfVec (fibVecTensorObj _ Y) ⟶ fibFamOfVec (fibVecTensorObj _ Y))
  tensorHom {X₁ Y₁ X₂ Y₂} f g := ((fibVecTensorIso X₁ X₂).inv ≫ fibFamTensorHom f g ≫ (fibVecTensorIso Y₁ Y₂).hom : fibFamOfVec (fibVecTensorObj X₁ X₂) ⟶ fibFamOfVec (fibVecTensorObj Y₁ Y₂))
  tensorUnit := oneVec
  associator X Y Z := fibVecIsoOfFibFamIso (
    ((fibVecTensorIso (fibVecTensorObj X Y) Z).symm ≪≫ ((fibVecTensorIso X Y).symm ⊗ᵢ .refl (fibFamOfVec Z)))
      ≪≫ α_ (fibFamOfVec X) (fibFamOfVec Y) (fibFamOfVec Z)
      ≪≫ ((.refl (fibFamOfVec X) ⊗ᵢ fibVecTensorIso Y Z) ≪≫ fibVecTensorIso X (fibVecTensorObj Y Z)))
  leftUnitor X := fibVecIsoOfFibFamIso (
    ((fibVecTensorIso oneVec X).symm ≪≫ (fibVecUnitIso.symm ⊗ᵢ .refl (fibFamOfVec X))) ≪≫ λ_ (fibFamOfVec X))
  rightUnitor X := fibVecIsoOfFibFamIso (
    ((fibVecTensorIso X oneVec).symm ≪≫ (.refl (fibFamOfVec X) ⊗ᵢ fibVecUnitIso.symm)) ≪≫ ρ_ (fibFamOfVec X))

/-- Transport data for inducing monoidal category structure on `FibObject → ℕ`. -/
def fibVecInducingData : CategoryTheory.Monoidal.InducingFunctorData fibVecFunctor where
  μIso := by
    intro X Y
    change fibVecFunctor.obj X ⊗ fibVecFunctor.obj Y ≅ fibVecFunctor.obj (fibVecTensorObj X Y)
    exact fibVecTensorIso X Y
  εIso := by
    change 𝟙_ FibFam ≅ fibVecFunctor.obj oneVec
    exact fibVecUnitIso
  whiskerLeft_eq := by intros; rfl
  whiskerRight_eq := by intros; rfl
  tensorHom_eq := by intros; rfl
  associator_eq := by intros; rfl
  leftUnitor_eq := by intros; rfl
  rightUnitor_eq := by intros; rfl

/-- Transported `MonoidalCategory` instance on `FibObject → ℕ`. -/
instance fibVecMonoidalCategory : MonoidalCategory (FibObject → ℕ) :=
  CategoryTheory.Monoidal.induced fibVecFunctor fibVecInducingData

/-- The embedding functor is monoidal. -/
instance fibVecMonoidalFunctor : fibVecFunctor.Monoidal :=
  CategoryTheory.Monoidal.fromInducedMonoidal fibVecFunctor fibVecInducingData

/-- Candidate braiding isomorphisms on `FibObject → ℕ`. -/
def fibVecBraiding (X Y : FibObject → ℕ) : X ⊗ Y ≅ Y ⊗ X where
  hom := ((fibVecTensorIso X Y).inv ≫ (fibFamBraiding (fibFamOfVec X) (fibFamOfVec Y)).hom ≫ (fibVecTensorIso Y X).hom :
    fibFamOfVec (fibVecTensorObj X Y) ⟶ fibFamOfVec (fibVecTensorObj Y X))
  inv := ((fibVecTensorIso Y X).inv ≫ (fibFamBraiding (fibFamOfVec X) (fibFamOfVec Y)).inv ≫ (fibVecTensorIso X Y).hom :
    fibFamOfVec (fibVecTensorObj Y X) ⟶ fibFamOfVec (fibVecTensorObj X Y))
  hom_inv_id := by
    change ((fibVecTensorIso X Y).inv ≫ (fibFamBraiding (fibFamOfVec X) (fibFamOfVec Y)).hom ≫ (fibVecTensorIso Y X).hom) ≫
      ((fibVecTensorIso Y X).inv ≫ (fibFamBraiding (fibFamOfVec X) (fibFamOfVec Y)).inv ≫ (fibVecTensorIso X Y).hom) = 𝟙 _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  inv_hom_id := by
    change ((fibVecTensorIso Y X).inv ≫ (fibFamBraiding (fibFamOfVec X) (fibFamOfVec Y)).inv ≫ (fibVecTensorIso X Y).hom) ≫
      ((fibVecTensorIso X Y).inv ≫ (fibFamBraiding (fibFamOfVec X) (fibFamOfVec Y)).hom ≫ (fibVecTensorIso Y X).hom) = 𝟙 _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- Transported `BraidedCategory` instance on `FibObject → ℕ`. -/
instance fibVecBraidedCategory : BraidedCategory (FibObject → ℕ) :=
  BraidedCategory.ofFaithful fibVecFunctor fibVecBraiding (fun X Y => by
    change (fibVecTensorIso X Y).hom ≫
      ((fibVecTensorIso X Y).inv ≫ (fibFamBraiding (fibFamOfVec X) (fibFamOfVec Y)).hom ≫ (fibVecTensorIso Y X).hom) =
      (fibFamBraiding (fibFamOfVec X) (fibFamOfVec Y)).hom ≫ (fibVecTensorIso Y X).hom
    rw [Iso.hom_inv_id_assoc])

/-- The parameter `q` satisfies `q^2 ≠ 1`. -/
lemma q_sq_ne_one : YangBaxterProof.q ^ 2 ≠ 1 := by
  have hq : fibRSym .tau .tau .unit * fibRSym .tau .tau .unit = YangBaxterProof.q ^ 2 := by
    simp [fibRSym, FibAdmB, pow_two]
  intro h
  apply fibRSym_tau_unit_square_ne_one
  rwa [hq]

/-- Canonical unique index in `Fin 1`. -/
def finZero : Fin 1 := ⟨0, Nat.zero_lt_one⟩

theorem fin_one_unique (i : Fin 1) : i = finZero := by
  ext
  omega

/-- Non-triviality of the squared braiding on `tau ⊗ tau`. -/
theorem fibonacci_braiding_squared_ne_id :
    (BraidedCategory.braiding (tauVec : FibObject → ℕ) tauVec).hom ≫
      (BraidedCategory.braiding tauVec tauVec).hom ≠ 𝟙 (tauVec ⊗ tauVec) := by
  intro h
  have h_hom : (fibVecBraiding tauVec tauVec).hom ≫ (fibVecBraiding tauVec tauVec).hom =
      𝟙 (fibFamOfVec (fibVecTensorObj tauVec tauVec)) := h
  have hconj :
      (fibFamBraiding (fibFamOfVec tauVec) (fibFamOfVec tauVec)).hom ≫
        (fibFamBraiding (fibFamOfVec tauVec) (fibFamOfVec tauVec)).hom =
      𝟙 (fibFamTensorObj (fibFamOfVec tauVec) (fibFamOfVec tauVec)) := by
    have h1 := congr_arg (fun f => (fibVecTensorIso tauVec tauVec).hom ≫ f ≫ (fibVecTensorIso tauVec tauVec).inv) h_hom
    change (fibVecTensorIso tauVec tauVec).hom ≫
      (((fibVecTensorIso tauVec tauVec).inv ≫ (fibFamBraiding (fibFamOfVec tauVec) (fibFamOfVec tauVec)).hom ≫ (fibVecTensorIso tauVec tauVec).hom) ≫
        ((fibVecTensorIso tauVec tauVec).inv ≫ (fibFamBraiding (fibFamOfVec tauVec) (fibFamOfVec tauVec)).hom ≫ (fibVecTensorIso tauVec tauVec).hom)) ≫
      (fibVecTensorIso tauVec tauVec).inv =
      (fibVecTensorIso tauVec tauVec).hom ≫ 𝟙 _ ≫ (fibVecTensorIso tauVec tauVec).inv at h1
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id] at h1
    exact h1
  let z : (fibFamTensorObj (fibFamOfVec tauVec) (fibFamOfVec tauVec)).idx .unit :=
    ⟨(.tau, .tau), ⟨⟨rfl⟩, finZero, finZero⟩⟩
  have : Unique ((fibFamTensorObj (fibFamOfVec tauVec) (fibFamOfVec tauVec)).idx .unit) :=
    { default := z
      uniq := fun v => by
        rcases v with ⟨⟨a, b⟩, ⟨h⟩, i, j⟩
        cases a with
        | unit => exact i.elim0
        | tau =>
          cases b with
          | unit => exact j.elim0
          | tau =>
            have hi : i = finZero := fin_one_unique i
            have hj : j = finZero := fin_one_unique j
            subst hi hj
            rfl }
  have hv := congrFun (congrFun (congrFun hconj .unit) z) z
  change (∑ v : (fibFamTensorObj (fibFamOfVec tauVec) (fibFamOfVec tauVec)).idx .unit,
    (fibFamBraiding (fibFamOfVec tauVec) (fibFamOfVec tauVec)).hom .unit z v *
      (fibFamBraiding (fibFamOfVec tauVec) (fibFamOfVec tauVec)).hom .unit v z) =
    (if z = z then 1 else 0) at hv
  rw [Fintype.sum_unique] at hv
  have hzd : z = default := Subsingleton.elim _ _
  rw [hzd] at hv
  have hdef : (default : (fibFamTensorObj (fibFamOfVec tauVec) (fibFamOfVec tauVec)).idx .unit) = z := Subsingleton.elim _ _
  have hval : (fibFamBraiding (fibFamOfVec tauVec) (fibFamOfVec tauVec)).hom .unit default default = fibRSym .tau .tau .unit := by
    rw [hdef]
    simp [fibFamBraiding, homEntry, FibFam.id_apply, fibFamOfVec, tauVec, z, finZero]
  rw [hval, ite_eq_left rfl] at hv
  exact fibRSym_tau_unit_square_ne_one hv

/-- 1. Schur's lemma for unit: Hom(1, 1) ≅ ℂ. -/
def homOneOneEquiv : ((oneVec : FibObject → ℕ) ⟶ (oneVec : FibObject → ℕ)) ≃ ℂ where
  toFun f := f FibObject.unit finZero finZero
  invFun c s := match s with
    | .unit => fun _ _ => c
    | .tau  => fun i _ => i.elim0
  left_inv f := by
    funext s i j
    cases s with
    | unit => rw [fin_one_unique i, fin_one_unique j]
    | tau  => exact Fin.elim0 i
  right_inv c := rfl

/-- 2. Schur's lemma for tau: Hom(tau, tau) ≅ ℂ. -/
def homTauTauEquiv : ((tauVec : FibObject → ℕ) ⟶ (tauVec : FibObject → ℕ)) ≃ ℂ where
  toFun f := f FibObject.tau finZero finZero
  invFun c s := match s with
    | .unit => fun i _ => i.elim0
    | .tau  => fun _ _ => c
  left_inv f := by
    funext s i j
    cases s with
    | unit => exact Fin.elim0 i
    | tau  => rw [fin_one_unique i, fin_one_unique j]
  right_inv c := rfl

/-- 3. Orthogonality of simple objects: Hom(1, tau) is zero-dimensional (Unique). -/
instance uniqueHomOneTau : Unique ((oneVec : FibObject → ℕ) ⟶ (tauVec : FibObject → ℕ)) where
  default s := match s with
    | .unit => fun _ j => j.elim0
    | .tau  => fun i _ => i.elim0
  uniq f := by
    funext s i j
    cases s with
    | unit => exact Fin.elim0 j
    | tau  => exact Fin.elim0 i

/-- 4. Fusion channel multiplicity N_{tau tau}^1 = 1: Hom(1, tau ⊗ tau) ≅ ℂ. -/
def homOneTauTauEquiv : ((oneVec : FibObject → ℕ) ⟶ fibVecTensorObj tauVec tauVec) ≃ ℂ where
  toFun f := f FibObject.unit finZero finZero
  invFun c s := match s with
    | .unit => fun _ _ => c
    | .tau  => fun i _ => i.elim0
  left_inv f := by
    funext s i j
    cases s with
    | unit => rw [fin_one_unique i, fin_one_unique j]
    | tau  => exact Fin.elim0 i
  right_inv c := rfl

/-- 5. Fusion channel multiplicity N_{tau tau}^tau = 1: Hom(tau, tau ⊗ tau) ≅ ℂ. -/
def homTauTauTauEquiv : ((tauVec : FibObject → ℕ) ⟶ fibVecTensorObj tauVec tauVec) ≃ ℂ where
  toFun f := f FibObject.tau finZero finZero
  invFun c s := match s with
    | .unit => fun i _ => i.elim0
    | .tau  => fun _ _ => c
  left_inv f := by
    funext s i j
    cases s with
    | unit => exact Fin.elim0 i
    | tau  => rw [fin_one_unique i, fin_one_unique j]
  right_inv c := rfl

/-- Full Debt D6 package theorem establishing all properties required by `FibonacciBraidedClaimPred`. -/
theorem fibonacci_braided_category_package :
    (𝟙_ (FibObject → ℕ) = oneVec) ∧
    (∀ X Y : FibObject → ℕ,
      (X ⊗ Y) FibObject.unit = X FibObject.unit * Y FibObject.unit + X FibObject.tau * Y FibObject.tau ∧
      (X ⊗ Y) FibObject.tau =
        X FibObject.unit * Y FibObject.tau + X FibObject.tau * Y FibObject.unit +
          X FibObject.tau * Y FibObject.tau) ∧
    Nonempty (((oneVec : FibObject → ℕ) ⟶ oneVec) ≃ ℂ) ∧
    Nonempty (((tauVec : FibObject → ℕ) ⟶ tauVec) ≃ ℂ) ∧
    Nonempty (Unique ((oneVec : FibObject → ℕ) ⟶ tauVec)) ∧
    Nonempty (((oneVec : FibObject → ℕ) ⟶ fibVecTensorObj tauVec tauVec) ≃ ℂ) ∧
    Nonempty (((tauVec : FibObject → ℕ) ⟶ fibVecTensorObj tauVec tauVec) ≃ ℂ) ∧
    ((BraidedCategory.braiding (tauVec : FibObject → ℕ) tauVec).hom ≫
      (BraidedCategory.braiding tauVec tauVec).hom ≠ 𝟙 (tauVec ⊗ tauVec)) :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl⟩, ⟨homOneOneEquiv⟩, ⟨homTauTauEquiv⟩, ⟨inferInstance⟩,
   ⟨homOneTauTauEquiv⟩, ⟨homTauTauTauEquiv⟩, fibonacci_braiding_squared_ne_id⟩

end InfoGeometry.Categorical.FibonacciMonoidalBraidedInstance
