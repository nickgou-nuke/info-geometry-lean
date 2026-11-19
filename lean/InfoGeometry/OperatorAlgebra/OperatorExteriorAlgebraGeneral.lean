/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Alternating.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus

/-!
# Arbitrary-Degree Operator Forms & Exact Onsager–Casimir Time-Reversal Derivation

This module provides the complete formalization:
1. Operator-valued differential forms of arbitrary degree `n ∈ ℕ`:
     `OpForm R V A n := AlternatingMap R V A (Fin n)`
2. Functorial pullback `ϕ*` on forms of arbitrary degree `n` via `AlternatingMap.compLinearMap`.
3. Derivation action `D(ω)` on forms of arbitrary degree `n`.
4. Strict deduction of the Onsager–Casimir reciprocity theorem:
     `W(Tu, Tv) = W(v, u)`
   derived purely from the time-even parity of `L` and time-odd parity of `Ω`.
5. Graded exterior product `opWedge` on `OpForm` (via `DerivationExteriorCalculus`),
   `ExteriorAlgebra` (`Op1Form`/`Op2Form`/`wedge`) compatibility, `derivN_opWedge` Leibniz,
   and exact DGA bridges to `ActionOperatorForm` / `DerivationOperatorForm`.
6. Adapters for `FormDerivation` and `ExteriorAlgebra.OpDerivation` into the unified
   `NonAssocDerivation.derivations` / `DerivationLieLane` / `LieActionLane` spine.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.General

variable {R V W U A : Type*}
variable [Ring R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable [Ring A] [Module R A]

/-!
=============================================================================
PART 1: Operator-Valued Differential Forms of Arbitrary Degree n ∈ ℕ
=============================================================================
-/

/-- 
  An operator-valued differential form of arbitrary degree `n ∈ ℕ` on module V
  with values in operator ring A over a (possibly noncommutative) ring R,
  formalized as an Alternating Multilinear Map.
-/
abbrev OpForm (R V A : Type*) (n : ℕ)
    [Ring R] [AddCommGroup V] [Module R V] [Ring A] [Module R A] :=
  AlternatingMap R V A (Fin n)

/-- Pullback of an operator form of arbitrary degree `n` along a linear map `ϕ : W →ₗ[R] V`. -/
def pullbackN (n : ℕ) (ϕ : W →ₗ[R] V) (ω : OpForm R V A n) : OpForm R W A n :=
  AlternatingMap.compLinearMap ω ϕ

@[simp]
theorem pullbackN_apply (n : ℕ) (ϕ : W →ₗ[R] V) (ω : OpForm R V A n) (v : Fin n → W) :
    pullbackN n ϕ ω v = ω (fun i => ϕ (v i)) := rfl

/-- 
  THEOREM 1 (Functoriality of Pullbacks for Arbitrary Degree n):
  (ψ ∘ ϕ)* ω = ψ* (ϕ* ω)
-/
theorem pullbackN_comp (n : ℕ) (ψ : U →ₗ[R] W) (ϕ : W →ₗ[R] V) (ω : OpForm R V A n) :
    pullbackN n (ϕ.comp ψ) ω = pullbackN n ψ (pullbackN n ϕ ω) := by
  ext v
  simp only [pullbackN_apply, LinearMap.coe_comp, Function.comp_apply]

/-!
=============================================================================
PART 2: Derivation Action on Forms of Arbitrary Degree n ∈ ℕ
=============================================================================
-/

/-- An R-linear derivation on the operator ring A over a (possibly noncommutative) ring R. -/
structure FormDerivation (R A : Type*) [Ring R] [Ring A] [Module R A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (c : R) x, toFun (c • x) = c • toFun x
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

instance : CoeFun (FormDerivation R A) (fun _ => A → A) where
  coe D := D.toFun

namespace FormDerivation

variable (D : FormDerivation R A)

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem map_smul (c : R) (x : A) : D (c • x) = c • D x := D.map_smul' c x
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 = D 0 + D 0 := by
    calc D 0 = D (0 + 0) := by rw [add_zero]
    _ = D 0 + D 0 := D.map_add 0 0
  have h1 : D 0 - D 0 = (D 0 + D 0) - D 0 := congr_arg (fun x => x - D 0) h
  rw [sub_self, add_sub_cancel_right] at h1
  exact h1.symm

end FormDerivation

/-- 
  Action of a derivation on an operator form of arbitrary degree `n`:
  (D ω)(v₁, ..., vₙ) = D(ω(v₁, ..., vₙ))
-/
def derivN (n : ℕ) (D : FormDerivation R A) (ω : OpForm R V A n) : OpForm R V A n where
  toFun v := D (ω v)
  map_update_add' v i x y := by
    simp only [AlternatingMap.map_update_add, D.map_add]
  map_update_smul' v i c x := by
    simp only [AlternatingMap.map_update_smul, D.map_smul]
  map_eq_zero_of_eq' v i j hij h_eq := by
    rw [AlternatingMap.map_eq_zero_of_eq ω v hij h_eq, D.map_zero]

@[simp]
theorem derivN_apply (n : ℕ) (D : FormDerivation R A) (ω : OpForm R V A n) (v : Fin n → V) :
    derivN n D ω v = D (ω v) := rfl

/-- Transport an arbitrary-degree operator-valued form through an R-linear map
on its coefficient operator ring. -/
def mapN {C : Type*} [Ring C] [Module R C] (n : ℕ)
    (f : A →ₗ[R] C) (ω : OpForm R V A n) : OpForm R V C n :=
  f.compAlternatingMap ω

@[simp] theorem mapN_apply {C : Type*} [Ring C] [Module R C] (n : ℕ)
    (f : A →ₗ[R] C) (ω : OpForm R V A n) (v : Fin n → V) :
    mapN n f ω v = f (ω v) := rfl

@[simp] theorem mapN_id (n : ℕ) (ω : OpForm R V A n) :
    mapN n (LinearMap.id : A →ₗ[R] A) ω = ω := by
  ext v
  rfl

/-- Arbitrary-degree coefficient transport is functorial under composition of
R-linear maps. -/
theorem mapN_comp {C D : Type*} [Ring C] [Module R C]
    [Ring D] [Module R D] (n : ℕ)
    (f : A →ₗ[R] C) (g : C →ₗ[R] D) (ω : OpForm R V A n) :
    mapN n (g.comp f) ω = mapN n g (mapN n f ω) := by
  ext v
  rfl

/-- An R-linear map intertwining two coefficient derivations induces a
map of their arbitrary-degree operator-valued form derivation actions. -/
theorem mapN_derivN {C : Type*} [Ring C] [Module R C]
    (n : ℕ) (f : A →ₗ[R] C) (D : FormDerivation R A)
    (E : FormDerivation R C)
    (hDE : ∀ a, f (D a) = E (f a)) (ω : OpForm R V A n) :
    mapN n f (derivN n D ω) = derivN n E (mapN n f ω) := by
  ext v
  exact hDE (ω v)

/-- Applying a coefficient derivation to an operator-valued form commutes with
pullback along a linear map. This is the naturality square relating the
operator derivation action to changes of parameter coordinates. -/
theorem derivN_pullbackN (n : ℕ) (D : FormDerivation R A)
    (ϕ : W →ₗ[R] V) (ω : OpForm R V A n) :
    derivN n D (pullbackN n ϕ ω) = pullbackN n ϕ (derivN n D ω) := by
  ext v
  rfl

/-!
=============================================================================
PART 3: Exact Derivation of Onsager–Casimir Reciprocity from Parities
=============================================================================
-/

/-- An R-bilinear transport tensor W(u, v) over a (possibly noncommutative) ring R. -/
structure TransportTensor (R V A : Type*) [Ring R] [AddCommGroup V] [Module R V] [Ring A] [Module R A] where
  toFun : V → V → A
  map_add_left' : ∀ u v w, toFun (u + v) w = toFun u w + toFun v w
  map_add_right' : ∀ u v w, toFun u (v + w) = toFun u v + toFun u w
  map_smul_left' : ∀ (c : R) u v, toFun (c • u) v = c • toFun u v
  map_smul_right' : ∀ (c : R) u v, toFun u (c • v) = c • toFun u v

instance : CoeFun (TransportTensor R V A) (fun _ => V → V → A) where
  coe W := W.toFun

namespace TransportTensor

variable (W : TransportTensor R V A)

/-- The Symmetric Dissipative Tensor: L(u, v) = (1/2) • (W(u, v) + W(v, u)). -/
def symmPart (half : R) (u v : V) : A :=
  half • (W.toFun u v + W.toFun v u)

/-- The Alternating Reversible 2-Form: Ω(u, v) = (1/2) • (W(u, v) - W(v, u)). -/
def altPart (half : R) (u v : V) : A :=
  half • (W.toFun u v - W.toFun v u)

@[simp]
theorem symmPart_symm (half : R) (u v : V) :
    W.symmPart half u v = W.symmPart half v u := by
  dsimp [symmPart]
  rw [add_comm]

@[simp]
theorem altPart_skew (half : R) (u v : V) :
    W.altPart half u v = - W.altPart half v u := by
  dsimp [altPart]
  rw [← smul_neg]
  have h_sub : - (W.toFun v u - W.toFun u v) = W.toFun u v - W.toFun v u := by abel
  rw [h_sub]

/-- Exact Metriplectic Decomposition: W(u, v) = L(u, v) + Ω(u, v). -/
theorem decomposition (half : R) (h_half : (2 : R) * half = 1) (u v : V) :
    W.toFun u v = W.symmPart half u v + W.altPart half u v := by
  dsimp [symmPart, altPart]
  rw [← smul_add]
  have h_add : (W.toFun u v + W.toFun v u) + (W.toFun u v - W.toFun v u) = (2 : R) • (W.toFun u v) := by
    calc
      (W.toFun u v + W.toFun v u) + (W.toFun u v - W.toFun v u) =
        (W.toFun u v + W.toFun u v) + (W.toFun v u - W.toFun v u) := by abel
      _ = (2 : R) • (W.toFun u v) + 0 := by rw [two_smul, sub_self]
      _ = (2 : R) • (W.toFun u v) := by rw [add_zero]
  rw [h_add, smul_smul]
  have h_norm : half * 2 = 1 := by rw [mul_two, ← two_mul, h_half]
  rw [h_norm, one_smul]

/-- 
  THEOREM 2 (Exact Derivation of Onsager–Casimir Reciprocity):
  Given a Time-Reversal operator T on V, if:
  1. The dissipative part L is time-even:  L(Tu, Tv) = L(u, v)
  2. The Hamiltonian part Ω is time-odd:   Ω(Tu, Tv) = - Ω(u, v)
  THEN the transport tensor satisfies Onsager transpose reciprocity:
    W(Tu, Tv) = W(v, u)
-/
theorem onsager_casimir_reciprocity_exact
    (half : R) (h_half : (2 : R) * half = 1)
    (T : V →ₗ[R] V) (u v : V)
    (hL_even : W.symmPart half (T u) (T v) = W.symmPart half u v)
    (hOmega_odd : W.altPart half (T u) (T v) = - W.altPart half u v) :
    W.toFun (T u) (T v) = W.toFun v u := by
  -- 1. Decompose W(Tu, Tv) into L(Tu, Tv) + Ω(Tu, Tv)
  rw [W.decomposition half h_half (T u) (T v)]
  -- 2. Apply time-reversal parities: L(Tu,Tv) = L(u,v) and Ω(Tu,Tv) = -Ω(u,v)
  rw [hL_even, hOmega_odd]
  -- 3. Use L(u,v) = L(v,u) and -Ω(u,v) = Ω(v,u)
  have hL_symm : W.symmPart half u v = W.symmPart half v u := W.symmPart_symm half u v
  have hOmega_skew : - W.altPart half u v = W.altPart half v u := by
    have h := W.altPart_skew half u v
    rw [h, neg_neg]
  rw [hL_symm, hOmega_skew]
  -- 4. Reconstruct W(v, u) = L(v, u) + Ω(v, u)
  exact (W.decomposition half h_half v u).symm

end TransportTensor

end InfoGeometry.OperatorAlgebra.General

namespace InfoGeometry.OperatorAlgebra.General

/-!
=============================================================================
PART 4: Graded Exterior Product `opWedge` & `ExteriorAlgebra` Compatibility
=============================================================================
-/

section GradedWedge

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-- Abelian trivial `LieActionLane` on any `R`-module `V`, so that
`ActionOperatorForm (trivialLieActionLane R V A) n` is definitionally `OpForm R V A n`. -/
def trivialLieActionLane (R V A : Type*) [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup A] [Module R A] :
    LieActionLane R A :=
  letI : LieRing V :=
    { bracket := fun _ _ => 0
      add_lie := fun _ _ _ => (add_zero 0).symm
      lie_add := fun _ _ _ => (add_zero 0).symm
      lie_self := fun _ => rfl
      leibniz_lie := fun _ _ _ => (add_zero 0).symm }
  letI : LieAlgebra R V :=
    { lie_smul := fun _ _ _ => (smul_zero _).symm }
  { L := V
    lieRing := ‹_›
    lieAlgebra := ‹_›
    act := 0 }

section FormDerivationLinearMap

variable {R A : Type*} [Ring R] [Ring A] [Module R A]

/-- Bundle a `FormDerivation R A` as an `R`-linear endomorphism of `A`. -/
def FormDerivation.toLinearMap (D : FormDerivation R A) : A →ₗ[R] A where
  toFun := D.toFun
  map_add' := D.map_add'
  map_smul' := D.map_smul'

@[simp] theorem FormDerivation.toLinearMap_apply (D : FormDerivation R A) (a : A) :
    D.toLinearMap a = D a :=
  rfl

@[simp] theorem FormDerivation.map_neg (D : FormDerivation R A) (a : A) : D (-a) = -D a :=
  D.toLinearMap.map_neg a

@[simp] theorem FormDerivation.map_sub (D : FormDerivation R A) (a b : A) : D (a - b) = D a - D b :=
  D.toLinearMap.map_sub a b

end FormDerivationLinearMap

section DerivNHelpers

variable {R V A : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Ring A] [Module R A]

@[simp] theorem derivN_curryLeft (n : ℕ) (D : FormDerivation R A)
    (ω : OpForm R V A (n + 1)) (x : V) :
    (derivN (n + 1) D ω).curryLeft x = derivN n D (ω.curryLeft x) :=
  rfl

@[simp] theorem derivN_add (n : ℕ) (D : FormDerivation R A)
    (ω η : OpForm R V A n) :
    derivN n D (ω + η) = derivN n D ω + derivN n D η := by
  ext v
  simp [derivN_apply, D.map_add]

@[simp] theorem derivN_smul (n : ℕ) (D : FormDerivation R A)
    (c : R) (ω : OpForm R V A n) :
    derivN n D (c • ω) = c • derivN n D ω := by
  ext v
  simp [derivN_apply, D.map_smul]

theorem derivN_reindexForm {m n : ℕ} (h : m = n) (D : FormDerivation R A)
    (ω : OpForm R V A m) :
    derivN n D (reindexForm h ω) = reindexForm h (derivN m D ω) := by
  subst h
  rfl

end DerivNHelpers

section BasicWedge

variable {R V W A : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [Ring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

/-- Bilinear noncommutative graded wedge product on `OpForm R V A`. -/
def opWedgeBil (p q : ℕ) :
    OpForm R V A p →ₗ[R] OpForm R V A q →ₗ[R] OpForm R V A (p + q) :=
  actionWedgeBil (trivialLieActionLane R V A) p q

/-- Noncommutative graded wedge product on `OpForm R V A`. -/
def opWedge {p q : ℕ} (ω : OpForm R V A p) (η : OpForm R V A q) :
    OpForm R V A (p + q) :=
  actionWedge (trivialLieActionLane R V A) ω η

@[simp] theorem opWedge_zero_left {q : ℕ} (a : OpForm R V A 0) (η : OpForm R V A q) :
    opWedge a η =
      reindexForm (Nat.zero_add q).symm
        ((LinearMap.mul R A (a Fin.elim0)).compAlternatingMap η) :=
  actionWedge_zero_left (trivialLieActionLane R V A) a η

@[simp] theorem opWedge_zero_right {p : ℕ} (ω : OpForm R V A p) (b : OpForm R V A 0) :
    opWedge ω b = ((LinearMap.mul R A).flip (b Fin.elim0)).compAlternatingMap ω :=
  actionWedge_zero_right (trivialLieActionLane R V A) ω b

@[simp] theorem opWedge_zero_zero_apply (a b : OpForm R V A 0) (v : Fin 0 → V) :
    opWedge a b v = a Fin.elim0 * b Fin.elim0 :=
  actionWedge_zero_zero_apply (trivialLieActionLane R V A) a b v

@[simp] theorem opWedge_one_one_apply (ω η : OpForm R V A 1) (x y : V) :
    opWedge ω η ![x, y] = ω ![x] * η ![y] - ω ![y] * η ![x] :=
  actionWedge_one_one_apply (trivialLieActionLane R V A) ω η x y

@[simp] theorem opWedge_succ_succ_curryLeft {p' q' : ℕ}
    (ω : OpForm R V A (p' + 1)) (η : OpForm R V A (q' + 1)) (x : V) :
    (opWedge ω η).curryLeft x =
      reindexForm (by omega : p' + (q' + 1) = p' + 1 + q')
        (opWedge (ω.curryLeft x) η) +
        ((-1 : R) ^ (p' + 1)) • opWedge ω (η.curryLeft x) :=
  actionWedge_succ_succ_curryLeft (trivialLieActionLane R V A) ω η x

theorem opWedge_reindexForm_left {p₁ p₂ q : ℕ} (h : p₁ = p₂)
    (ω : OpForm R V A p₁) (η : OpForm R V A q) :
    opWedge (reindexForm h ω) η = reindexForm (congrArg (· + q) h) (opWedge ω η) :=
  actionWedge_reindexForm_left (trivialLieActionLane R V A) h ω η

theorem opWedge_reindexForm_right {p q₁ q₂ : ℕ} (h : q₁ = q₂)
    (ω : OpForm R V A p) (η : OpForm R V A q₁) :
    opWedge ω (reindexForm h η) = reindexForm (congrArg (p + ·) h) (opWedge ω η) :=
  actionWedge_reindexForm_right (trivialLieActionLane R V A) h ω η

@[simp] theorem opWedge_add_left {p q : ℕ} (ω₁ ω₂ : OpForm R V A p) (η : OpForm R V A q) :
    opWedge (ω₁ + ω₂) η = opWedge ω₁ η + opWedge ω₂ η :=
  actionWedge_add_left (trivialLieActionLane R V A) ω₁ ω₂ η

@[simp] theorem opWedge_add_right {p q : ℕ} (ω : OpForm R V A p) (η₁ η₂ : OpForm R V A q) :
    opWedge ω (η₁ + η₂) = opWedge ω η₁ + opWedge ω η₂ :=
  actionWedge_add_right (trivialLieActionLane R V A) ω η₁ η₂

@[simp] theorem opWedge_sub_left {p q : ℕ} (ω₁ ω₂ : OpForm R V A p) (η : OpForm R V A q) :
    opWedge (ω₁ - ω₂) η = opWedge ω₁ η - opWedge ω₂ η :=
  actionWedge_sub_left (trivialLieActionLane R V A) ω₁ ω₂ η

@[simp] theorem opWedge_sub_right {p q : ℕ} (ω : OpForm R V A p) (η₁ η₂ : OpForm R V A q) :
    opWedge ω (η₁ - η₂) = opWedge ω η₁ - opWedge ω η₂ :=
  actionWedge_sub_right (trivialLieActionLane R V A) ω η₁ η₂

@[simp] theorem opWedge_smul_left {p q : ℕ} (c : R) (ω : OpForm R V A p) (η : OpForm R V A q) :
    opWedge (c • ω) η = c • opWedge ω η :=
  actionWedge_smul_left (trivialLieActionLane R V A) c ω η

@[simp] theorem opWedge_smul_right {p q : ℕ} (c : R) (ω : OpForm R V A p) (η : OpForm R V A q) :
    opWedge ω (c • η) = c • opWedge ω η :=
  actionWedge_smul_right (trivialLieActionLane R V A) c ω η

@[simp] theorem opWedge_zero_val_left {p q : ℕ} (η : OpForm R V A q) :
    opWedge (0 : OpForm R V A p) η = 0 :=
  actionWedge_zero_val_left (trivialLieActionLane R V A) η

@[simp] theorem opWedge_zero_val_right {p q : ℕ} (ω : OpForm R V A p) :
    opWedge ω (0 : OpForm R V A q) = 0 :=
  actionWedge_zero_val_right (trivialLieActionLane R V A) ω

/-- Functoriality of pullback with respect to `opWedge`:
`ϕ*(ω ∧ η) = (ϕ* ω) ∧ (ϕ* η)`. -/
theorem pullbackN_opWedge (ϕ : W →ₗ[R] V) {p q : ℕ}
    (ω : OpForm R V A p) (η : OpForm R V A q) :
    pullbackN (p + q) ϕ (opWedge ω η) =
      opWedge (pullbackN p ϕ ω) (pullbackN q ϕ η) :=
  pullbackActionForm_actionWedge
    (K₁ := trivialLieActionLane R W A) (K₂ := trivialLieActionLane R V A) ϕ ω η

/-- Graded Leibniz rule for the coefficient derivation action `derivN` on `opWedge`:
`D (ω ∧ η) = (D ω) ∧ η + ω ∧ (D η)`. -/
theorem derivN_opWedge (D : FormDerivation R A) :
    ∀ (p q : ℕ) (ω : OpForm R V A p) (η : OpForm R V A q),
      derivN (p + q) D (opWedge ω η) =
        opWedge (derivN p D ω) η + opWedge ω (derivN q D η)
  | 0, q, ω, η => by
    ext v
    simp only [derivN_apply, opWedge_zero_left, reindexForm_apply,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply',
      AlternatingMap.add_apply, D.leibniz]
  | p' + 1, 0, ω, η => by
    ext v
    simp only [derivN_apply, opWedge_zero_right,
      LinearMap.compAlternatingMap_apply, LinearMap.flip_apply,
      LinearMap.mul_apply', AlternatingMap.add_apply, D.leibniz]
  | p' + 1, q' + 1, ω, η => by
    apply alternating_ext_curryLeft
    intro x
    change derivN (p' + 1 + q') D ((opWedge ω η).curryLeft x) =
      (opWedge (derivN (p' + 1) D ω) η + opWedge ω (derivN (q' + 1) D η)).curryLeft x
    rw [opWedge_succ_succ_curryLeft, derivN_add, derivN_reindexForm,
      derivN_smul, derivN_opWedge D p' (q' + 1) (ω.curryLeft x) η,
      derivN_opWedge D (p' + 1) q' ω (η.curryLeft x)]
    rw [AlternatingMap.curryLeft_add, LinearMap.add_apply,
      opWedge_succ_succ_curryLeft, opWedge_succ_succ_curryLeft]
    simp only [derivN_curryLeft, reindexForm_add, smul_add]
    abel

end BasicWedge

section AssociativeCompatibility

variable {R V A : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [Ring A] [Algebra R A]

@[simp] theorem mapN_curryLeft {C : Type*} [Ring C] [Module R C] (n : ℕ)
    (f : A →ₗ[R] C) (ω : OpForm R V A (n + 1)) (x : V) :
    (mapN (n + 1) f ω).curryLeft x = mapN n f (ω.curryLeft x) :=
  rfl

theorem mapN_reindexForm {C : Type*} [Ring C] [Module R C] {m n : ℕ} (h : m = n)
    (f : A →ₗ[R] C) (ω : OpForm R V A m) :
    mapN n f (reindexForm h ω) = reindexForm h (mapN m f ω) := by
  subst h
  rfl

@[simp] theorem mapN_add {C : Type*} [Ring C] [Module R C] (n : ℕ)
    (f : A →ₗ[R] C) (ω η : OpForm R V A n) :
    mapN n f (ω + η) = mapN n f ω + mapN n f η := by
  ext v
  simp [mapN_apply]

@[simp] theorem mapN_smul {C : Type*} [Ring C] [Module R C] (n : ℕ)
    (f : A →ₗ[R] C) (c : R) (ω : OpForm R V A n) :
    mapN n f (c • ω) = c • mapN n f ω := by
  ext v
  simp [mapN_apply]

/-- Coefficient transport along an `R`-algebra homomorphism preserves `opWedge`. -/
theorem mapN_opWedge {C : Type*} [Ring C] [Algebra R C] (f : A →ₐ[R] C) :
    ∀ (p q : ℕ) (ω : OpForm R V A p) (η : OpForm R V A q),
      mapN (p + q) f.toLinearMap (opWedge ω η) =
        opWedge (mapN p f.toLinearMap ω) (mapN q f.toLinearMap η)
  | 0, q, ω, η => by
    ext v
    simp only [mapN_apply, opWedge_zero_left, reindexForm_apply,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]
    exact f.map_mul _ _
  | p' + 1, 0, ω, η => by
    ext v
    simp only [mapN_apply, opWedge_zero_right, LinearMap.compAlternatingMap_apply,
      LinearMap.flip_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]
    exact f.map_mul _ _
  | p' + 1, q' + 1, ω, η => by
    apply alternating_ext_curryLeft
    intro x
    change mapN (p' + 1 + q') f.toLinearMap ((opWedge ω η).curryLeft x) =
      (opWedge (mapN (p' + 1) f.toLinearMap ω) (mapN (q' + 1) f.toLinearMap η)).curryLeft x
    rw [opWedge_succ_succ_curryLeft, mapN_add, mapN_reindexForm,
      mapN_smul, mapN_opWedge f p' (q' + 1) (ω.curryLeft x) η,
      mapN_opWedge f (p' + 1) q' ω (η.curryLeft x)]
    rw [opWedge_succ_succ_curryLeft, mapN_curryLeft, mapN_curryLeft]

/-- Associativity of `opWedge` over an associative `R`-algebra `A`. -/
theorem opWedge_assoc {p q r : ℕ}
    (ω : OpForm R V A p) (η : OpForm R V A q) (θ : OpForm R V A r) :
    reindexForm (Nat.add_assoc p q r) (opWedge (opWedge ω η) θ) =
      opWedge ω (opWedge η θ) :=
  actionWedge_assoc (trivialLieActionLane R V A) p q r ω η θ

/-- Linear equivalence between `ExteriorAlgebra.Op1Form R V A` and `OpForm R V A 1`. -/
def op1FormEquivOpForm :
    ExteriorAlgebra.Op1Form R V A ≃ₗ[R] OpForm R V A 1 where
  toLinearMap :=
    { toFun := AlternatingMap.ofSubsingleton R V A (0 : Fin 1)
      map_add' := fun _ _ => by ext v; rfl
      map_smul' := fun _ _ => by ext v; rfl }
  invFun η :=
    { toFun := fun x => η (fun _ => x)
      map_add' := fun x y => by
        have h : (fun _ : Fin 1 => x + y) = Function.update (fun _ => x) 0 (x + y) :=
          funext fun i => by fin_cases i; rfl
        have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
          funext fun i => by fin_cases i; rfl
        have h1 : (fun _ : Fin 1 => y) = Function.update (fun _ => x) 0 y :=
          funext fun i => by fin_cases i; rfl
        rw [h, η.map_update_add, ← h0, ← h1]
      map_smul' := fun c x => by
        have h : (fun _ : Fin 1 => c • x) = Function.update (fun _ => x) 0 (c • x) :=
          funext fun i => by fin_cases i; rfl
        have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
          funext fun i => by fin_cases i; rfl
        change η (fun _ => c • x) = c • η (fun _ => x)
        rw [h, η.map_update_smul, ← h0] }
  left_inv _ := by ext x; rfl
  right_inv η := by
    ext v
    change η (fun _ => v 0) = η v
    congr 1
    ext i
    rw [Fin.eq_zero i]

@[simp] theorem op1FormEquivOpForm_apply (α : ExteriorAlgebra.Op1Form R V A) (v : Fin 1 → V) :
    op1FormEquivOpForm α v = α (v 0) :=
  rfl

@[simp] theorem op1FormEquivOpForm_symm_apply (η : OpForm R V A 1) (x : V) :
    op1FormEquivOpForm.symm η x = η (fun _ => x) :=
  rfl

/-- Equivalence between `ExteriorAlgebra.Op2Form R V A` and `OpForm R V A 2`. -/
def op2FormEquivOpForm :
    ExteriorAlgebra.Op2Form R V A ≃ OpForm R V A 2 where
  toFun ω :=
    { MultilinearMap.mk' (fun v : Fin 2 → V => ω (v 0) (v 1))
        (fun v i x y => by fin_cases i <;> simp [Function.update])
        (fun v i c x => by fin_cases i <;> simp [Function.update]) with
      map_eq_zero_of_eq' := fun v i j hv hij => by
        fin_cases i <;> fin_cases j <;> dsimp at hv hij
        · exact (hij rfl).elim
        · change ω (v 0) (v 1) = 0
          rw [hv]
          exact ω.alt (v 1)
        · change ω (v 0) (v 1) = 0
          rw [hv]
          exact ω.alt (v 0)
        · exact (hij rfl).elim }
  invFun η :=
    ⟨LinearMap.mk₂ R (fun x y => η ![x, y])
      (fun x₁ x₂ y => by
        have h1 : ![x₁ + x₂, y] = Function.update ![x₁, y] 0 (x₁ + x₂) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x₁, y] = Function.update ![x₁, y] 0 x₁ := by
          ext i; fin_cases i <;> rfl
        have h2 : ![x₂, y] = Function.update ![x₁, y] 0 x₂ := by
          ext i; fin_cases i <;> rfl
        rw [h1, η.map_update_add, ← h0, ← h2])
      (fun c x y => by
        have h1 : ![c • x, y] = Function.update ![x, y] 0 (c • x) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x, y] = Function.update ![x, y] 0 x := by
          ext i; fin_cases i <;> rfl
        rw [h1, η.map_update_smul, ← h0])
      (fun x y₁ y₂ => by
        have h1 : ![x, y₁ + y₂] = Function.update ![x, y₁] 1 (y₁ + y₂) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x, y₁] = Function.update ![x, y₁] 1 y₁ := by
          ext i; fin_cases i <;> rfl
        have h2 : ![x, y₂] = Function.update ![x, y₁] 1 y₂ := by
          ext i; fin_cases i <;> rfl
        rw [h1, η.map_update_add, ← h0, ← h2])
      (fun c x y => by
        have h1 : ![x, c • y] = Function.update ![x, y] 1 (c • y) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x, y] = Function.update ![x, y] 1 y := by
          ext i; fin_cases i <;> rfl
        rw [h1, η.map_update_smul, ← h0]),
     fun x => η.map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)⟩
  left_inv _ := ExteriorAlgebra.Op2Form.ext _ _ (fun _ _ => rfl)
  right_inv η := by
    ext v
    change η ![v 0, v 1] = η v
    congr 1
    ext i
    fin_cases i <;> rfl

@[simp] theorem op2FormEquivOpForm_apply (ω : ExteriorAlgebra.Op2Form R V A) (v : Fin 2 → V) :
    op2FormEquivOpForm ω v = ω (v 0) (v 1) :=
  rfl

@[simp] theorem op2FormEquivOpForm_symm_apply (η : OpForm R V A 2) (x y : V) :
    op2FormEquivOpForm.symm η x y = η ![x, y] :=
  rfl

@[simp] theorem op2FormEquivOpForm_zero :
    op2FormEquivOpForm (0 : ExteriorAlgebra.Op2Form R V A) = 0 := by
  ext v
  rfl

@[simp] theorem op2FormEquivOpForm_add (ω₁ ω₂ : ExteriorAlgebra.Op2Form R V A) :
    op2FormEquivOpForm (ω₁ + ω₂) = op2FormEquivOpForm ω₁ + op2FormEquivOpForm ω₂ := by
  ext v
  rfl

@[simp] theorem op2FormEquivOpForm_neg (ω : ExteriorAlgebra.Op2Form R V A) :
    op2FormEquivOpForm (-ω) = -op2FormEquivOpForm ω := by
  ext v
  rfl

@[simp] theorem op2FormEquivOpForm_sub (ω₁ ω₂ : ExteriorAlgebra.Op2Form R V A) :
    op2FormEquivOpForm (ω₁ - ω₂) = op2FormEquivOpForm ω₁ - op2FormEquivOpForm ω₂ := by
  ext v
  rfl

@[simp] theorem op2FormEquivOpForm_smul (c : R) (ω : ExteriorAlgebra.Op2Form R V A) :
    op2FormEquivOpForm (c • ω) = c • op2FormEquivOpForm ω := by
  ext v
  rfl

/-- `op2FormEquivOpForm` intertwines `ExteriorAlgebra.wedge` with `opWedge`. -/
theorem op2FormEquivOpForm_wedge (α β : ExteriorAlgebra.Op1Form R V A) :
    op2FormEquivOpForm (ExteriorAlgebra.wedge α β) =
      opWedge (op1FormEquivOpForm α) (op1FormEquivOpForm β) := by
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, opWedge_one_one_apply]
  rfl

theorem op1FormEquivOpForm_pullback1 {W : Type*} [AddCommGroup W] [Module R W]
    (ϕ : W →ₗ[R] V) (α : ExteriorAlgebra.Op1Form R V A) :
    op1FormEquivOpForm (R := R) (V := W) (A := A) (ExteriorAlgebra.pullback1 ϕ α) =
      pullbackN 1 ϕ (op1FormEquivOpForm (R := R) (V := V) (A := A) α) := by
  ext v
  rfl

theorem op2FormEquivOpForm_pullback2 {W : Type*} [AddCommGroup W] [Module R W]
    (ϕ : W →ₗ[R] V) (ω : ExteriorAlgebra.Op2Form R V A) :
    op2FormEquivOpForm (R := R) (V := W) (A := A) (ExteriorAlgebra.pullback2 ϕ ω) =
      pullbackN 2 ϕ (op2FormEquivOpForm (R := R) (V := V) (A := A) ω) := by
  ext v
  rfl

theorem op1FormEquivOpForm_map1 {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (α : ExteriorAlgebra.Op1Form R V A) :
    op1FormEquivOpForm (R := R) (V := V) (A := B) (ExteriorAlgebra.map1 f α) =
      mapN 1 f.toLinearMap (op1FormEquivOpForm (R := R) (V := V) (A := A) α) := by
  ext v
  rfl

theorem op2FormEquivOpForm_map2 {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (ω : ExteriorAlgebra.Op2Form R V A) :
    op2FormEquivOpForm (R := R) (V := V) (A := B) (ExteriorAlgebra.map2 f ω) =
      mapN 2 f.toLinearMap (op2FormEquivOpForm (R := R) (V := V) (A := A) ω) := by
  ext v
  rfl

end AssociativeCompatibility

section CommutativeSpecialization

variable {R V A : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [CommRing A] [Algebra R A]

/-- Graded commutativity of `opWedge` when `A` is a commutative `R`-algebra. -/
theorem opWedge_comm_of_commRing {p q : ℕ}
    (ω : OpForm R V A p) (η : OpForm R V A q) :
    opWedge ω η =
      ((-1 : R) ^ (p * q)) • reindexForm (Nat.add_comm q p) (opWedge η ω) :=
  actionWedge_comm_of_commRing (trivialLieActionLane R V A) p q ω η

/-- Self-wedge of a 1-form vanishes when `A` is a commutative `R`-algebra. -/
theorem opWedge_self_one_eq_zero_of_commRing (ω : OpForm R V A 1) :
    opWedge ω ω = 0 := by
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, opWedge_one_one_apply, mul_comm, sub_self]
  rfl

end CommutativeSpecialization

end GradedWedge

/-!
=============================================================================
PART 5: `OpForm` ↔ `ActionOperatorForm` / `DerivationOperatorForm` DGA Bridge
=============================================================================
-/

section ExteriorCalculusBridge

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

section ActionLaneBridge

variable {R A : Type*} [CommRing R] [Ring A] [Module R A]

/-- Definitional `R`-linear equivalence `OpForm R K.L A n ≃ₗ[R] ActionOperatorForm K n`. -/
def opFormEquivActionForm (K : LieActionLane R A) (n : ℕ) :
    OpForm R K.L A n ≃ₗ[R] ActionOperatorForm K n :=
  LinearEquiv.refl R _

/-- Chevalley--Eilenberg exterior derivative transferred onto `OpForm R K.L A n`. -/
def opExteriorDerivative (K : LieActionLane R A) (n : ℕ) :
    OpForm R K.L A n →ₗ[R] OpForm R K.L A (n + 1) :=
  actionExteriorDerivative K n

/-- `d_{n+1} ∘ d_n = 0` on `OpForm R K.L A n` (without faithfulness). -/
theorem opExteriorDerivative_succ_comp (K : LieActionLane R A) (n : ℕ)
    (ω : OpForm R K.L A n) :
    opExteriorDerivative K (n + 1) (opExteriorDerivative K n ω) = 0 :=
  actionExteriorDerivative_succ_comp K n ω

/-- Pullback along a Lie-action-equivariant homomorphism commutes with `opExteriorDerivative`. -/
theorem pullbackN_opExteriorDerivative {K₁ K₂ : LieActionLane R A}
    (φ : K₁.L →ₗ⁅R⁆ K₂.L)
    (hact : ∀ (x : K₁.L) (a : A), K₁.operatorAction x a = K₂.operatorAction (φ x) a)
    (n : ℕ) (ω : OpForm R K₂.L A n) :
    opExteriorDerivative K₁ n (pullbackN n (φ : K₁.L →ₗ[R] K₂.L) ω) =
      pullbackN (n + 1) (φ : K₁.L →ₗ[R] K₂.L) (opExteriorDerivative K₂ n ω) :=
  pullbackActionForm_actionExteriorDerivative φ hact n ω

section WedgeAgreement

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- `opWedge` agrees identically with `actionWedge K` when `V = K.L`. -/
theorem opWedge_eq_actionWedge (K : LieActionLane R A) {p q : ℕ}
    (ω : OpForm R K.L A p) (η : OpForm R K.L A q) :
    opWedge ω η = actionWedge K ω η :=
  (pullbackActionForm_actionWedge (K₁ := trivialLieActionLane R K.L A) (K₂ := K)
    LinearMap.id ω η).symm

/-- Graded Leibniz rule for `opExteriorDerivative` and `opWedge` under `IsLeibnizAction K`. -/
theorem opExteriorDerivative_opWedge (K : LieActionLane R A) (hK : IsLeibnizAction K)
    (p q : ℕ) (ω : OpForm R K.L A p) (η : OpForm R K.L A q) :
    opExteriorDerivative K (p + q) (opWedge ω η) =
      reindexForm (by omega : (p + 1) + q = p + q + 1)
        (opWedge (opExteriorDerivative K p ω) η) +
        ((-1 : R) ^ p) •
          reindexForm (by omega : p + (q + 1) = p + q + 1)
            (opWedge ω (opExteriorDerivative K q η)) := by
  rw [opWedge_eq_actionWedge K ω η, opWedge_eq_actionWedge K (opExteriorDerivative K p ω) η,
    opWedge_eq_actionWedge K ω (opExteriorDerivative K q η)]
  exact actionExteriorDerivative_actionWedge K hK p q ω η

/-- Pullback of `opWedge` from a `LieActionLane` carrier to any `R`-module `V`. -/
theorem pullbackN_opWedge_lane (K : LieActionLane R A) {V : Type*}
    [AddCommGroup V] [Module R V] (ϕ : V →ₗ[R] K.L) {p q : ℕ}
    (ω : OpForm R K.L A p) (η : OpForm R K.L A q) :
    pullbackN (p + q) ϕ (opWedge ω η) =
      opWedge (pullbackN p ϕ ω) (pullbackN q ϕ η) :=
  pullbackN_opWedge ϕ ω η

end WedgeAgreement

/-- Coefficient derivations commuting with the `LieActionLane` action commute with `lieDeriv`. -/
theorem derivN_lieDeriv (K : LieActionLane R A) (D : FormDerivation R A)
    (hDK : ∀ (x : K.L) (a : A), D (K.operatorAction x a) = K.operatorAction x (D a))
    (x : K.L) {n : ℕ} (ω : OpForm R K.L A n) :
    derivN n D (lieDeriv K x ω) = lieDeriv K x (derivN n D ω) := by
  ext v
  simp only [derivN_apply, lieDeriv_apply, D.map_sub, hDK]
  congr 1
  exact map_sum D.toLinearMap _ _

/-- Coefficient derivations commuting with the `LieActionLane` action commute with
`opExteriorDerivative`. -/
theorem derivN_opExteriorDerivative (K : LieActionLane R A) (D : FormDerivation R A)
    (hDK : ∀ (x : K.L) (a : A), D (K.operatorAction x a) = K.operatorAction x (D a))
    (n : ℕ) (ω : OpForm R K.L A n) :
    derivN (n + 1) D (opExteriorDerivative K n ω) =
      opExteriorDerivative K n (derivN n D ω) := by
  induction n with
  | zero =>
    apply alternating_ext_curryLeft
    intro x
    rw [derivN_curryLeft]
    exact derivN_lieDeriv K D hDK x ω
  | succ m ih =>
    apply alternating_ext_curryLeft
    intro x
    rw [derivN_curryLeft]
    change derivN (m + 1) D (lieDeriv K x ω - opExteriorDerivative K m (ω.curryLeft x)) =
      lieDeriv K x (derivN (m + 1) D ω) -
        opExteriorDerivative K m ((derivN (m + 1) D ω).curryLeft x)
    ext w
    simp only [derivN_apply, AlternatingMap.sub_apply, D.map_sub]
    have h1 := AlternatingMap.congr_fun (derivN_lieDeriv K D hDK x ω) w
    have h2 := AlternatingMap.congr_fun (ih (ω.curryLeft x)) w
    simp only [derivN_apply] at h1 h2
    rw [h1, h2]
    rfl

end ActionLaneBridge

section DerivationLaneBridge

variable {R A : Type*} [CommRing R] [Ring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Definitional `R`-linear equivalence `OpForm R K.L A n ≃ₗ[R] DerivationOperatorForm K n`. -/
def opFormEquivDerivationForm (K : DerivationLieLane R A) (n : ℕ) :
    OpForm R K.L A n ≃ₗ[R] DerivationOperatorForm K n :=
  LinearEquiv.refl R _

/-- `opWedge` agrees identically with `ceWedge K` when `V = K.L`. -/
theorem opWedge_eq_ceWedge (K : DerivationLieLane R A) {p q : ℕ}
    (ω : OpForm R K.L A p) (η : OpForm R K.L A q) :
    opWedge ω η = ceWedge K ω η :=
  opWedge_eq_actionWedge K.toLieActionLane ω η

/-- `opExteriorDerivative` on `K.toLieActionLane` is definitionally `ceExteriorDerivative K`. -/
theorem opExteriorDerivative_eq_ceExteriorDerivative (K : DerivationLieLane R A) (n : ℕ) :
    opExteriorDerivative K.toLieActionLane n = ceExteriorDerivative K n :=
  rfl

end DerivationLaneBridge

end ExteriorCalculusBridge

/-!
=============================================================================
PART 6: `FormDerivation` & `ExteriorAlgebra.OpDerivation` M1A Spine Adapters
=============================================================================
-/

section DerivationSpineAdapters

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

section NoncommRingAdapters

variable {R A : Type*} [Ring R] [Ring A] [Module R A]

@[ext] theorem FormDerivation.ext {D E : FormDerivation R A}
    (h : ∀ x : A, D x = E x) : D = E := by
  cases D; cases E; congr; exact funext h

instance : Zero (FormDerivation R A) where
  zero :=
    { toFun := 0
      map_add' := fun _ _ => (add_zero 0).symm
      map_smul' := fun _ _ => (smul_zero _).symm
      leibniz' := fun _ _ => by simp }

instance : Add (FormDerivation R A) where
  add D E :=
    { toFun := fun x => D x + E x
      map_add' := fun x y => by
        simp only [D.map_add, E.map_add]
        abel
      map_smul' := fun c x => by
        simp only [D.map_smul, E.map_smul, smul_add]
      leibniz' := fun x y => by
        simp only [D.leibniz, E.leibniz, add_mul, mul_add]
        abel }

instance : Neg (FormDerivation R A) where
  neg D :=
    { toFun := fun x => -D x
      map_add' := fun x y => by simp only [D.map_add, neg_add]
      map_smul' := fun c x => by simp only [D.map_smul, smul_neg]
      leibniz' := fun x y => by
        simp only [D.leibniz, neg_add, neg_mul, mul_neg] }

instance : Sub (FormDerivation R A) where
  sub D E :=
    { toFun := fun x => D x - E x
      map_add' := fun x y => by
        simp only [D.map_add, E.map_add]
        abel
      map_smul' := fun c x => by
        simp only [D.map_smul, E.map_smul, smul_sub]
      leibniz' := fun x y => by
        simp only [D.leibniz, E.leibniz, sub_mul, mul_sub]
        abel }

instance : AddCommGroup (FormDerivation R A) where
  add_assoc D E F := by ext x; exact add_assoc (D x) (E x) (F x)
  zero_add D := by ext x; exact zero_add (D x)
  add_zero D := by ext x; exact add_zero (D x)
  neg_add_cancel D := by ext x; exact neg_add_cancel (D x)
  add_comm D E := by ext x; exact add_comm (D x) (E x)
  sub_eq_add_neg D E := by ext x; exact sub_eq_add_neg (D x) (E x)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Bracket (FormDerivation R A) (FormDerivation R A) where
  bracket D E :=
    { toFun := fun x => D (E x) - E (D x)
      map_add' := fun x y => by
        simp only [E.map_add, D.map_add]
        abel
      map_smul' := fun c x => by
        simp only [E.map_smul, D.map_smul, smul_sub]
      leibniz' := fun x y => by
        simp only [E.leibniz, D.map_add, D.leibniz, E.map_add, sub_mul, mul_sub]
        abel }

@[simp] theorem FormDerivation.zero_apply (x : A) :
    (0 : FormDerivation R A) x = 0 := rfl

@[simp] theorem FormDerivation.add_apply (D E : FormDerivation R A) (x : A) :
    (D + E) x = D x + E x := rfl

@[simp] theorem FormDerivation.neg_apply (D : FormDerivation R A) (x : A) :
    (-D) x = -D x := rfl

@[simp] theorem FormDerivation.sub_apply (D E : FormDerivation R A) (x : A) :
    (D - E) x = D x - E x := rfl

@[simp] theorem FormDerivation.lie_apply (D E : FormDerivation R A) (x : A) :
    ⁅D, E⁆ x = D (E x) - E (D x) := rfl

instance : LieRing (FormDerivation R A) where
  add_lie D E F := by
    ext x
    simp only [FormDerivation.lie_apply, FormDerivation.add_apply, F.map_add]
    abel
  lie_add D E F := by
    ext x
    simp only [FormDerivation.lie_apply, FormDerivation.add_apply, D.map_add]
    abel
  lie_self D := by
    ext x
    simp only [FormDerivation.lie_apply, FormDerivation.zero_apply, sub_self]
  leibniz_lie D E F := by
    ext x
    simp only [FormDerivation.lie_apply, FormDerivation.add_apply,
      D.map_sub, E.map_sub, F.map_sub]
    abel

/-- Canonical equivalence between `FormDerivation R A` and `ExteriorAlgebra.OpDerivation R A`. -/
def formDerivationEquivOpDerivation :
    FormDerivation R A ≃ ExteriorAlgebra.OpDerivation R A where
  toFun D := ⟨D.toLinearMap, D.leibniz'⟩
  invFun D :=
    { toFun := D.toLinearMap
      map_add' := D.toLinearMap.map_add
      map_smul' := D.toLinearMap.map_smul
      leibniz' := D.leibniz' }
  left_inv D := by ext x; rfl
  right_inv D := by cases D; rfl

@[simp] theorem formDerivationEquivOpDerivation_apply (D : FormDerivation R A) (x : A) :
    formDerivationEquivOpDerivation D x = D x :=
  rfl

@[simp] theorem formDerivationEquivOpDerivation_symm_apply
    (D : ExteriorAlgebra.OpDerivation R A) (x : A) :
    formDerivationEquivOpDerivation.symm D x = D x :=
  rfl

/-- Compatibility of `ExteriorAlgebra.applyDeriv1` with `derivN 1`. -/
theorem op1FormEquivOpForm_applyDeriv1 {R' V A' : Type*} [CommRing R']
    [AddCommGroup V] [Module R' V] [Ring A'] [Algebra R' A']
    (D : ExteriorAlgebra.OpDerivation R' A') (α : ExteriorAlgebra.Op1Form R' V A') :
    op1FormEquivOpForm (R := R') (V := V) (A := A') (ExteriorAlgebra.applyDeriv1 D α) =
      derivN 1 (formDerivationEquivOpDerivation.symm D)
        (op1FormEquivOpForm (R := R') (V := V) (A := A') α) := by
  ext v
  rfl

/-- Compatibility of `ExteriorAlgebra.applyDeriv2` with `derivN 2`. -/
theorem op2FormEquivOpForm_applyDeriv2 {R' V A' : Type*} [CommRing R']
    [AddCommGroup V] [Module R' V] [Ring A'] [Algebra R' A']
    (D : ExteriorAlgebra.OpDerivation R' A') (ω : ExteriorAlgebra.Op2Form R' V A') :
    op2FormEquivOpForm (R := R') (V := V) (A := A') (ExteriorAlgebra.applyDeriv2 D ω) =
      derivN 2 (formDerivationEquivOpDerivation.symm D)
        (op2FormEquivOpForm (R := R') (V := V) (A := A') ω) := by
  ext v
  rfl

/-- Restrict any `FormDerivation R A` to an integer-linear `NCG.Calculus.NCDerivation A`. -/
def formDerivationToNCDerivation (D : FormDerivation R A) :
    InfoGeometry.NCG.Calculus.NCDerivation A where
  toLinearMap := D.toLinearMap.restrictScalars ℤ
  leibniz' := D.leibniz'

/-- Restrict any `ExteriorAlgebra.OpDerivation R A` to an integer-linear
`NCG.Calculus.NCDerivation A`. -/
def opDerivationToNCDerivation (D : ExteriorAlgebra.OpDerivation R A) :
    InfoGeometry.NCG.Calculus.NCDerivation A where
  toLinearMap := D.toLinearMap.restrictScalars ℤ
  leibniz' := D.leibniz'

end NoncommRingAdapters

section CommRingAdapters

variable {R A : Type*} [CommRing R] [Ring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

instance : SMul R (FormDerivation R A) where
  smul r D :=
    { toFun := fun x => r • D x
      map_add' := fun x y => by simp only [D.map_add, smul_add]
      map_smul' := fun c x => by
        simp only [D.map_smul]
        exact (smul_comm c r (D x)).symm
      leibniz' := fun x y => by
        simp only [D.leibniz, smul_add, smul_mul_assoc, mul_smul_comm] }

@[simp] theorem FormDerivation.smul_apply (r : R) (D : FormDerivation R A) (x : A) :
    (r • D) x = r • D x := rfl

instance : Module R (FormDerivation R A) where
  one_smul D := by ext x; exact one_smul R (D x)
  mul_smul r s D := by ext x; exact mul_smul r s (D x)
  smul_zero r := by ext x; exact smul_zero r
  smul_add r D E := by ext x; exact smul_add r (D x) (E x)
  add_smul r s D := by ext x; exact add_smul r s (D x)
  zero_smul D := by ext x; exact zero_smul R (D x)

instance : LieAlgebra R (FormDerivation R A) where
  lie_smul r D E := by
    ext x
    simp only [FormDerivation.lie_apply, FormDerivation.smul_apply, D.map_smul, smul_sub]

/-- Lie algebra isomorphism between `FormDerivation R A` and
`NonAssocDerivation.derivations R A`. -/
def formDerivationEquivDerivations :
    FormDerivation R A ≃ₗ⁅R⁆ NonAssocDerivation.derivations R A where
  toFun D := ⟨D.toLinearMap, D.leibniz'⟩
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_lie' := Subtype.ext (LinearMap.ext fun _ => rfl)
  invFun D :=
    { toFun := (D : Module.End R A)
      map_add' := (D : Module.End R A).map_add
      map_smul' := (D : Module.End R A).map_smul
      leibniz' := D.property }
  left_inv D := by ext x; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

@[simp] theorem formDerivationEquivDerivations_apply (D : FormDerivation R A) (x : A) :
    ((formDerivationEquivDerivations D : NonAssocDerivation.derivations R A) :
      Module.End R A) x = D x :=
  rfl

/-- Canonical faithful `DerivationLieLane R A` on `FormDerivation R A`. -/
def formDerivationLieLane (R A : Type*) [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : DerivationLieLane R A where
  L := FormDerivation R A
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := formDerivationEquivDerivations.toLieHom
  faithful := formDerivationEquivDerivations.injective

/-- Equivariant identification between `formDerivationLieLane` and `fullDerivationLieLane`. -/
def formDerivationLaneEquivFull (R A : Type*) [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    DerivationLaneEquiv (formDerivationLieLane R A) (fullDerivationLieLane R A) where
  map := formDerivationEquivDerivations
  equivariant _ := rfl

/-- Faithful `DerivationLieLane R A` on the Lie subalgebra generated by a single `FormDerivation`. -/
def formDerivationSpanLane (D : FormDerivation R A) : DerivationLieLane R A :=
  lieSubalgebraLane (LieSubalgebra.lieSpan R (NonAssocDerivation.derivations R A)
    {formDerivationEquivDerivations D})

/-- One-generator abelian `LieActionLane R A` attached to a single `FormDerivation D`. -/
def formDerivationActionLane (D : FormDerivation R A) : LieActionLane R A :=
  letI : LieRing R :=
    { bracket := fun _ _ => 0
      add_lie := fun _ _ _ => (add_zero 0).symm
      lie_add := fun _ _ _ => (add_zero 0).symm
      lie_self := fun _ => rfl
      leibniz_lie := fun _ _ _ => (add_zero 0).symm }
  letI : LieAlgebra R R :=
    { lie_smul := fun _ _ _ => (smul_zero _).symm }
  { L := R
    lieRing := ‹_›
    lieAlgebra := ‹_›
    act :=
      { toFun := fun r => r • (formDerivationEquivDerivations D : Module.End R A)
        map_add' := fun r s => add_smul r s _
        map_smul' := fun r s => smul_eq_mul r s ▸ mul_smul r s _
        map_lie' := fun {r s} => by
          ext a
          change (0 : R) • D a =
            r • D (s • D a) - s • D (r • D a)
          rw [zero_smul, D.map_smul, D.map_smul, smul_smul, smul_smul, mul_comm r s, sub_self] } }

theorem formDerivationActionLane_isLeibniz (D : FormDerivation R A) :
    IsLeibnizAction (formDerivationActionLane D) := by
  intro r x y
  let r' : R := r
  change r' • D (x * y) = (r' • D x) * y + x * (r' • D y)
  rw [D.leibniz, smul_add, smul_mul_assoc, mul_smul_comm]

/-- Equivalence between `ExteriorAlgebra.OpDerivation R A` and
`NonAssocDerivation.derivations R A` (without adding orphan instances on `OpDerivation`). -/
def opDerivationEquivDerivations :
    ExteriorAlgebra.OpDerivation R A ≃ NonAssocDerivation.derivations R A where
  toFun D := ⟨D.toLinearMap, D.leibniz'⟩
  invFun D := ⟨(D : Module.End R A), D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

@[simp] theorem opDerivationEquivDerivations_apply
    (D : ExteriorAlgebra.OpDerivation R A) (x : A) :
    ((opDerivationEquivDerivations D : NonAssocDerivation.derivations R A) :
      Module.End R A) x = D x :=
  rfl

/-- Lie commutator on `ExteriorAlgebra.OpDerivation R A`. -/
def opDerivationCommutator (D E : ExteriorAlgebra.OpDerivation R A) :
    ExteriorAlgebra.OpDerivation R A :=
  formDerivationEquivOpDerivation
    ⁅formDerivationEquivOpDerivation.symm D, formDerivationEquivOpDerivation.symm E⁆

theorem opDerivationEquivDerivations_commutator
    (D E : ExteriorAlgebra.OpDerivation R A) :
    opDerivationEquivDerivations (opDerivationCommutator D E) =
      ⁅opDerivationEquivDerivations D, opDerivationEquivDerivations E⁆ := by
  apply Subtype.ext
  ext x
  rfl

/-- Faithful `DerivationLieLane R A` on the Lie subalgebra generated by a single
`ExteriorAlgebra.OpDerivation D`. -/
def opDerivationSpanLane (D : ExteriorAlgebra.OpDerivation R A) : DerivationLieLane R A :=
  lieSubalgebraLane (LieSubalgebra.lieSpan R (NonAssocDerivation.derivations R A)
    {opDerivationEquivDerivations D})

/-- One-generator abelian `LieActionLane R A` attached to a single `ExteriorAlgebra.OpDerivation D`. -/
def opDerivationActionLane (D : ExteriorAlgebra.OpDerivation R A) : LieActionLane R A :=
  formDerivationActionLane (formDerivationEquivOpDerivation.symm D)

theorem opDerivationActionLane_isLeibniz (D : ExteriorAlgebra.OpDerivation R A) :
    IsLeibnizAction (opDerivationActionLane D) :=
  formDerivationActionLane_isLeibniz (formDerivationEquivOpDerivation.symm D)

end CommRingAdapters

end DerivationSpineAdapters

end InfoGeometry.OperatorAlgebra.General

end noncomputable section
