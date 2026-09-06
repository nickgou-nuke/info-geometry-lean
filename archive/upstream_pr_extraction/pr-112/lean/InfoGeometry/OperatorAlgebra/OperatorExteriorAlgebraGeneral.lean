import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

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

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.General

variable {R V W U A : Type*}
variable [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable [Ring A] [Algebra R A]

/-!
=============================================================================
PART 1: Operator-Valued Differential Forms of Arbitrary Degree n ∈ ℕ
=============================================================================
-/

/-- 
  An operator-valued differential form of arbitrary degree `n ∈ ℕ` on module V
  with values in algebra A, formalized as an Alternating Multilinear Map.
-/
abbrev OpForm (R V A : Type*) (n : ℕ)
    [CommRing R] [AddCommGroup V] [Module R V] [Ring A] [Algebra R A] :=
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

/-- An R-linear derivation on the algebra A. -/
structure FormDerivation (R A : Type*) [CommRing R] [Ring A] [Algebra R A] where
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

/-!
=============================================================================
PART 3: Exact Derivation of Onsager–Casimir Reciprocity from Parities
=============================================================================
-/

/-- An R-bilinear transport tensor W(u, v). -/
structure TransportTensor (R V A : Type*) [CommRing R] [AddCommGroup V] [Module R V] [Ring A] [Algebra R A] where
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
  have h_norm : half * 2 = 1 := by rw [mul_comm, h_half]
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

end noncomputable section
