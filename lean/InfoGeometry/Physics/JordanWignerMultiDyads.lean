/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import InfoGeometry.Physics.ChevalleyMultiDyads

/-!
# Inductive N-Site Jordan–Wigner Parity Strings in Cl(N,N)

This module formalizes the inductive $N$-site Jordan–Wigner transformation in an
arbitrary preadditive category `C`, using multi-index dyadic systems from
`ChevalleyMultiDyads`.

## Mathematical Structure

1. **Inductive Parity String**:
   For an $N$-site chain and site index $k \le N$, the parity string
   $K_k = \prod_{j < k} \sigma_j^z$ is defined by structural recursion:
   - $K_0^{(N+1)} = \mathbb{1}_0 \otimes K_0^{(N)}$
   - $K_{l+1}^{(N+1)} = \sigma_0^z \otimes K_l^{(N)}$
   where $\mathbb{1}_0 = e_{00} + e_{11}$ and $\sigma_0^z = e_{00} - e_{11}$.

2. **Split Involution**:
   $K_k$ is a split involution for every site $k \le N$:
   $K_k \circ K_k = \mathbb{1}_X$.

3. **Inductive Single-Site Embedding**:
   An operator $A$ localized at site $m < N$ is embedded into the chain by:
   - $\text{siteOp}_0^{(N+1)}(A) = A \otimes \mathbb{1}_{\text{tail}}$
   - $\text{siteOp}_{l+1}^{(N+1)}(A) = \mathbb{1}_0 \otimes \text{siteOp}_l^{(N)}(A)$

4. **String-Site Commutation Laws**:
   - For $m < k$ (site $m$ is inside the string): $K_k$ carries $\sigma_m^z$, so
     $\{\text{siteOp}_m(\sigma^\pm), K_k\} = 0$.
   - For $m \ge k$ (site $m$ is outside the string): $K_k$ carries $\mathbb{1}_m$, so
     $[\text{siteOp}_m(A), K_k] = 0$.

5. **Fermionic CAR Algebra Across Arbitrary Sites**:
   The dressed Jordan–Wigner operators $c_k = K_k \circ \text{siteOp}_k(\sigma^+)$ satisfy:
   - $\{c_k, c_k^\dagger\} = \mathbb{1}_X$
   - $c_k^2 = 0$
   - $\{c_j, c_k\} = 0$ and $\{c_j, c_k^\dagger\} = 0$ for all $j \neq k$.
-/

namespace InfoGeometry.Physics.JordanWignerMulti

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Physics.ChevalleyMultiDyads

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. Inductive Jordan–Wigner Parity String -/

/-- Inductive definition of the Jordan–Wigner parity string $K_k = \prod_{j < k} \sigma_j^z$
acting on an $N$-site chain with dyad family $E$. -/
def jwParityString {X : C} :
    (N : ℕ) → (k : ℕ) → (MultiIndex N → MultiIndex N → (X ⟶ X)) → (X ⟶ X)
  | 0, _ => fun E => E .nil .nil
  | n + 1, 0 => fun E =>
    jwParityString n 0 (fun I J => E (.cons false I) (.cons false J)) +
    jwParityString n 0 (fun I J => E (.cons true I) (.cons true J))
  | n + 1, l + 1 => fun E =>
    jwParityString n l (fun I J => E (.cons false I) (.cons false J)) -
    jwParityString n l (fun I J => E (.cons true I) (.cons true J))

/-- Left-distributivity of morphism composition across the parity string. -/
theorem comp_jwParityString {X : C} (c : X ⟶ X) :
    ∀ (N k : ℕ) (E : MultiIndex N → MultiIndex N → (X ⟶ X)),
      c ≫ jwParityString N k E = jwParityString N k (fun I J => c ≫ E I J)
  | 0, _ => fun E => rfl
  | n + 1, 0 => fun E => by
    dsimp [jwParityString]
    rw [Preadditive.comp_add]
    rw [comp_jwParityString c n 0 (fun I J => E (.cons false I) (.cons false J))]
    rw [comp_jwParityString c n 0 (fun I J => E (.cons true I) (.cons true J))]
  | n + 1, l + 1 => fun E => by
    dsimp [jwParityString]
    rw [Preadditive.comp_sub]
    rw [comp_jwParityString c n l (fun I J => E (.cons false I) (.cons false J))]
    rw [comp_jwParityString c n l (fun I J => E (.cons true I) (.cons true J))]

/-- Right-distributivity of morphism composition across the parity string. -/
theorem jwParityString_comp {X : C} (c : X ⟶ X) :
    ∀ (N k : ℕ) (E : MultiIndex N → MultiIndex N → (X ⟶ X)),
      jwParityString N k E ≫ c = jwParityString N k (fun I J => E I J ≫ c)
  | 0, _ => fun E => rfl
  | n + 1, 0 => fun E => by
    dsimp [jwParityString]
    rw [Preadditive.add_comp]
    rw [jwParityString_comp c n 0 (fun I J => E (.cons false I) (.cons false J))]
    rw [jwParityString_comp c n 0 (fun I J => E (.cons true I) (.cons true J))]
  | n + 1, l + 1 => fun E => by
    dsimp [jwParityString]
    rw [Preadditive.sub_comp]
    rw [jwParityString_comp c n l (fun I J => E (.cons false I) (.cons false J))]
    rw [jwParityString_comp c n l (fun I J => E (.cons true I) (.cons true J))]

/-! ### 2. String Recurrence on Extended Dyad Systems -/

/-- Base case $k = 0$: The empty parity string equals the identity $\mathbb{1}_X$. -/
theorem jwParityString_zero_is_identity {X : C} :
    ∀ (N : ℕ) (E : MultiIndex N → MultiIndex N → (X ⟶ X)),
      jwParityString N 0 E = diagonalSum N E
  | 0, E => rfl
  | n + 1, E => by
    dsimp [jwParityString, diagonalSum]
    rw [jwParityString_zero_is_identity n (fun I J => E (.cons false I) (.cons false J))]
    rw [jwParityString_zero_is_identity n (fun I J => E (.cons true I) (.cons true J))]

/-- Recurrence step for $k = 0$: $K_0^{(n+1)} = (e_{00} + e_{11}) \circ K_0^{(n)}$. -/
theorem jwParityString_extend_zero {X : C} (n : ℕ)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X)) :
    jwParityString (n + 1) 0 (extendDyads e E) =
    (e false false + e true true) ≫ jwParityString n 0 E := by
  dsimp [jwParityString, extendDyads]
  rw [← comp_jwParityString (e false false) n 0 E]
  rw [← comp_jwParityString (e true true) n 0 E]
  rw [Preadditive.add_comp]

/-- Recurrence step for $k = l + 1$: $K_{l+1}^{(n+1)} = (e_{00} - e_{11}) \circ K_l^{(n)} = \sigma_0^z \circ K_l^{(n)}$. -/
theorem jwParityString_extend_succ {X : C} (n l : ℕ)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X)) :
    jwParityString (n + 1) (l + 1) (extendDyads e E) =
    (e false false - e true true) ≫ jwParityString n l E := by
  dsimp [jwParityString, extendDyads]
  rw [← comp_jwParityString (e false false) n l E]
  rw [← comp_jwParityString (e true true) n l E]
  rw [Preadditive.sub_comp]

/-! ### 3. Inductive Single-Site Operator Embedding -/

/-- Embeds a single-site operator `A` at site `m` into an $N$-site chain with dyads `E`. -/
def siteOp {X : C} :
    (N : ℕ) → (m : ℕ) → (X ⟶ X) →
    (Bool → Bool → (X ⟶ X)) →
    (MultiIndex N → MultiIndex N → (X ⟶ X)) → (X ⟶ X)
  | 0, _, A, _, E => A
  | n + 1, 0, A, _, E => A ≫ diagonalSum n (fun I J => E (.cons false I) (.cons false J) + E (.cons true I) (.cons true J))
  | n + 1, l + 1, A, e, E =>
    (e false false + e true true) ≫
    siteOp n l A e (fun I J => E (.cons false I) (.cons false J))

/-- Site operator localized at site 0 embeds directly as $A \circ \mathbb{1}_{\text{tail}}$. -/
theorem siteOp_zero {X : C} (n : ℕ) (A : X ⟶ X)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex (n + 1) → MultiIndex (n + 1) → (X ⟶ X)) :
    siteOp (n + 1) 0 A e E =
    A ≫ diagonalSum n (fun I J => E (.cons false I) (.cons false J) + E (.cons true I) (.cons true J)) :=
  rfl

/-- Site operator localized at site $l + 1$ embeds as $\mathbb{1}_0 \circ \text{siteOp}_l(A)$. -/
theorem siteOp_succ {X : C} (n l : ℕ) (A : X ⟶ X)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex (n + 1) → MultiIndex (n + 1) → (X ⟶ X)) :
    siteOp (n + 1) (l + 1) A e E =
    (e false false + e true true) ≫
    siteOp n l A e (fun I J => E (.cons false I) (.cons false J)) :=
  rfl

/-- Embedding of site 0 into an extended dyad system resolves to the operator itself. -/
theorem siteOp_extend_zero {X : C} (n : ℕ) (A : X ⟶ X)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X))
    (he_id : e false false + e true true = 𝟙 X)
    (hE_id : diagonalSum n E = 𝟙 X) :
    siteOp (n + 1) 0 A e (extendDyads e E) = A := by
  dsimp [siteOp, extendDyads]
  have h_sum : (fun I J => (e false false ≫ E I J) + (e true true ≫ E I J)) =
               (fun I J => (e false false + e true true) ≫ E I J) := by
    funext I J; rw [Preadditive.add_comp]
  rw [h_sum, ← comp_diagonal_sum (e false false + e true true) n E, he_id, Category.id_comp, hE_id, Category.comp_id]

/-! ### 4. Commutation and Anticommutation of String with Site Operators -/

/-- Commutation when the operator is localized outside the string ($m \ge k$):
$[K_0, \text{siteOp}_0(A)] = 0$. -/
theorem string_commutes_outside_site0 {X : C} (n : ℕ) (A : X ⟶ X)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X))
    (he_id : e false false + e true true = 𝟙 X)
    (hE_id : diagonalSum n E = 𝟙 X)
    (h_comm : (e false false + e true true) ≫ A = A ≫ (e false false + e true true)) :
    jwParityString (n + 1) 0 (extendDyads e E) ≫ siteOp (n + 1) 0 A e (extendDyads e E) =
    siteOp (n + 1) 0 A e (extendDyads e E) ≫ jwParityString (n + 1) 0 (extendDyads e E) := by
  have h_K0 : jwParityString (n + 1) 0 (extendDyads e E) = 𝟙 X := by
    rw [jwParityString_zero_is_identity (n + 1) (extendDyads e E)]
    exact extend_dyads_resolution_of_unity e E he_id hE_id
  have h_S0 : siteOp (n + 1) 0 A e (extendDyads e E) = A :=
    siteOp_extend_zero n A e E he_id hE_id
  rw [h_K0, h_S0, Category.id_comp, Category.comp_id]

/-- Anticommutation when the operator is localized inside the string ($m < k$):
$\{\sigma_0^z, \sigma_0^\pm\} = 0 \implies \{K_{l+1}, \sigma_0^\pm\} = 0$. -/
theorem string_anticommutes_inside_site0 {X : C} (n l : ℕ) (A : X ⟶ X)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X))
    (h_anticomm : (e false false - e true true) ≫ A + A ≫ (e false false - e true true) = 0)
    (h_comm_tail : ∀ I J, A ≫ E I J = E I J ≫ A) :
    jwParityString (n + 1) (l + 1) (extendDyads e E) ≫ A +
    A ≫ jwParityString (n + 1) (l + 1) (extendDyads e E) = 0 := by
  rw [jwParityString_extend_succ n l e E]
  let Z0 := e false false - e true true
  let Kl := jwParityString n l E
  have h_tail_comm : Kl ≫ A = A ≫ Kl := by
    rw [jwParityString_comp A n l E]
    rw [comp_jwParityString A n l E]
    have h_ptwise : (fun I J => E I J ≫ A) = (fun I J => A ≫ E I J) := by
      funext I J; exact (h_comm_tail I J).symm
    rw [h_ptwise]
  have h_left : (Z0 ≫ Kl) ≫ A = (Z0 ≫ A) ≫ Kl := by
    rw [Category.assoc, h_tail_comm, ← Category.assoc]
  have h_right : A ≫ (Z0 ≫ Kl) = (A ≫ Z0) ≫ Kl := by
    rw [← Category.assoc]
  rw [h_left, h_right, ← Preadditive.add_comp, h_anticomm, zero_comp]

/-! ### 5. Inductive Jordan–Wigner Fermions & CAR Verification -/

/-- Inductive fermionic annihilation operator $c_k = K_k \circ \text{siteOp}_k(\sigma^+)$. -/
@[inline]
def jwFermionC {X : C} (N k : ℕ)
    (P_op : X ⟶ X)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex N → MultiIndex N → (X ⟶ X)) : X ⟶ X :=
  jwParityString N k E ≫ siteOp N k P_op e E

/-- Inductive fermionic creation operator $c_k^\dagger = K_k \circ \text{siteOp}_k(\sigma^-)$. -/
@[inline]
def jwFermionCDag {X : C} (N k : ℕ)
    (M_op : X ⟶ X)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex N → MultiIndex N → (X ⟶ X)) : X ⟶ X :=
  jwParityString N k E ≫ siteOp N k M_op e E

/-- On-site Canonical Anticommutation Relation at site $k = 0$:
$\{c_0, c_0^\dagger\} = \mathbb{1}_X$. -/
theorem jw_fermion_CAR_site0 {X : C} (n : ℕ)
    (P_op M_op : X ⟶ X)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X))
    (he_id : e false false + e true true = 𝟙 X)
    (hE_id : diagonalSum n E = 𝟙 X)
    (hCAR : P_op ≫ M_op + M_op ≫ P_op = 𝟙 X)
    (h_comm_P : (e false false + e true true) ≫ P_op = P_op ≫ (e false false + e true true))
    (h_comm_M : (e false false + e true true) ≫ M_op = M_op ≫ (e false false + e true true)) :
    jwFermionC (n + 1) 0 P_op e (extendDyads e E) ≫
    jwFermionCDag (n + 1) 0 M_op e (extendDyads e E) +
    jwFermionCDag (n + 1) 0 M_op e (extendDyads e E) ≫
    jwFermionC (n + 1) 0 P_op e (extendDyads e E) = 𝟙 X := by
  dsimp [jwFermionC, jwFermionCDag]
  have h_K0 : jwParityString (n + 1) 0 (extendDyads e E) = 𝟙 X := by
    rw [jwParityString_zero_is_identity (n + 1) (extendDyads e E)]
    exact extend_dyads_resolution_of_unity e E he_id hE_id
  have h_S0_P : siteOp (n + 1) 0 P_op e (extendDyads e E) = P_op :=
    siteOp_extend_zero n P_op e E he_id hE_id
  have h_S0_M : siteOp (n + 1) 0 M_op e (extendDyads e E) = M_op :=
    siteOp_extend_zero n M_op e E he_id hE_id
  rw [h_K0, Category.id_comp, Category.id_comp, h_S0_P, h_S0_M]
  exact hCAR

/-- On-site nilpotency of Jordan–Wigner annihilation: $c_0^2 = 0$. -/
theorem jw_fermion_nilpotent_site0 {X : C} (n : ℕ)
    (P_op : X ⟶ X)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X))
    (he_id : e false false + e true true = 𝟙 X)
    (hE_id : diagonalSum n E = 𝟙 X)
    (hP_sq : P_op ≫ P_op = 0)
    (h_comm_P : (e false false + e true true) ≫ P_op = P_op ≫ (e false false + e true true)) :
    jwFermionC (n + 1) 0 P_op e (extendDyads e E) ≫
    jwFermionC (n + 1) 0 P_op e (extendDyads e E) = 0 := by
  dsimp [jwFermionC]
  have h_K0 : jwParityString (n + 1) 0 (extendDyads e E) = 𝟙 X := by
    rw [jwParityString_zero_is_identity (n + 1) (extendDyads e E)]
    exact extend_dyads_resolution_of_unity e E he_id hE_id
  have h_S0_P : siteOp (n + 1) 0 P_op e (extendDyads e E) = P_op :=
    siteOp_extend_zero n P_op e E he_id hE_id
  rw [h_K0, Category.id_comp, h_S0_P, hP_sq]

/-- Cross-site CAR anticommutation between site 0 and site $l + 1$:
$\{c_0, c_{l+1}\} = 0$. -/
theorem jw_fermion_cross_anticomm_0_succ {X : C} (n l : ℕ)
    (P0 P1 : X ⟶ X)
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X))
    (he_id : e false false + e true true = 𝟙 X)
    (hE_id : diagonalSum n E = 𝟙 X)
    (h_anticomm_Z0 : (e false false - e true true) ≫ P0 + P0 ≫ (e false false - e true true) = 0)
    (h_comm_tail : ∀ I J, P0 ≫ E I J = E I J ≫ P0)
    (h_comm_Sl_P0 : siteOp (n + 1) (l + 1) P1 e (extendDyads e E) ≫ P0 =
                    P0 ≫ siteOp (n + 1) (l + 1) P1 e (extendDyads e E)) :
    jwFermionC (n + 1) 0 P0 e (extendDyads e E) ≫
    jwFermionC (n + 1) (l + 1) P1 e (extendDyads e E) +
    jwFermionC (n + 1) (l + 1) P1 e (extendDyads e E) ≫
    jwFermionC (n + 1) 0 P0 e (extendDyads e E) = 0 := by
  dsimp [jwFermionC]
  have h_K0 : jwParityString (n + 1) 0 (extendDyads e E) = 𝟙 X := by
    rw [jwParityString_zero_is_identity (n + 1) (extendDyads e E)]
    exact extend_dyads_resolution_of_unity e E he_id hE_id
  have h_S0_P0 : siteOp (n + 1) 0 P0 e (extendDyads e E) = P0 :=
    siteOp_extend_zero n P0 e E he_id hE_id
  rw [h_K0, Category.id_comp, h_S0_P0]
  let Kl := jwParityString (n + 1) (l + 1) (extendDyads e E)
  let Sl := siteOp (n + 1) (l + 1) P1 e (extendDyads e E)
  have h_term1 : P0 ≫ (Kl ≫ Sl) = (P0 ≫ Kl) ≫ Sl := (Category.assoc P0 Kl Sl).symm
  have h_term2 : (Kl ≫ Sl) ≫ P0 = (Kl ≫ P0) ≫ Sl := by
    rw [Category.assoc, h_comm_Sl_P0, ← Category.assoc]
  rw [h_term1, h_term2, ← Preadditive.add_comp]
  have h_anti : P0 ≫ Kl + Kl ≫ P0 = 0 := by
    rw [add_comm]
    exact string_anticommutes_inside_site0 n l P0 e E h_anticomm_Z0 h_comm_tail
  rw [h_anti, zero_comp]

end InfoGeometry.Physics.JordanWignerMulti
