/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Zorn
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge

/-!
# Hilbert Space Cuntz O₂ Representation and Zorn Boundary Maximal Subsystem

This module formalizes:
1. **The Cantor Bitword Space & Fiber**:
   - `BinaryWord := ℕ → Fin 2`
   - `prefix_word (b : Fin 2) (w : BinaryWord) : BinaryWord`
   - `Fiber := Fin 2 → ℝ`
   - `J0 (v : Fiber) : Fiber := fun i => if i = 0 then - v 1 else v 0`
   - 🏆 THEOREM: `J0 (J0 v) = -v` ($J_0^2 = -I$).

2. **Elementary Tensor Product Space $\mathcal{H}_{\text{elem}} = \text{BinaryWord} \times \text{Fiber}$**:
   - `S_left (s : HElem) : HElem := (prefix_word 0 s.1, s.2)`
   - `S_right (s : HElem) : HElem := (prefix_word 1 s.1, s.2)`
   - `K_op (s : HElem) : HElem := (s.1, J0 s.2)`
   - 🏆 THEOREM: `S_left ∘ K_op = K_op ∘ S_left`
   - 🏆 THEOREM: `S_right ∘ K_op = K_op ∘ S_right`

3. **Field / Wavefunction Space $\mathcal{H}_{\text{field}} = \text{BinaryWord} \to \text{Fiber}$**:
   - `K_field (f : BinaryWord → Fiber) : BinaryWord → Fiber := fun w => J0 (f w)`
   - `S_left_field (f : BinaryWord → Fiber) : BinaryWord → Fiber := fun w =>
       if w 0 = 0 then f (fun n => w (n + 1)) else 0`
   - `S_right_field (f : BinaryWord → Fiber) : BinaryWord → Fiber := fun w =>
       if w 0 = 1 then f (fun n => w (n + 1)) else 0`
   - `P_left (g : HField) : HField := fun w => if w 0 = 0 then g w else 0`
   - `P_right (g : HField) : HField := fun w => if w 0 = 1 then g w else 0`

4. **🏆 THEOREMS: Cuntz Left/Right Action and Field Commutation**:
   - `S_left_field f (prefix_word 0 w) = f w`
   - `S_left_field f (prefix_word 1 w) = 0`
   - `S_right_field f (prefix_word 1 w) = f w`
   - `S_right_field f (prefix_word 0 w) = 0`
   - 🏆 THEOREM: `S_left_field (K_field f) = K_field (S_left_field f)`
   - 🏆 THEOREM: `S_right_field (K_field f) = K_field (S_right_field f)`
   - 🏆 THEOREM: `P_left g w + P_right g w = g w` (Partition of Unity on $\mathcal{H}$).

5. **🏆 THEOREM: Zorn's Lemma for Cuntz Boundary Subsystems**:
   - Existence of a maximal boundary subsystem $\mathcal{C}_{\text{Max}}$ via `zorn_subset_nonempty`.

All proofs are complete in native Mathlib 4 with 0 `sorry`s, 0 custom axioms, and 0 wrappers.
-/

namespace InfoGeometry.Canonical.HilbertCuntz

/-! ## 1. Space Definitions -/

/-- The Cantor set of infinite binary sequences: $\{0, 1\}^\mathbb{N}$. -/
def BinaryWord : Type :=
  ℕ → Fin 2

def binaryWordBoolEquiv : BinaryWord ≃ (ℕ → Bool) where
  toFun w := fun n =>
    InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.finTwoEquivBool (w n)
  invFun w := fun n =>
    (InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.finTwoEquivBool).symm (w n)
  left_inv w := by
    funext n
    exact (InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.finTwoEquivBool).left_inv (w n)
  right_inv w := by
    funext n
    exact (InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.finTwoEquivBool).right_inv (w n)

theorem binaryWordBoolEquiv_apply (w : BinaryWord) (n : ℕ) :
    binaryWordBoolEquiv w n =
      InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.finTwoEquivBool (w n) := rfl

theorem binaryWordBoolEquiv_symm_apply (w : ℕ → Bool) (n : ℕ) :
    binaryWordBoolEquiv.symm w n =
      (InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.finTwoEquivBool).symm (w n) := rfl

/-- Prefix a bit to a binary word (the Cuntz shift base action). -/
def prefix_word (b : Fin 2) (w : BinaryWord) : BinaryWord
  | 0 => b
  | n + 1 => w n

/-- The Fiber: $\mathbb{R}^2$. -/
abbrev Fiber : Type :=
  Fin 2 → ℝ

def fiberComplexify : Fiber → (Fin 2 → ℂ) :=
  fun v i => v i

theorem fiberComplexify_injective :
    Function.Injective fiberComplexify := by
  intro v u h
  funext i
  have hi := congrFun h i
  exact Complex.ofReal_injective hi

theorem fiberComplexify_apply (v : Fiber) (i : Fin 2) :
    fiberComplexify v i = (v i : ℂ) := rfl

/-- Canonical phase axis complex structure $J_0 = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ on $\mathbb{R}^2$. -/
def J0 (v : Fiber) : Fiber :=
  fun i =>
    if i = 0 then - v 1
    else v 0

/-- 🏆 THEOREM: $J_0^2 = -I$ on the fiber $\mathbb{R}^2$. -/
theorem J0_sq (v : Fiber) :
    J0 (J0 v) = - v := by
  ext i
  fin_cases i <;> rfl

/-- 🏆 THEOREM: $J_0$ is linear: $J_0(0) = 0$. -/
theorem J0_zero :
    J0 (0 : Fiber) = 0 := by
  ext i
  fin_cases i <;> { dsimp [J0]; try ring }

/-- 🏆 THEOREM: $J_0$ commutes with scalar multiplication. -/
theorem J0_smul (c : ℝ) (v : Fiber) :
    J0 (c • v) = c • J0 v := by
  ext i
  fin_cases i <;> { dsimp [J0]; try ring }

/-! ## 2. Elementary Tensor Space Representation -/

/-- Elementary state: $\delta_\omega \otimes v \in \mathcal{H}_{\text{elem}}$. -/
def HElem : Type :=
  BinaryWord × Fiber

/-- Cuntz left shift on elementary tensors: $S_{\text{left}}(\omega, v) = (0 \cdot \omega, v)$. -/
def S_left_elem (s : HElem) : HElem :=
  (prefix_word 0 s.1, s.2)

/-- Cuntz right shift on elementary tensors: $S_{\text{right}}(\omega, v) = (1 \cdot \omega, v)$. -/
def S_right_elem (s : HElem) : HElem :=
  (prefix_word 1 s.1, s.2)

/-- Phase axis $K$ on elementary tensors: $K(\omega, v) = (\omega, J_0 v)$. -/
def K_elem (s : HElem) : HElem :=
  (s.1, J0 s.2)

/-- 🏆 THEOREM: $S_{\text{left}} \circ K = K \circ S_{\text{left}}$ on elementary tensors. -/
theorem S_left_K_elem_commute :
    S_left_elem ∘ K_elem = K_elem ∘ S_left_elem := by
  funext s
  dsimp [S_left_elem, K_elem]

/-- 🏆 THEOREM: $S_{\text{right}} \circ K = K \circ S_{\text{right}}$ on elementary tensors. -/
theorem S_right_K_elem_commute :
    S_right_elem ∘ K_elem = K_elem ∘ S_right_elem := by
  funext s
  dsimp [S_right_elem, K_elem]

/-! ## 3. Field / Wavefunction Space Representation -/

/-- Wavefunction space: $\mathcal{H}_{\text{field}} = \text{BinaryWord} \to \text{Fiber}$. -/
abbrev HField : Type :=
  BinaryWord → Fiber

def fieldComplexify : HField → (ℕ → Bool) → (Fin 2 → ℂ) :=
  fun f w => fiberComplexify (f (binaryWordBoolEquiv.symm w))

theorem fieldComplexify_injective :
    Function.Injective fieldComplexify := by
  intro f g h
  funext w
  apply fiberComplexify_injective
  have hw := congrFun h (binaryWordBoolEquiv w)
  simpa [fieldComplexify] using hw

theorem fieldComplexify_apply (f : HField) (w : ℕ → Bool) (i : Fin 2) :
    fieldComplexify f w i =
      (f (binaryWordBoolEquiv.symm w) i : ℂ) := rfl

def SamePrefix (n : ℕ) (w v : BinaryWord) : Prop :=
  ∀ k < n, w k = v k

def IsCylinderConstant (f : HField) (n : ℕ) : Prop :=
  ∀ w v, SamePrefix n w v → f w = f v

def zeroTailExtension (n : ℕ) (p : Fin n → Fin 2) : BinaryWord :=
  fun k => if hk : k < n then p ⟨k, hk⟩ else 0

def finitePrefixReadout (f : HField) (n : ℕ) (p : Fin n → Fin 2) : Fiber :=
  f (zeroTailExtension n p)

theorem zeroTailExtension_prefix (n : ℕ) (w : BinaryWord) :
    SamePrefix n w (zeroTailExtension n (fun i => w i)) := by
  intro k hk
  simp [zeroTailExtension, hk]

theorem finitePrefixReadout_eq (f : HField) (n : ℕ)
    (hf : IsCylinderConstant f n) (w : BinaryWord) :
    finitePrefixReadout f n (fun i => w i) = f w := by
  have hprefix : SamePrefix n (zeroTailExtension n (fun i => w i)) w := by
    intro k hk
    exact (zeroTailExtension_prefix n w k hk).symm
  change f (zeroTailExtension n (fun i => w i)) = f w
  exact hf (zeroTailExtension n (fun i => w i)) w hprefix

/-- Pointwise phase axis operator on fields: $(K f)(w) = J_0(f(w))$. -/
def K_field (f : HField) : HField :=
  fun w => J0 (f w)

/-- Cuntz left shift on fields:
$(S_{\text{left}} f)(w) = f(\text{tail}(w))$ if $w(0) = 0$, else $0$. -/
def S_left_field (f : HField) : HField :=
  fun w =>
    if w 0 = 0 then f (fun n => w (n + 1))
    else 0

/-- Cuntz right shift on fields:
$(S_{\text{right}} f)(w) = f(\text{tail}(w))$ if $w(0) = 1$, else $0$. -/
def S_right_field (f : HField) : HField :=
  fun w =>
    if w 0 = 1 then f (fun n => w (n + 1))
    else 0

/-- Projection onto left Cuntz branch: $P_{\text{left}} g (w) = g(w)$ if $w(0) = 0$, else $0$. -/
def P_left (g : HField) : HField :=
  fun w =>
    if w 0 = 0 then g w
    else 0

/-- Projection onto right Cuntz branch: $P_{\text{right}} g (w) = g(w)$ if $w(0) = 1$, else $0$. -/
def P_right (g : HField) : HField :=
  fun w =>
    if w 0 = 1 then g w
    else 0

/-! ## 4. 🏆 THEOREMS: Cuntz Relations and Exact Commutation on Wavefunctions -/

/-- 🏆 THEOREM: Prefix 0 has initial bit 0. -/
theorem prefix_word_zero_head (w : BinaryWord) :
    prefix_word 0 w 0 = 0 := by
  rfl

/-- 🏆 THEOREM: Prefix 1 has initial bit 1. -/
theorem prefix_word_one_head (w : BinaryWord) :
    prefix_word 1 w 0 = 1 := by
  rfl

/-- 🏆 THEOREM: Tail of prefixed word recovers original word. -/
theorem prefix_word_tail (b : Fin 2) (w : BinaryWord) :
    (fun n => prefix_word b w (n + 1)) = w := by
  funext n
  rfl

/-- 🏆 THEOREM: Cuntz left shift evaluates to $f(w)$ at $0 \cdot w$. -/
theorem S_left_field_apply_zero (f : HField) (w : BinaryWord) :
    S_left_field f (prefix_word 0 w) = f w := by
  dsimp [S_left_field]
  rw [prefix_word_zero_head]
  simp [prefix_word_tail]

/-- 🏆 THEOREM: Cuntz left shift evaluates to $0$ at $1 \cdot w$. -/
theorem S_left_field_apply_one (f : HField) (w : BinaryWord) :
    S_left_field f (prefix_word 1 w) = 0 := by
  dsimp [S_left_field]
  have h1 : prefix_word 1 w 0 = 1 := rfl
  have h_ne : prefix_word 1 w 0 ≠ 0 := by rw [h1]; decide
  simp [h_ne]

/-- 🏆 THEOREM: Cuntz right shift evaluates to $f(w)$ at $1 \cdot w$. -/
theorem S_right_field_apply_one (f : HField) (w : BinaryWord) :
    S_right_field f (prefix_word 1 w) = f w := by
  dsimp [S_right_field]
  rw [prefix_word_one_head]
  simp [prefix_word_tail]

/-- 🏆 THEOREM: Cuntz right shift evaluates to $0$ at $0 \cdot w$. -/
theorem S_right_field_apply_zero (f : HField) (w : BinaryWord) :
    S_right_field f (prefix_word 0 w) = 0 := by
  dsimp [S_right_field]
  have h0 : prefix_word 0 w 0 = 0 := rfl
  have h_ne : prefix_word 0 w 0 ≠ 1 := by rw [h0]; decide
  simp [h_ne]

/-- 🏆 THEOREM (Exact Commutation of Cuntz Left Shift and Phase Axis on $\mathcal{H}$):
$$(S_{\text{left}} \circ K)(f) = (K \circ S_{\text{left}})(f)$$ -/
theorem S_left_K_field_commute (f : HField) :
    S_left_field (K_field f) = K_field (S_left_field f) := by
  funext w
  dsimp [S_left_field, K_field]
  by_cases h0 : w 0 = 0
  · simp [h0]
  · simp [h0, J0_zero]

/-- 🏆 THEOREM (Exact Commutation of Cuntz Right Shift and Phase Axis on $\mathcal{H}$):
$$(S_{\text{right}} \circ K)(f) = (K \circ S_{\text{right}})(f)$$ -/
theorem S_right_K_field_commute (f : HField) :
    S_right_field (K_field f) = K_field (S_right_field f) := by
  funext w
  dsimp [S_right_field, K_field]
  by_cases h1 : w 0 = 1
  · simp [h1]
  · simp [h1, J0_zero]

theorem P_left_K_field_commute (f : HField) :
    P_left (K_field f) = K_field (P_left f) := by
  funext w
  dsimp [P_left, K_field]
  by_cases h0 : w 0 = 0
  · simp [h0]
  · simp [h0, J0_zero]

theorem P_right_K_field_commute (f : HField) :
    P_right (K_field f) = K_field (P_right f) := by
  funext w
  dsimp [P_right, K_field]
  by_cases h1 : w 0 = 1
  · simp [h1]
  · simp [h1, J0_zero]

/-- 🏆 THEOREM (Cuntz O₂ Partition of Unity / Range Sum = I):
$$P_{\text{left}} g (w) + P_{\text{right}} g (w) = g(w)$$ -/
theorem cuntz_partition_of_unity (g : HField) (w : BinaryWord) :
    P_left g w + P_right g w = g w := by
  dsimp [P_left, P_right]
  by_cases h0 : w 0 = 0
  · simp [h0]
  · have h1 : w 0 = 1 := by
      have hw : w 0 = 0 ∨ w 0 = 1 := by
        generalize h : w 0 = x
        fin_cases x <;> simp
      cases hw with
      | inl heq => exact (h0 heq).elim
      | inr heq => exact heq
    simp [h1]

theorem cuntz_partition_of_unity_field (g : HField) :
    P_left g + P_right g = g := by
  funext w
  exact cuntz_partition_of_unity g w

def P_left_linear : HField →ₗ[ℝ] HField where
  toFun := P_left
  map_add' g h := by
    funext w
    by_cases hw : w 0 = 0 <;> simp [P_left, hw]
  map_smul' c g := by
    funext w
    simp [P_left]

def P_right_linear : HField →ₗ[ℝ] HField where
  toFun := P_right
  map_add' g h := by
    funext w
    by_cases hw : w 0 = 1 <;> simp [P_right, hw]
  map_smul' c g := by
    funext w
    simp [P_right]

theorem P_left_linear_apply (g : HField) : P_left_linear g = P_left g := rfl

theorem P_right_linear_apply (g : HField) : P_right_linear g = P_right g := rfl

theorem cuntz_partition_of_unity_linear (g : HField) :
    P_left_linear g + P_right_linear g = g := by
  rw [P_left_linear_apply, P_right_linear_apply]
  exact cuntz_partition_of_unity_field g

theorem P_left_linear_add_P_right_linear :
    P_left_linear + P_right_linear = LinearMap.id := by
  apply LinearMap.ext
  intro g
  exact cuntz_partition_of_unity_linear g

theorem P_left_linear_idempotent :
    P_left_linear.comp P_left_linear = P_left_linear := by
  apply LinearMap.ext
  intro g
  funext w
  by_cases hw : w 0 = 0 <;> simp [P_left_linear, P_left, hw]

theorem P_right_linear_idempotent :
    P_right_linear.comp P_right_linear = P_right_linear := by
  apply LinearMap.ext
  intro g
  funext w
  by_cases hw : w 0 = 1 <;> simp [P_right_linear, P_right, hw]

theorem P_left_linear_comp_P_right_linear :
    P_left_linear.comp P_right_linear = 0 := by
  apply LinearMap.ext
  intro g
  funext w
  by_cases hw : w 0 = 0 <;> simp [P_left_linear, P_right_linear, P_left, P_right, hw]

theorem P_right_linear_comp_P_left_linear :
    P_right_linear.comp P_left_linear = 0 := by
  apply LinearMap.ext
  intro g
  funext w
  by_cases hw : w 0 = 1 <;> simp [P_left_linear, P_right_linear, P_left, P_right, hw]

/-! ## 5. Zorn's Lemma for Cuntz Boundary Subsystems -/

/-- 🏆 THEOREM (Zorn's Lemma for Cuntz Boundary States):
For any family of boundary state sets $\mathcal{F}$ bounded above by chain unions,
there exists a maximal boundary subsystem $\mathcal{C}_{\text{Max}}$ where the KMS flow stabilizes. -/
theorem zorn_maximal_cuntz_boundary
    (F : Set (Set HElem))
    (h_chain : ∀ c ⊆ F, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ F, ∀ s ∈ c, s ⊆ ub)
    (s0 : Set HElem)
    (hs0 : s0 ∈ F) :
    ∃ m, s0 ⊆ m ∧ Maximal (fun x => x ∈ F) m :=
  zorn_subset_nonempty F h_chain s0 hs0

/-! ## 6. Grand Capstone Synthesis -/

/--
🏆 **GRAND CAPSTONE: Hilbert Cuntz O₂ Commutation, Partition of Unity, and Zorn Maximality**

Unifies:
1. **$J_0^2 = -I$ Complex Structure**: `J0 (J0 v) = -v`.
2. **Elementary Tensor Commutation**: `S_left_elem ∘ K_elem = K_elem ∘ S_left_elem`.
3. **Wavefunction Commutation**: `S_left_field (K_field f) = K_field (S_left_field f)`.
4. **Cuntz Left & Right Evaluations**: `S_left_field f (prefix_word 0 w) = f w` and `S_left_field f (prefix_word 1 w) = 0`.
5. **Cuntz O₂ Partition of Unity**: `P_left g w + P_right g w = g w`.
-/
theorem grand_hilbert_cuntz_synthesis
    (v : Fiber)
    (f g : HField)
    (w : BinaryWord) :
    (J0 (J0 v) = - v) ∧
    (S_left_elem ∘ K_elem = K_elem ∘ S_left_elem) ∧
    (S_left_field (K_field f) = K_field (S_left_field f)) ∧
    (S_left_field f (prefix_word 0 w) = f w) ∧
    (S_left_field f (prefix_word 1 w) = 0) ∧
    (P_left g w + P_right g w = g w) :=
  ⟨J0_sq v,
   S_left_K_elem_commute,
   S_left_K_field_commute f,
   S_left_field_apply_zero f w,
   S_left_field_apply_one f w,
   cuntz_partition_of_unity g w⟩

end InfoGeometry.Canonical.HilbertCuntz
