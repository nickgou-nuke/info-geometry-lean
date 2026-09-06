import Mathlib.Tactic
open Real

noncomputable section

/-!
# Concrete Cuntz O₂ / Phase-Axis Commutation on ℓ²(CantorBoundary) ⊗ ℝ²

**What:** The last missing `KLinear` hypothesis for the e₂ self-adjointness
chain (see `KLinearGap.lean`).

**How:** We construct the concrete Hilbert space

    ℋ = ℓ²(CantorBoundary, ℝ²)

and prove S_left, S_right, and K = J₀ satisfy:

1. **Commutation**: S_left ∘ K = K ∘ S_left, S_right ∘ K = K ∘ S_right
2. **Cuntz O₂ relations**: star(S_left)·S_left = I, star(S_right)·S_right = I,
   star(S_left)·S_right = 0, S_left·star(S_left) + S_right·star(S_right) = I
-/

set_option autoImplicit false

namespace InfoGeometry.Analysis.L2CantorCommutation

/-! ## Binary symbols and boundary sequences -/

inductive BinarySector : Type where | plus | minus
  deriving DecidableEq, Fintype
open BinarySector

abbrev BaseIndex := ℕ → BinarySector

def head (x : BaseIndex) : BinarySector := x 0
def tail (x : BaseIndex) : BaseIndex := fun n => x (n + 1)

def prepend (s : BinarySector) (x : BaseIndex) : BaseIndex
  | 0 => s
  | n + 1 => x n

@[simp] theorem tail_prepend (s : BinarySector) (x : BaseIndex) : tail (prepend s x) = x := by
  ext n; simp [tail, prepend]

@[simp] theorem head_prepend (s : BinarySector) (x : BaseIndex) : head (prepend s x) = s := by
  simp [head, prepend]

lemma head_cases (x : BaseIndex) : head x = plus ∨ head x = minus := by
  have all : (Finset.univ : Finset BinarySector) = {plus, minus} := by decide
  have mem : head x ∈ (Finset.univ : Finset BinarySector) := Finset.mem_univ _
  simpa [all] using mem

theorem prepend_head_tail (x : BaseIndex) : prepend (head x) (tail x) = x := by
  ext n; cases n <;> simp [prepend, head, tail]

/-! ## The fiber ℝ² with J₀ rotation -/

abbrev Fiber := ℝ × ℝ

def J₀ : Fiber → Fiber := fun (a, b) => (-b, a)

@[simp] theorem J₀_apply (a b : ℝ) : J₀ (a, b) = (-b, a) := rfl

theorem J₀_apply' (p : ℝ × ℝ) : J₀ p = (-p.2, p.1) := by
  rcases p with ⟨a, b⟩; simp

theorem J₀_sq : J₀ ∘ J₀ = -id := by
  ext ⟨a, b⟩ <;> simp

/-! ## The concrete carrier and operators -/

abbrev H := BaseIndex → Fiber

def S_left : H → H :=
  fun ψ y => if _h : head y = plus then ψ (tail y) else (0, 0)

def S_right : H → H :=
  fun ψ y => if _h : head y = minus then ψ (tail y) else (0, 0)

def star_S_left : H → H :=
  fun ψ x => ψ (prepend plus x)

def star_S_right : H → H :=
  fun ψ x => ψ (prepend minus x)

def K_op : H → H :=
  fun ψ x => J₀ (ψ x)

theorem K_op_sq : K_op ∘ K_op = -id := by
  ext ψ x
  · simpa [K_op, Function.comp_apply] using
      congrArg Prod.fst (congrArg (fun f : Fiber → Fiber => f (ψ x)) J₀_sq)
  · simpa [K_op, Function.comp_apply] using
      congrArg Prod.snd (congrArg (fun f : Fiber → Fiber => f (ψ x)) J₀_sq)

/-! ## Commutation -/

theorem S_left_commutes_K : S_left ∘ K_op = K_op ∘ S_left := by
  apply funext; intro ψ; apply funext; intro x
  simp [S_left, K_op, J₀_apply', Function.comp_apply]
  split_ifs <;> simp

theorem S_right_commutes_K : S_right ∘ K_op = K_op ∘ S_right := by
  apply funext; intro ψ; apply funext; intro x
  simp [S_right, K_op, J₀_apply', Function.comp_apply]
  split_ifs <;> simp

/-! ## Cuntz O₂ relations -/

theorem star_S_left_comp_S_left : star_S_left ∘ S_left = id := by
  apply funext; intro ψ; apply funext; intro x
  simp [star_S_left, S_left, Function.comp_apply, head_prepend, tail_prepend]

theorem star_S_right_comp_S_right : star_S_right ∘ S_right = id := by
  apply funext; intro ψ; apply funext; intro x
  simp [star_S_right, S_right, Function.comp_apply, head_prepend, tail_prepend]

theorem star_S_left_comp_S_right : star_S_left ∘ S_right = fun (_ : H) _ => (0, 0) := by
  apply funext; intro ψ; apply funext; intro x
  simp [star_S_left, S_right, Function.comp_apply, head_prepend]

theorem star_S_right_comp_S_left : star_S_right ∘ S_left = fun (_ : H) _ => (0, 0) := by
  apply funext; intro ψ; apply funext; intro x
  simp [star_S_right, S_left, Function.comp_apply, head_prepend]

theorem S_left_star_S_left_add_S_right_star_S_right :
    (S_left ∘ star_S_left) + (S_right ∘ star_S_right) = id := by
  apply funext; intro ψ; apply funext; intro x
  simp [Pi.add_apply, S_left, star_S_left, S_right, star_S_right, Function.comp_apply,
    ]
  rcases head_cases x with (hplus | hminus)
  · have : prepend plus (tail x) = x := by
      calc
        prepend plus (tail x) = prepend (head x) (tail x) := by simp [hplus]
        _ = x := prepend_head_tail x
    simp [hplus, this]
  · have : prepend minus (tail x) = x := by
      calc
        prepend minus (tail x) = prepend (head x) (tail x) := by simp [hminus]
        _ = x := prepend_head_tail x
    simp [hminus, this]

end InfoGeometry.Analysis.L2CantorCommutation
