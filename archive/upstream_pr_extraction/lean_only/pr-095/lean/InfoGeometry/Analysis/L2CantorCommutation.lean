import Mathlib.Tactic
open Real

noncomputable section

/-!
# Concrete Cuntz O₂ / Phase-Axis Commutation on the Cantor Function Carrier

**What:** Native real-linear maps for the concrete Cantor function carrier and
their phase-axis commutation and Cuntz relations.

**How:** We construct the concrete function carrier

    H = (ℕ → BinarySector) → (ℝ × ℝ)

and prove S_left, S_right, and K = J₀ satisfy:

1. **Commutation**: S_left ∘ K = K ∘ S_left, S_right ∘ K = K ∘ S_right
2. **Cuntz O₂ relations**: star(S_left)·S_left = I, star(S_right)·S_right = I,
   star(S_left)·S_right = 0, S_left·star(S_left) + S_right·star(S_right) = I

This owner does not assert a Hilbert-space completion or self-adjointness.
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

theorem S_left_map_add (ψ φ : H) :
    S_left (ψ + φ) = S_left ψ + S_left φ := by
  funext x
  by_cases h : head x = plus <;> simp [S_left, h]

theorem S_left_map_smul (r : ℝ) (ψ : H) :
    S_left (r • ψ) = r • S_left ψ := by
  funext x
  by_cases h : head x = plus <;> simp [S_left, h]

theorem S_right_map_add (ψ φ : H) :
    S_right (ψ + φ) = S_right ψ + S_right φ := by
  funext x
  by_cases h : head x = minus <;> simp [S_right, h]

theorem S_right_map_smul (r : ℝ) (ψ : H) :
    S_right (r • ψ) = r • S_right ψ := by
  funext x
  by_cases h : head x = minus <;> simp [S_right, h]

theorem star_S_left_map_add (ψ φ : H) :
    star_S_left (ψ + φ) = star_S_left ψ + star_S_left φ := by
  funext x
  simp [star_S_left]

theorem star_S_left_map_smul (r : ℝ) (ψ : H) :
    star_S_left (r • ψ) = r • star_S_left ψ := by
  funext x
  simp [star_S_left]

theorem star_S_right_map_add (ψ φ : H) :
    star_S_right (ψ + φ) = star_S_right ψ + star_S_right φ := by
  funext x
  simp [star_S_right]

theorem star_S_right_map_smul (r : ℝ) (ψ : H) :
    star_S_right (r • ψ) = r • star_S_right ψ := by
  funext x
  simp [star_S_right]

theorem K_op_map_add (ψ φ : H) :
    K_op (ψ + φ) = K_op ψ + K_op φ := by
  funext x
  rcases ψ x with ⟨a, b⟩
  rcases φ x with ⟨c, d⟩
  simp [K_op, J₀]
  ring

theorem K_op_map_smul (r : ℝ) (ψ : H) :
    K_op (r • ψ) = r • K_op ψ := by
  funext x
  rcases ψ x with ⟨a, b⟩
  simp [K_op, J₀]

def S_leftLinear : H →ₗ[ℝ] H where
  toFun := S_left
  map_add' := S_left_map_add
  map_smul' := S_left_map_smul

def S_rightLinear : H →ₗ[ℝ] H where
  toFun := S_right
  map_add' := S_right_map_add
  map_smul' := S_right_map_smul

def star_S_leftLinear : H →ₗ[ℝ] H where
  toFun := star_S_left
  map_add' := star_S_left_map_add
  map_smul' := star_S_left_map_smul

def star_S_rightLinear : H →ₗ[ℝ] H where
  toFun := star_S_right
  map_add' := star_S_right_map_add
  map_smul' := star_S_right_map_smul

def K_opLinear : H →ₗ[ℝ] H where
  toFun := K_op
  map_add' := K_op_map_add
  map_smul' := K_op_map_smul

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

theorem star_S_left_commutes_K :
    star_S_left ∘ K_op = K_op ∘ star_S_left := by
  apply funext; intro ψ; apply funext; intro x
  simp [star_S_left, K_op, J₀_apply', Function.comp_apply]

theorem star_S_right_commutes_K :
    star_S_right ∘ K_op = K_op ∘ star_S_right := by
  apply funext; intro ψ; apply funext; intro x
  simp [star_S_right, K_op, J₀_apply', Function.comp_apply]

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

theorem S_leftLinear_comp_K_opLinear :
    S_leftLinear.comp K_opLinear = K_opLinear.comp S_leftLinear := by
  apply LinearMap.ext
  intro ψ
  funext x
  simpa [S_leftLinear, K_opLinear, Function.comp_apply] using
    congrFun (congrFun S_left_commutes_K ψ) x

theorem S_rightLinear_comp_K_opLinear :
    S_rightLinear.comp K_opLinear = K_opLinear.comp S_rightLinear := by
  apply LinearMap.ext
  intro ψ
  funext x
  simpa [S_rightLinear, K_opLinear, Function.comp_apply] using
    congrFun (congrFun S_right_commutes_K ψ) x

theorem star_S_leftLinear_comp_K_opLinear :
    star_S_leftLinear.comp K_opLinear = K_opLinear.comp star_S_leftLinear := by
  apply LinearMap.ext
  intro ψ
  funext x
  simpa [star_S_leftLinear, K_opLinear, Function.comp_apply] using
    congrFun (congrFun star_S_left_commutes_K ψ) x

theorem star_S_rightLinear_comp_K_opLinear :
    star_S_rightLinear.comp K_opLinear = K_opLinear.comp star_S_rightLinear := by
  apply LinearMap.ext
  intro ψ
  funext x
  simpa [star_S_rightLinear, K_opLinear, Function.comp_apply] using
    congrFun (congrFun star_S_right_commutes_K ψ) x

theorem star_S_leftLinear_comp_S_leftLinear :
    star_S_leftLinear.comp S_leftLinear = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext x
  simpa [star_S_leftLinear, S_leftLinear, Function.comp_apply] using
    congrFun (congrFun star_S_left_comp_S_left ψ) x

theorem star_S_rightLinear_comp_S_rightLinear :
    star_S_rightLinear.comp S_rightLinear = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext x
  simpa [star_S_rightLinear, S_rightLinear, Function.comp_apply] using
    congrFun (congrFun star_S_right_comp_S_right ψ) x

theorem star_S_leftLinear_comp_S_rightLinear :
    star_S_leftLinear.comp S_rightLinear = 0 := by
  apply LinearMap.ext
  intro ψ
  funext x
  simpa [star_S_leftLinear, S_rightLinear, Function.comp_apply] using
    congrFun (congrFun star_S_left_comp_S_right ψ) x

theorem star_S_rightLinear_comp_S_leftLinear :
    star_S_rightLinear.comp S_leftLinear = 0 := by
  apply LinearMap.ext
  intro ψ
  funext x
  simpa [star_S_rightLinear, S_leftLinear, Function.comp_apply] using
    congrFun (congrFun star_S_right_comp_S_left ψ) x

theorem K_opLinear_comp_K_opLinear :
    K_opLinear.comp K_opLinear = -LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext x
  simpa [K_opLinear, Function.comp_apply] using
    congrFun (congrFun K_op_sq ψ) x

theorem S_leftLinear_comp_star_S_leftLinear_add_S_rightLinear_comp_star_S_rightLinear :
    S_leftLinear.comp star_S_leftLinear +
        S_rightLinear.comp star_S_rightLinear = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext x
  simpa [S_leftLinear, star_S_leftLinear, S_rightLinear, star_S_rightLinear,
    Function.comp_apply, Pi.add_apply] using
    congrFun (congrFun S_left_star_S_left_add_S_right_star_S_right ψ) x

end InfoGeometry.Analysis.L2CantorCommutation
