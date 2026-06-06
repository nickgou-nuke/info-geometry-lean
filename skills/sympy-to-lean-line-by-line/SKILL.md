# Skill: Line-by-Line SymPy → Lean 4 Translation

## Purpose

Translate a SymPy symbolic computation into a Lean 4 formal proof, one assertion at a time, with no `sorry` left behind and every `calc` block building correctly before moving on.

## Workflow

### 0. Prerequisites

Before starting, read both:
- The SymPy file completely
- The existing Lean file (if any) to understand namespace, axioms, and conventions

### 1. Identify the next un-translated SymPy assertion

Read the SymPy file sequentially. Find the next `assert` statement that has no corresponding Lean theorem.

Example:
```python
# SymPy
F = Matrix([[τ, s], [s, -τ]])
F2 = apply_rels(F * F)
assert F2 == eye(2)
```

### 2. Write one Lean theorem — no more

Write exactly one theorem, mimicking the SymPy assertion exactly.

```lean4
theorem F_sq : F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ...
```

### 3. Test the theorem in isolation FIRST

Create a temporary test file with the minimal context needed:

```lean4
import Mathlib
open Matrix

axiom τ : ℂ
axiom tau_sq_add_tau : τ ^ 2 + τ = 1
axiom s : ℂ
axiom s_sq_eq_tau : s ^ 2 = τ

def F : Matrix (Fin 2) (Fin 2) ℂ := !![τ, s; s, -τ]

-- Write the proof with no sorry
theorem F_sq : F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ...
```

Build with:
```bash
lake env lean /tmp/test.lean
```

### 4. Fix ONE error at a time

When the build fails, read the FIRST error only. Fix it, rebuild, repeat.

Common errors and fixes:

| Error | Likely cause | Fix |
|---|---|---|
| `ring_nf made no progress` | `ring` doesn't work on matrices (non-commutative) | Use `simp [Matrix.mul_assoc]` |
| `linarith` / `nlinarith` failed | `linarith` doesn't work on ℂ | Use `ring` + `rw` with explicit relations |
| `calc` syntax error (`unexpected token ':='`) | `calc` each step must be `_ = expr := by proof` on its own line | Never use `;` inside `calc`; each step on a new line |
| `simp` made no progress | Missing lemma or type mismatch | Inspect the goal with `set_option pp.all true` |
| `Variable X is not a proposition` | `simp` can't use a `def` as a rewrite rule | Use `unfold X` or `rw [show X = ... from rfl]` |
| `typeclass instance problem is stuck` (HSMul) | Scalar type not inferred | Add type annotation: `(τ : ℂ) • H` |
| `ring` works but `pi` is a constant | `ring` treats `Real.pi` as a constant, not a polynomial variable | Use `ring_nf` or `field_simp` + `ring` |
| `zpow_add` requires nonzero proof | `zpow_add` needs `a ≠ 0` | Provide `hq_ne_zero : q ≠ 0 := Complex.exp_ne_zero _` |
| `q⁻⁴` syntax error | `⁻` after `^` | Use `(q⁻¹)^4` or `q ^ (-4 : ℤ)` |

### 5. Build the theorem inside the project

Append the theorem to the real file, then build the specific module:

```bash
lake build InfoGeometry.Canonical.YangBaxterProof
```

### 6. Only then move to the next SymPy assertion

Do NOT write multiple theorems in one edit. Do NOT fix multiple errors at once.

## Key Rules

### ℂ is a CommRing, but `ring` has limits

- `ring` works on ℂ for polynomial expressions without `Real.pi`
- `ring` does NOT work on matrices (use `simp [Matrix.mul_assoc]`)
- `linarith` / `nlinarith` do NOT work on ℂ
- `norm_num` works on ℂ for concrete numeral arithmetic

### `calc` block formatting

Correct:
```lean4
calc
  τ ^ 2 = (τ ^ 2 + τ) - τ := by ring
  _ = 1 - τ := by rw [tau_sq_add_tau]
```

Incorrect (never use `;`):
```lean4
calc τ ^ 2 = (τ ^ 2 + τ) - τ := by ring; _ = 1 - τ := by rw [tau_sq_add_tau]
```

### SymPy symbols → Lean axioms or noncomputable defs

- SymPy symbols with relations → `axiom` + `axiom` for their defining equations
- SymPy concrete definitions (e.g., `q = exp(iπ/5)`) → `noncomputable def`
- SymPy `subs(τ², 1-τ)` → `rw [tau_sq_eq_one_minus_tau]`

### The F-matrix entry pattern

For 2×2 matrix assertions, use `ext i j; fin_cases i <;> fin_cases j` then handle each entry:

```lean4
theorem F_sq : F * F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]
    calc τ * τ + s * s = τ ^ 2 + s ^ 2 := by ring; _ = 1 := tau_sq_add_s_sq
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]
    calc s * s + τ * τ = s ^ 2 + τ ^ 2 := by ring; _ = τ ^ 2 + s ^ 2 := add_comm _ _; _ = 1 := tau_sq_add_s_sq
```

For 3×3 matrix assertions, use `Fin.sum_univ_three` instead.

## Complete Example

### SymPy
```python
τ, s, q = sp.symbols('τ s q')
F = Matrix([[τ, s], [s, -τ]])
F2 = apply_rels(F * F)
assert F2 == eye(2)
```

### Lean (one theorem, one build cycle)
```lean4
axiom τ : ℂ
axiom tau_sq_add_tau : τ ^ 2 + τ = 1
axiom s : ℂ
axiom s_sq_eq_tau : s ^ 2 = τ

theorem tau_sq_add_s_sq : τ ^ 2 + s ^ 2 = 1 := by
  calc τ ^ 2 + s ^ 2 = τ ^ 2 + τ := by rw [s_sq_eq_tau]; _ = 1 := tau_sq_add_tau

def F : Matrix (Fin 2) (Fin 2) ℂ := !![τ, s; s, -τ]

theorem F_sq : F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]
    calc τ * τ + s * s = τ ^ 2 + s ^ 2 := by ring; _ = 1 := tau_sq_add_s_sq
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]
    calc s * s + τ * τ = s ^ 2 + τ ^ 2 := by ring; _ = τ ^ 2 + s ^ 2 := add_comm _ _; _ = 1 := tau_sq_add_s_sq
```

## Anti-patterns

- ❌ Writing multiple theorems before building
- ❌ Using `linarith` on ℂ
- ❌ Using `ring` on matrices
- ❌ Using `calc ... := by ring; ... :=` on one line
- ❌ Leaving `sorry` in a theorem
- ❌ Adding imports to `All.lean` before the module builds
- ❌ Using ℝ constants when working in ℂ (causes typeclass issues with `HSMul`)
