import Mathlib.Tactic
import InfoGeometry.Physics.ChiralCausalCone

/-!
# Temperley–Lieb Chain — indexed 3-site TL relations

Explicit 8×8 matrix verification of the TL₂(2) chain relations.

**Closed:**
- `e4² = 2·e4` — the 4×4 Kronecker image (proved)
- `e0² = 2·e0`, `e1² = 2·e1` — 3-site idempotency (proved)

**Next:**
- TL_n(2) full chain, Jones braid, Yang–Baxter
-/

noncomputable section

namespace InfoGeometry.External.Auto.TLChain

open Matrix

/-! ## 4×4 Kronecker image of the chiral TL generator -/

def e4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
    0, 1, 1, 0;
    0, 1, 1, 0;
    0, 0, 0, 0]

theorem e4_sq : e4 * e4 = (2 : ℂ) • e4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e4, Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply] <;> norm_num

/-! ## 3-site chain: explicit 8×8 matrices

`e0` acts on slots (0,1), identity on slot 2.
`e1` acts on slots (1,2), identity on slot 0.

Both are 8×8 matrices indexed by `Fin 8` with the standard basis order:
row/col 0..7 = (0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)
in the Kronecker `Fin 4 × Fin 2` decomposition.
-/

/-- e₀ = e4 ⊗ₖ I₂ — acts on slots (0,1). -/
def e0 : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0]

/-- e₁ = I₂ ⊗ₖ e4 — acts on slots (1,2). -/
def e1 : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0]

/-- TL idempotency for e₀: `e₀² = 2·e₀`. -/
theorem e0_sq : e0 * e0 = (2 : ℂ) • e0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [Matrix.mul_apply, Matrix.smul_apply] <;>
    simp [e0, Fin.sum_univ_eight] <;> norm_num

/-- TL idempotency for e₁: `e₁² = 2·e₁`. -/
theorem e1_sq : e1 * e1 = (2 : ℂ) • e1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [Matrix.mul_apply, Matrix.smul_apply] <;>
    simp [e1, Fin.sum_univ_eight] <;> norm_num

/-- TL skein relation: `e₀·e₁·e₀ = e₀`. -/
theorem e0_mul_e1_mul_e0 : e0 * e1 * e0 = e0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [Matrix.mul_apply] <;>
    simp [e0, e1, Fin.sum_univ_eight]

/-- TL symmetric skein: `e₁·e₀·e₁ = e₁`. -/
theorem e1_mul_e0_mul_e1 : e1 * e0 * e1 = e1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [Matrix.mul_apply] <;>
    simp [e0, e1, Fin.sum_univ_eight]

end InfoGeometry.External.Auto.TLChain
