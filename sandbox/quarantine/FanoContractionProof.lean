import InfoGeometry.Clifford.FanoOctonionParavector

open InfoGeometry.Clifford.FanoOctonionParavector
open InfoGeometry.Clifford.OctonionParavectorBridge

set_option maxHeartbeats 400000

/-! Proving the Fano contraction identity in isolation.

Mirrors the existing, green proof pattern of `fanoCross_self`:
`ext k; fin_cases k; simp [fanoCrossRaw]; ring`. No `Ring`/`NonUnital*`
instance is needed; the identity is a coordinatewise polynomial equality on
`Fin 7 → ℝ` closed by `ring`. The `cons_val_*` helper lemmas are intentionally
omitted — mathlib's `Matrix.cons_val_succ` / `cons_val_zero` (already in the
`simp` set) peel `vecCons` applications. -/

/-- `fanoCross` reduces to its raw coordinate definition. -/
@[simp] theorem fanoCross_apply (u v : R7) : fanoCross u v = fanoCrossRaw u v := rfl

/-- Dot product application. -/
@[simp] theorem dot7_apply (u v : R7) : dot7 u v = ∑ i : Fin 7, u i * v i := rfl

/-- Expansion of a `Fin 7` sum into seven explicit terms. -/
@[simp] theorem sum_univ_seven (f : Fin 7 → ℝ) :
    (∑ i : Fin 7, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp [Fin.sum_univ_succ]
  ring

/-- The Fano contraction identity on `R7`.

```text
u × (v × w) + v × (w × u) + w × (u × v)
  = 2 (u·v) w + 2 (v·w) u + 2 (w·u) v
```
From this, octonion alternativity (`octonion_alt_left` /
`octonion_alt_right`) follows by unwrapping the paravector multiplication. -/
theorem fano_contraction (u v w : R7) :
    fanoCross u (fanoCross v w) + fanoCross v (fanoCross w u) + fanoCross w (fanoCross u v) =
      2 * (dot7 u v) • w + 2 * (dot7 v w) • u + 2 * (dot7 w u) • v := by
  ext k
  fin_cases k <;>
    simp [fanoCross_apply, fanoCrossRaw, dot7_apply, sum_univ_seven] <;>
    ring
