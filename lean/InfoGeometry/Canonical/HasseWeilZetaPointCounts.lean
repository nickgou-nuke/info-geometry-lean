import InfoGeometry.Canonical.KapranovZetaSeries
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Hasse--Weil Point Counts and Zeta Factorization

This file formalizes the finite algebraic point-count layer behind the
additive-to-multiplicative zeta dictionary. It reuses the Cauchy-series owner
from `KapranovZetaSeries` and states formal exponentiation as an explicit
predicate on a raw function, rather than as a proof-carrying structure.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `LogZeta_zero`, `LogZeta_add`, `N_P_zero`, `N_P_step`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES:
  `Zeta_add` and `zeta_projective_decomposition` are conditional on the named
  formal-exponential law `IsFormalExp`.
- BUCKET 3: OPEN CLOSURE DEBT:
  This file does not construct schemes, finite fields, or geometric point-count
  proofs for affine and projective spaces. It proves the algebraic factorization
  once the point-count formulas and formal exponential law are supplied.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.HasseWeilZetaPointCounts

open InfoGeometry.Canonical.KapranovZetaSeries

/-- Point counts over finite-field extensions, represented by extension degree. -/
abbrev PointCount :=
  ℕ → ℚ

/-- The logarithmic zeta series `m ↦ N(m) / m`, with zero constant term. -/
def LogZeta (N : PointCount) : Series ℚ :=
  fun m => if m = 0 then 0 else N m / (m : ℚ)

@[simp]
theorem LogZeta_zero (N : PointCount) :
    LogZeta N 0 = 0 :=
  rfl

/-- The logarithmic zeta construction is additive in point-count sequences. -/
theorem LogZeta_add (N₁ N₂ : PointCount) :
    LogZeta (fun m => N₁ m + N₂ m) =
      fun m => LogZeta N₁ m + LogZeta N₂ m := by
  funext m
  by_cases hm : m = 0
  · subst hm
    simp [LogZeta]
  · simp [LogZeta, hm]
    ring

/-- A raw formal exponential map on rational formal series. -/
abbrev FormalExp :=
  Series ℚ → Series ℚ

/--
The formal exponential law needed for zeta multiplicativity: it maps sums of
zero-constant-term logarithmic series to Cauchy products.
-/
def IsFormalExp (Exp : FormalExp) : Prop :=
  ∀ (A B : Series ℚ), A 0 = 0 → B 0 = 0 →
    Exp (fun n => A n + B n) = Exp A * Exp B

/-- The zeta series obtained by applying a formal exponential to `LogZeta`. -/
def Zeta (N : PointCount) (Exp : FormalExp) : Series ℚ :=
  Exp (LogZeta N)

/--
The additive-to-multiplicative theorem for Hasse--Weil style point-count zeta
series, conditional only on the explicit formal-exponential law.
-/
theorem Zeta_add (N₁ N₂ : PointCount) (Exp : FormalExp) (hExp : IsFormalExp Exp) :
    Zeta (fun m => N₁ m + N₂ m) Exp = Zeta N₁ Exp * Zeta N₂ Exp := by
  unfold Zeta
  rw [LogZeta_add]
  exact hExp (LogZeta N₁) (LogZeta N₂) (LogZeta_zero N₁) (LogZeta_zero N₂)

/-- Point count of affine space `A^k`: `q^(k*m)` over the degree-`m` extension. -/
def N_A (k : ℕ) (q : ℚ) : PointCount :=
  fun m => q ^ (k * m)

/-- Point count of projective space `P^n`: `∑_{k=0}^n q^(k*m)`. -/
def N_P (n : ℕ) (q : ℚ) : PointCount :=
  fun m => Finset.sum (Finset.range (n + 1)) (fun k => q ^ (k * m))

/-- The zero-dimensional projective count is the zero-dimensional affine count. -/
theorem N_P_zero (q : ℚ) :
    N_P 0 q = N_A 0 q := by
  funext m
  simp [N_P, N_A]

/--
The Bruhat-cell count step:
`N_{P^{n+1}} = N_{P^n} + N_{A^{n+1}}`.
-/
theorem N_P_step (n : ℕ) (q : ℚ) :
    N_P (n + 1) q = fun m => N_P n q m + N_A (n + 1) q m := by
  funext m
  simpa [N_P, N_A] using
    Finset.sum_range_succ (fun k : ℕ => q ^ (k * m)) (n + 1)

/-- Recursive finite product of formal series indexed by `0, ..., n`. -/
def seriesProd (f : ℕ → Series ℚ) : ℕ → Series ℚ
  | 0 => f 0
  | n + 1 => seriesProd f n * f (n + 1)

/--
The projective-space zeta series factors into the finite product of affine-cell
zeta series, once the formal exponential satisfies `IsFormalExp`.
-/
theorem zeta_projective_decomposition (n : ℕ) (q : ℚ)
    (Exp : FormalExp) (hExp : IsFormalExp Exp) :
    Zeta (N_P n q) Exp = seriesProd (fun k => Zeta (N_A k q) Exp) n := by
  induction n with
  | zero =>
      rw [N_P_zero]
      rfl
  | succ n ih =>
      rw [N_P_step]
      rw [Zeta_add (N_P n q) (N_A (n + 1) q) Exp hExp]
      rw [ih]
      rfl

end InfoGeometry.Canonical.HasseWeilZetaPointCounts
