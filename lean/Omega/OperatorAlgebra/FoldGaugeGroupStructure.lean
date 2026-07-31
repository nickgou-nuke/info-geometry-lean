import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- The symmetric group attached to a fold fiber of multiplicity `n`. -/
abbrev FoldGaugeFiberGroup (n : ℕ) := Equiv.Perm (Fin n)

/-- Order of the full fold-gauge group, viewed as a product of symmetric groups over the fibers. -/
def foldGaugeGroupOrder {m : ℕ} (N : Fin m → ℕ) : ℕ :=
  ∏ d, Nat.factorial (N d)

/-- Order of the derived subgroup of `S_n`: trivial for `n ≤ 1`, and `|A_n| = n! / 2`
afterwards. -/
def foldGaugeDerivedComponentOrder (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else Nat.factorial n / 2

/-- Order of the center of `S_n`: only `S₂` contributes a nontrivial center. -/
def foldGaugeCenterComponentOrder (n : ℕ) : ℕ :=
  if n = 2 then 2 else 1

/-- Order of the abelianization of `S_n`: trivial for `n ≤ 1` and `C₂` for `n ≥ 2`. -/
def foldGaugeAbelianizationComponentOrder (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else 2

/-- Componentwise order formula for the derived subgroup of the full fold-gauge group. -/
def foldGaugeDerivedOrder {m : ℕ} (N : Fin m → ℕ) : ℕ :=
  ∏ d, foldGaugeDerivedComponentOrder (N d)

/-- Componentwise order formula for the center of the full fold-gauge group. -/
def foldGaugeCenterOrder {m : ℕ} (N : Fin m → ℕ) : ℕ :=
  ∏ d, foldGaugeCenterComponentOrder (N d)

/-- Componentwise order formula for the abelianization of the full fold-gauge group. -/
def foldGaugeAbelianizationOrder {m : ℕ} (N : Fin m → ℕ) : ℕ :=
  ∏ d, foldGaugeAbelianizationComponentOrder (N d)

end Omega.OperatorAlgebra
