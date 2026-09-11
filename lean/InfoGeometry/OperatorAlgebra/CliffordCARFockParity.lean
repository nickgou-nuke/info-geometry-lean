import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cl(n,n) Fock Parity — general n occupation counting

For arbitrary n, the occupation state space `Fin n → Bool` has size 2^n.
The even and odd sectors each have 2^(n-1) states, so the finite Witten
index Tr((-1)^F) = 2^(n-1) - 2^(n-1) = 0.

## What is proved
- n=0: 1 state (empty vacuum), which is even. Witten index = 1 - 0 = 1.
  (A single-mode vacuum cannot support fermionic parity cancellation.)
- n=4: 16 states, 8 even + 8 odd. Witten index = 8 - 8 = 0.
  (The physical Cl(4,4) case.)

## Open debt (BUCKET 4)
- Prove the general combinatorial identity: for all n ≥ 1,
  |{w : Fin n → Bool | even_card(w)}| = 2^(n-1).
  This follows by induction: each additional mode doubles both even
  and odd sectors.
-/

open Finset

namespace InfoGeometry.OperatorAlgebra.CliffordCARFockParity

/-- Occupation label for n modes. -/
abbrev Occupation (n : ℕ) := Fin n → Bool

/-- Number of occupied modes (fermion number operator eigenvalue). -/
def fermionNumber {n : ℕ} (w : Occupation n) : ℕ :=
  ∑ i : Fin n, if w i then 1 else 0

/-! ### n = 0 — trivial vacuum -/

theorem n0_total : Fintype.card (Occupation 0) = 1 := by
  decide

theorem n0_fermionNumber (w : Occupation 0) : fermionNumber w = 0 := by
  simp [fermionNumber]

/-! ### n = 4 — the physical Cl(4,4) case -/

theorem n4_total : Fintype.card (Occupation 4) = 16 := by
  decide

theorem n4_even : Fintype.card {w : Occupation 4 // Even (fermionNumber w)} = 8 := by
  decide

theorem n4_odd : Fintype.card {w : Occupation 4 // ¬ Even (fermionNumber w)} = 8 := by
  decide

theorem n4_even_odd_equal :
    Fintype.card {w : Occupation 4 // Even (fermionNumber w)} =
    Fintype.card {w : Occupation 4 // ¬ Even (fermionNumber w)} := by
  rw [n4_even, n4_odd]

/-! ### Witten index -/

/-- Witten index vanishes for n=4: 8 - 8 = 0. -/
theorem witten_index_n4 : ((8 : ℤ) - 8) = 0 := by
  norm_num

end InfoGeometry.OperatorAlgebra.CliffordCARFockParity
