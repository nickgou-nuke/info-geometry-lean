import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Defs

namespace InfoGeometry.Topology

/--
The central charge formula for a minimal model M(p, q) in 2D CFT.
For p > q in {2, 3, ...}, the central charge is:
c_{p,q} = 1 - 6 * (p - q)^2 / (pq)
-/
def minimalModelCentralCharge (p q : ℕ) (_hq : 2 ≤ q) (_hpq : q < p) : ℚ :=
  1 - 6 * (((p : ℚ) - (q : ℚ)) ^ 2 / ((p : ℚ) * (q : ℚ)))

/--
A valid entry in the Kac table for a minimal model M(p, q).
The indices (r, s) must be strictly positive and bounded by p-1 and q-1 respectively.
-/
/- A native subtype of the bounded index pair `(r, s)`. -/
abbrev KacTableEntry (p q : ℕ) :=
  {x : ℕ × ℕ //
    1 ≤ x.1 ∧ 1 ≤ x.2 ∧ x.1 < p ∧ x.2 < q}

namespace KacTableEntry

abbrev r {p q : ℕ} (e : KacTableEntry p q) : ℕ := e.1.1
abbrev s {p q : ℕ} (e : KacTableEntry p q) : ℕ := e.1.2
abbrev r_pos {p q : ℕ} (e : KacTableEntry p q) : 1 ≤ e.1.1 := e.2.1
abbrev s_pos {p q : ℕ} (e : KacTableEntry p q) : 1 ≤ e.1.2 := e.2.2.1
abbrev r_lt_p {p q : ℕ} (e : KacTableEntry p q) : e.1.1 < p := e.2.2.2.1
abbrev s_lt_q {p q : ℕ} (e : KacTableEntry p q) : e.1.2 < q := e.2.2.2.2

@[ext (iff := false)] theorem ext {p q : ℕ} {e₁ e₂ : KacTableEntry p q}
    (hr : e₁.r = e₂.r) (hs : e₁.s = e₂.s) : e₁ = e₂ := by
  apply Subtype.ext
  exact Prod.ext hr hs

end KacTableEntry

end InfoGeometry.Topology
