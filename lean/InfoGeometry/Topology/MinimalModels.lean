import Mathlib.Data.Rat.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
structure KacTableEntry (p q : ℕ) where
  r : ℕ
  s : ℕ
  r_pos : 1 ≤ r
  s_pos : 1 ≤ s
  r_lt_p : r < p
  s_lt_q : s < q

end InfoGeometry.Topology
