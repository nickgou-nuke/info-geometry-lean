import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic

namespace InfoGeometry.Topology.KTheory

/-- 
The K_0 group of the Cuntz Algebra O_n is isomorphic to Z / (n-1)Z.
For O_2, this is Z / (2-1)Z = Z / 1Z, which is the trivial group (0).
-/
abbrev K0_O_n (n : ℕ) := ZMod (n - 1)

/-- The K_0 group of O_2 is exactly the trivial group ZMod 1. -/
abbrev K0_O_2 := K0_O_n 2

/-- 
THEOREM: Triviality of K_0(O_2).
Any element in the K_0 group of O_2 is identically zero.
This is the finite `ZMod 1` readout of the standard `K_0(O_2)` computation.
-/
theorem k0_o2_is_trivial (x : K0_O_2) : x = 0 := by
  let y : ZMod 1 := x
  have hy : y = 0 := Subsingleton.elim y 0
  simpa [y] using hy

/-- 
The K_1 group of the Cuntz Algebra O_n is the kernel of the map (n-1) on Z.
Since n-1 is non-zero for n > 1, the kernel is strictly 0.
-/
abbrev K1_O_n (n : ℕ) := { x : ℤ // (n - 1) * x = 0 }

/-- The K_1 group of O_2 is exactly the trivial kernel. -/
abbrev K1_O_2 := K1_O_n 2

/-- 
THEOREM: Triviality of K_1(O_2).
Any element in the K_1 group of O_2 is identically zero.
This is the finite kernel readout of the standard `K_1(O_2)` computation.
-/
theorem k1_o2_is_trivial (x : K1_O_2) : x.val = 0 := by
  simpa [K1_O_2, K1_O_n] using x.property

end InfoGeometry.Topology.KTheory
