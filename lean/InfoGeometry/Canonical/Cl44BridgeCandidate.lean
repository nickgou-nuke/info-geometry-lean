import InfoGeometry.Algebra.F4Derivations
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge

/-!
# Split `Cl(4,4)` bridge exports

This module is an export boundary only.  The former `Candidate` and packet
structures stored unproved algebraic evidence; they did not define or prove a
new mathematical object and had no downstream users.  The actual owners are
imported above:

* `F4Derivations` owns the verified `H3Zorn` Jordan derivation subalgebra;
* `H3ZornJordanInstance` owns the installed Mathlib Jordan structure;
* `SplitCl44TKKJordanLieBridge` owns the split-Clifford/TKK bridge theorems.

No additional proposition or evidence carrier is introduced here.
-/
