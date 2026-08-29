/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.FermionFockMoebius

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.FermionFockMoebius ArithmeticFunction Complex

/-- 🏆 GRAND CANONICAL CAPSTONE: Fermionic Fock Space Möbius Synthesis -/
theorem grand_canonical_fermionic_moebius_fock_synthesis
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 2 ≤ k) (s : ℂ) :
    (moebius 1 = 1) ∧
    (moebius p = -1) ∧
    (moebius (p ^ k) = 0) ∧
    ((1 : ℂ) * (p : ℂ) ^ (0 : ℂ) + (-1 : ℂ) * (p : ℂ) ^ (-s) =
     primeFermionicFactor p s) :=
  grand_fermionic_moebius_fock_synthesis p hp k hk s

end InfoGeometry.Canonical
