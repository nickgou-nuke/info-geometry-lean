import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import InfoGeometry.Quantum.FermionFockMoebius

namespace InfoGeometry.Canonical.FermionFockMoebiusCapstone

open InfoGeometry.Quantum.FermionFockMoebius ArithmeticFunction

theorem capstone_fermionic_moebius_fock_synthesis
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 2 ≤ k) (s : ℂ) :
    (moebius 1 = 1) ∧
    (moebius p = -1) ∧
    (moebius (p ^ k) = 0) ∧
    ((1 : ℂ) * (1 : ℂ) + (-1 : ℂ) * Complex.cpow (p : ℂ) (-s) =
     primeFermionicFactor p s) :=
  grand_fermionic_moebius_fock_synthesis p hp k hk s

end InfoGeometry.Canonical.FermionFockMoebiusCapstone
