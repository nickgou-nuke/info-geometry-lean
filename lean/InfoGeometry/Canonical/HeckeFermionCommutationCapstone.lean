/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.HeckeFermionCommutation

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.HeckeFermionCommutation

/-- 🏆 GRAND CANONICAL CAPSTONE: Hecke-Fermion Commutation Superalgebra -/
theorem grand_canonical_hecke_fermion_synthesis
    (p q n : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h_pq : p ≠ q) (h_pn : Nat.Coprime p n) (h_qn : Nat.Coprime q n)
    (h_pq_coprime : Nat.Coprime (p * q) n) :
    (ArithmeticFunction.moebius (p * n) = - ArithmeticFunction.moebius n) ∧
    (ArithmeticFunction.moebius (p * n) + ArithmeticFunction.moebius n = 0) ∧
    (ArithmeticFunction.moebius (p * q * n) = ArithmeticFunction.moebius n) :=
  grand_hecke_fermion_synthesis p q n hp hq h_pq h_pn h_qn h_pq_coprime

end InfoGeometry.Canonical
