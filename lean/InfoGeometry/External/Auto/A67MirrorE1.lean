import Mathlib

namespace A67MirrorE1

structure MirrorPair where
  protonRichZ : ℕ
  neutronRichZ : ℕ
  protonRichN : ℕ
  neutronRichN : ℕ

def mirrorChargesExchange (P : MirrorPair) : Prop :=
  P.protonRichZ = P.neutronRichN ∧ P.neutronRichZ = P.protonRichN

theorem total_charge_eq_of_mirrorChargesExchange {P : MirrorPair}
    (hP : mirrorChargesExchange P) :
    P.protonRichZ + P.neutronRichZ = P.protonRichN + P.neutronRichN := by
  rcases hP with ⟨hZ, hN⟩
  omega

def spinDenominator (twoJi : ℕ) : ℚ := twoJi + 1

def E1PlusBE1 (twoJi : ℕ) (MIV MIS : ℚ) : ℚ :=
  ((MIV + MIS) ^ 2) / spinDenominator twoJi

def E1MinusBE1 (twoJi : ℕ) (MIV MIS : ℚ) : ℚ :=
  ((MIV - MIS) ^ 2) / spinDenominator twoJi

theorem E1PlusBE1_swap_sign (twoJi : ℕ) (MIV MIS : ℚ) :
    E1PlusBE1 twoJi MIV (-MIS) = E1MinusBE1 twoJi MIV MIS := by
  simp only [E1PlusBE1, E1MinusBE1]
  congr 1
  ring

theorem E1MinusBE1_swap_sign (twoJi : ℕ) (MIV MIS : ℚ) :
    E1MinusBE1 twoJi MIV (-MIS) = E1PlusBE1 twoJi MIV MIS := by
  simp only [E1PlusBE1, E1MinusBE1]
  congr 1
  ring

theorem spinDenominator_pos (twoJi : ℕ) :
    0 < spinDenominator twoJi := by
  dsimp [spinDenominator]
  exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg twoJi) zero_lt_one

end A67MirrorE1
