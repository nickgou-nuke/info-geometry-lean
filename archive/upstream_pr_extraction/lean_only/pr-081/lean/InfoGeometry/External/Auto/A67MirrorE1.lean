import Mathlib

namespace A67MirrorE1

abbrev MirrorPair := ℕ × ℕ × ℕ × ℕ

namespace MirrorPair

abbrev protonRichZ (P : MirrorPair) : ℕ := P.1

abbrev neutronRichZ (P : MirrorPair) : ℕ := P.2.1

abbrev protonRichN (P : MirrorPair) : ℕ := P.2.2.1

abbrev neutronRichN (P : MirrorPair) : ℕ := P.2.2.2

end MirrorPair

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
