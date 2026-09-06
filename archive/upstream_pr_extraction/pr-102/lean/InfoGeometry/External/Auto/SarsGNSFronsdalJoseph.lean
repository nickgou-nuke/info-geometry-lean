import Mathlib.Tactic

noncomputable section

namespace SarsGNSFronsdalJoseph

abbrev RPhase1 := ℚ × ℚ

def sigma1 (u v : RPhase1) : ℚ := u.1 * v.2 - u.2 * v.1

def normSq1 (u : RPhase1) : ℚ := u.1 * u.1 + u.2 * u.2

def fockExponentQuarter (u : RPhase1) : ℚ := - normSq1 u / 4

theorem sigma1_skew : ∀ u v : RPhase1, sigma1 v u = - sigma1 u v := by
  intro u v
  unfold sigma1
  ring

theorem normSq1_zero : normSq1 (0,0) = 0 := by
  norm_num [normSq1]

theorem fockExponent_zero : fockExponentQuarter (0,0) = 0 := by
  norm_num [fockExponentQuarter, normSq1]

theorem normSq1_nonneg (u : RPhase1) :
    0 ≤ normSq1 u := by
  unfold normSq1
  exact add_nonneg (mul_self_nonneg u.1) (mul_self_nonneg u.2)

theorem fockExponentQuarter_nonpos (u : RPhase1) :
    fockExponentQuarter u ≤ 0 := by
  unfold fockExponentQuarter
  have hnorm : 0 ≤ normSq1 u := normSq1_nonneg u
  linarith

abbrev FronsdalRankOneOrbit := (Fin 2 → ℚ) × (Fin 2 → ℚ)

namespace FronsdalRankOneOrbit

abbrev p (x : FronsdalRankOneOrbit) : Fin 2 → ℚ := x.1
abbrev q (x : FronsdalRankOneOrbit) : Fin 2 → ℚ := x.2

end FronsdalRankOneOrbit

def U (x : FronsdalRankOneOrbit) (a b : Fin 2) : ℚ := x.p a * x.q b

def josephMinor (x : FronsdalRankOneOrbit) : ℚ :=
  U x 0 0 * U x 1 1 - U x 0 1 * U x 1 0

theorem rank_one_joseph_minor_zero (x : FronsdalRankOneOrbit) :
    josephMinor x = 0 := by
  unfold josephMinor U
  simp only [FronsdalRankOneOrbit.p, FronsdalRankOneOrbit.q]
  ring

def quadraticEmbeddingTrace2 (x : FronsdalRankOneOrbit) : ℚ := U x 0 0 + U x 1 1

def starProductCorrection (hbar eta : ℚ) : ℚ := - hbar * hbar * eta

def fronsdalQuadraticRelation (hbar eta lhs : ℚ) : Prop :=
  lhs = starProductCorrection hbar eta

theorem fronsdal_relation_refl (hbar eta : ℚ) :
    fronsdalQuadraticRelation hbar eta (starProductCorrection hbar eta) := by
  rfl

def rankOneJosephRelation : FronsdalRankOneOrbit → ℚ := josephMinor

theorem rankOneJosephRelation_zero (x : FronsdalRankOneOrbit) :
    rankOneJosephRelation x = 0 :=
  rank_one_joseph_minor_zero x

end SarsGNSFronsdalJoseph

end noncomputable section
