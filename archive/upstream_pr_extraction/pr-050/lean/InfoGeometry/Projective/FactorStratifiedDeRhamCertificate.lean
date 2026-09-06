import Mathlib.Tactic
import InfoGeometry.Projective.NonIsoConf3RankIngestion

/-!
# Factor-stratified polynomial identities

This owner contains the finite polynomial identities and conditional rank
arithmetic that are available in Lean.  External computer-algebra execution
status is deliberately not encoded as a mathematical structure or theorem.
-/

namespace InfoGeometry.Projective.FactorStratifiedDeRhamCertificate

open InfoGeometry.Projective.NonIsoConf3RankIngestion
open Polynomial

noncomputable def factorBernsteinPoly : ℤ[X] := X ^ 2 + 3 * X + 2

noncomputable def generalBernsteinPoly : ℤ[X] := X ^ 3 + 10 * X ^ 2 + 33 * X + 36

def complementCountPoly (p : ℤ) : ℤ :=
  p ^ 8 - 3 * p ^ 7 + 7 * p ^ 5 - 4 * p ^ 4 - 4 * p ^ 3 + 3 * p ^ 2

theorem factorBernsteinPoly_factorization :
    factorBernsteinPoly = (X + 1) * (X + 2) := by
  simp [factorBernsteinPoly]
  ring

theorem generalBernsteinPoly_factorization :
    generalBernsteinPoly = (X + 3) ^ 2 * (X + 4) := by
  simp [generalBernsteinPoly]
  ring

theorem factorBernsteinPoly_eval_neg_one :
    eval (-1) factorBernsteinPoly = 0 := by
  rw [factorBernsteinPoly_factorization]
  simp

theorem factorBernsteinPoly_eval_neg_two :
    eval (-2) factorBernsteinPoly = 0 := by
  rw [factorBernsteinPoly_factorization]
  simp

theorem generalBernsteinPoly_eval_neg_three :
    eval (-3) generalBernsteinPoly = 0 := by
  rw [generalBernsteinPoly_factorization]
  simp

theorem generalBernsteinPoly_eval_neg_four :
    eval (-4) generalBernsteinPoly = 0 := by
  rw [generalBernsteinPoly_factorization]
  simp

theorem complementCountPoly_factorization (p : ℤ) :
    complementCountPoly p =
      p ^ 2 * (p - 1) ^ 2 * (p + 1) * (p ^ 3 - 2 * p ^ 2 - p + 3) := by
  unfold complementCountPoly
  ring

theorem complementCountPoly_at_three :
    complementCountPoly 3 = 1296 := by
  norm_num [complementCountPoly]

theorem complementCountPoly_at_five :
    complementCountPoly 5 = 175200 := by
  norm_num [complementCountPoly]

theorem complementCountPoly_at_seven :
    complementCountPoly 7 = 3400992 := by
  norm_num [complementCountPoly]

theorem candidateFixture_still_arithmetically_consistent :
    RankDataConsistent candidateLocalBettiData :=
  candidateLocalBettiData_consistent

theorem future_candidateFixture_spinTiled_rank32 :
    candidateLocalBettiData.totalRank * PenroseSpinTiling.spinTilingMultiplicity = 32 :=
  candidateLocalBettiData_spinTiled_rank32

end InfoGeometry.Projective.FactorStratifiedDeRhamCertificate
