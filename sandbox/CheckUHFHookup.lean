import Mathlib
import InfoGeometry.Capstone.BenamouBrenierBridge
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

set_option synthInstance.maxHeartbeats 1000000

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Capstone.BenamouBrenierBridge
open TrivSqZeroExt Finset

namespace InfoGeometry.Capstone.UHFHookup

def uhfTrivSqZeroExtEmbed (n : ℕ) : TrivSqZeroExt (DiagAlg n) (DiagAlg n) →+* TrivSqZeroExt (DiagAlg (n + 1)) (DiagAlg (n + 1)) where
  toFun x := inl (diagEmbedSucc n x.fst) + inr (diagEmbedSucc n x.snd)
  map_one' := by
    ext
    · simp [diagEmbedSucc_one]
    · simp [diagEmbedSucc_zero]
  map_mul' x y := by
    ext
    · simp [diagEmbedSucc_mul]
    · simp [diagEmbedSucc_mul, diagEmbedSucc_add]
  map_zero' := by
    ext
    · simp [diagEmbedSucc_zero]
    · simp [diagEmbedSucc_zero]
  map_add' x y := by
    ext
    · simp [diagEmbedSucc_add]
    · simp [diagEmbedSucc_add]

lemma uhfTrivSqZeroExtEmbed_inl (n : ℕ) (a : DiagAlg n) :
    uhfTrivSqZeroExtEmbed n (inl a) = inl (diagEmbedSucc n a) := by
  change inl (diagEmbedSucc n a) + inr (diagEmbedSucc n 0) = inl (diagEmbedSucc n a)
  simp [diagEmbedSucc_zero]

lemma uhfTrivSqZeroExtEmbed_inr (n : ℕ) (a : DiagAlg n) :
    uhfTrivSqZeroExtEmbed n (inr a) = inr (diagEmbedSucc n a) := by
  change inl (diagEmbedSucc n 0) + inr (diagEmbedSucc n a) = inr (diagEmbedSucc n a)
  simp [diagEmbedSucc_zero]

lemma diagEmbedSucc_pow (n : ℕ) (A : DiagAlg n) (k : ℕ) :
    diagEmbedSucc n (A ^ k) = diagEmbedSucc n A ^ k := by
  induction k with
  | zero => exact diagEmbedSucc_one n
  | succ k ih =>
    rw [pow_succ, pow_succ, diagEmbedSucc_mul n (A ^ k) A, ih]

theorem uhf_duhamel_naturality (n : ℕ) (A B : DiagAlg n) (k : ℕ) :
    uhfTrivSqZeroExtEmbed n (discreteDuhamelSum A B k) =
    discreteDuhamelSum (diagEmbedSucc n A) (diagEmbedSucc n B) k := by
  simp only [discreteDuhamelSum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_mul, uhfTrivSqZeroExtEmbed_inl, uhfTrivSqZeroExtEmbed_inr, uhfTrivSqZeroExtEmbed_inl]
  rw [diagEmbedSucc_pow, diagEmbedSucc_pow]

end InfoGeometry.Capstone.UHFHookup
