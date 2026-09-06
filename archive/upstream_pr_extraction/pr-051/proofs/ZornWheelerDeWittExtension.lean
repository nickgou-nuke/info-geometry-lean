import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import proofs.SplitQuaternionWheelerDeWitt
import proofs.SplitQuaternionWheelerDeWitt

open MvPolynomial Matrix

namespace ZornWheelerDeWittExtension

abbrev ZornWavePolynomial := MvPolynomial (Fin 8) ℝ
abbrev SplitWavePolynomial := MvPolynomial (Fin 4) ℝ

noncomputable def zornDeterminantPolynomial : ZornWavePolynomial :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - (MvPolynomial.X 2 * MvPolynomial.X 5 + MvPolynomial.X 3 * MvPolynomial.X 6 + MvPolynomial.X 4 * MvPolynomial.X 7)

noncomputable def zornBox (ψ : ZornWavePolynomial) : ZornWavePolynomial :=
  MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 ψ) -
  MvPolynomial.pderiv 2 (MvPolynomial.pderiv 5 ψ) -
  MvPolynomial.pderiv 3 (MvPolynomial.pderiv 6 ψ) -
  MvPolynomial.pderiv 4 (MvPolynomial.pderiv 7 ψ)

noncomputable def zornWheelerDeWittOperator (massSq : ℝ) (ψ : ZornWavePolynomial) : ZornWavePolynomial :=
  -zornBox ψ + MvPolynomial.C massSq * ψ

def IsZornWheelerDeWittSolution (massSq : ℝ) (ψ : ZornWavePolynomial) : Prop :=
  zornWheelerDeWittOperator massSq ψ = 0

noncomputable def embedToZorn : Fin 8 → SplitWavePolynomial
  | 0 => MvPolynomial.X 0 + MvPolynomial.X 2
  | 1 => MvPolynomial.X 0 - MvPolynomial.X 2
  | 2 => MvPolynomial.X 1
  | 3 => MvPolynomial.X 3
  | 4 => 0
  | 5 => -MvPolynomial.X 1
  | 6 => MvPolynomial.X 3
  | 7 => 0

noncomputable def zornRestriction : ZornWavePolynomial →ₐ[ℝ] SplitWavePolynomial :=
  MvPolynomial.aeval embedToZorn

noncomputable def splitToZorn : Fin 4 → ZornWavePolynomial
  | 0 => (MvPolynomial.X 0 + MvPolynomial.X 1) * MvPolynomial.C (1/2 : ℝ)
  | 1 => (MvPolynomial.X 2 - MvPolynomial.X 5) * MvPolynomial.C (1/2 : ℝ)
  | 2 => (MvPolynomial.X 0 - MvPolynomial.X 1) * MvPolynomial.C (1/2 : ℝ)
  | 3 => (MvPolynomial.X 3 + MvPolynomial.X 6) * MvPolynomial.C (1/2 : ℝ)

noncomputable def zornPullback : SplitWavePolynomial →ₐ[ℝ] ZornWavePolynomial :=
  MvPolynomial.aeval splitToZorn

theorem zornDeterminant_restricts_to_deWittQuadratic :
    zornRestriction zornDeterminantPolynomial = SplitQuaternionWheelerDeWitt.deWittQuadratic := by
  unfold zornRestriction zornDeterminantPolynomial SplitQuaternionWheelerDeWitt.deWittQuadratic
  simp only [map_sub, map_mul, map_add, MvPolynomial.aeval_X, embedToZorn]
  ring

lemma zornPullback_C (c : ℝ) : zornPullback (MvPolynomial.C c) = MvPolynomial.C c := AlgHom.commutes _ _
lemma zornPullback_X (k : Fin 4) : zornPullback (MvPolynomial.X k) = splitToZorn k := MvPolynomial.aeval_X _ _
lemma zornRestriction_C (c : ℝ) : zornRestriction (MvPolynomial.C c) = MvPolynomial.C c := AlgHom.commutes _ _
lemma zornRestriction_X (k : Fin 8) : zornRestriction (MvPolynomial.X k) = embedToZorn k := MvPolynomial.aeval_X _ _

lemma add_self_mul_half (x : SplitWavePolynomial) : (x + x) * MvPolynomial.C (1/2 : ℝ) = x := by
  have h1 : x + x = x * MvPolynomial.C (2 : ℝ) := by
    calc x + x = x * 1 + x * 1 := by rw [mul_one]
      _ = x * (1 + 1) := by rw [← mul_add]
      _ = x * (MvPolynomial.C 1 + MvPolynomial.C 1) := by simp only [map_one]
      _ = x * MvPolynomial.C (1 + 1) := by rw [← map_add]
      _ = x * MvPolynomial.C (2 : ℝ) := by norm_num
  rw [h1, mul_assoc, ← map_mul]
  have h2 : (2 : ℝ) * (1/2) = 1 := by norm_num
  rw [h2, map_one, mul_one]

lemma zornRestriction_zornPullback (P : SplitWavePolynomial) :
    zornRestriction (zornPullback P) = P := by
  induction P using MvPolynomial.induction_on
  case C c => simp [zornRestriction_C, zornPullback_C]
  case add p q hp hq => simp [map_add, hp, hq]
  case mul_X p k hp =>
    have hk : zornRestriction (zornPullback (MvPolynomial.X k)) = MvPolynomial.X k := by
      revert k; intro k; fin_cases k
      · simp only [zornRestriction_X, zornPullback_X, splitToZorn, embedToZorn, map_add, map_sub, map_mul, zornRestriction_C]
        have h : (MvPolynomial.X 0 + MvPolynomial.X 2 + (MvPolynomial.X 0 - MvPolynomial.X 2) : SplitWavePolynomial) = MvPolynomial.X 0 + MvPolynomial.X 0 := by ring
        rw [h, add_self_mul_half]; rfl
      · simp only [zornRestriction_X, zornPullback_X, splitToZorn, embedToZorn, map_add, map_sub, map_mul, zornRestriction_C, map_neg]
        have h : (MvPolynomial.X 1 - -MvPolynomial.X 1 : SplitWavePolynomial) = MvPolynomial.X 1 + MvPolynomial.X 1 := by ring
        rw [h, add_self_mul_half]; rfl
      · simp only [zornRestriction_X, zornPullback_X, splitToZorn, embedToZorn, map_add, map_sub, map_mul, zornRestriction_C]
        have h : (MvPolynomial.X 0 + MvPolynomial.X 2 - (MvPolynomial.X 0 - MvPolynomial.X 2) : SplitWavePolynomial) = MvPolynomial.X 2 + MvPolynomial.X 2 := by ring
        rw [h, add_self_mul_half]; rfl
      · simp only [zornRestriction_X, zornPullback_X, splitToZorn, embedToZorn, map_add, map_sub, map_mul, zornRestriction_C]
        have h : (MvPolynomial.X 3 + MvPolynomial.X 3 : SplitWavePolynomial) = MvPolynomial.X 3 + MvPolynomial.X 3 := by ring
        rw [h, add_self_mul_half]; rfl
    simp [map_mul, hp, hk]

lemma pullback_pderiv_0 (Φ : SplitWavePolynomial) : MvPolynomial.pderiv 0 (zornPullback Φ) = MvPolynomial.C (1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 0 Φ + MvPolynomial.pderiv 2 Φ) := by
  induction Φ using MvPolynomial.induction_on
  case C c => simp [zornPullback_C, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
  case add p q hp hq => simp [map_add, mul_add, hp, hq]; ring
  case mul_X p k hp =>
    have hX : MvPolynomial.pderiv 0 (zornPullback (MvPolynomial.X k)) = MvPolynomial.C (1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 0 (MvPolynomial.X k) + MvPolynomial.pderiv 2 (MvPolynomial.X k)) := by revert k; intro k; fin_cases k <;> simp [zornPullback_X, splitToZorn, map_add, map_sub, map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single, Function.update, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
    simp [map_add, map_mul, hp, hX, mul_add, MvPolynomial.pderiv_mul]; ring

lemma pullback_pderiv_1 (Φ : SplitWavePolynomial) : MvPolynomial.pderiv 1 (zornPullback Φ) = MvPolynomial.C (1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 0 Φ - MvPolynomial.pderiv 2 Φ) := by
  induction Φ using MvPolynomial.induction_on
  case C c => simp [zornPullback_C, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
  case add p q hp hq => simp [map_add, map_sub, mul_add, mul_sub, hp, hq]; ring
  case mul_X p k hp =>
    have hX : MvPolynomial.pderiv 1 (zornPullback (MvPolynomial.X k)) = MvPolynomial.C (1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 0 (MvPolynomial.X k) - MvPolynomial.pderiv 2 (MvPolynomial.X k)) := by revert k; intro k; fin_cases k <;> simp [zornPullback_X, splitToZorn, map_add, map_sub, map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single, Function.update, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
    simp [map_add, map_sub, map_mul, hp, hX, mul_add, mul_sub, MvPolynomial.pderiv_mul]; ring

lemma pullback_pderiv_2 (Φ : SplitWavePolynomial) : MvPolynomial.pderiv 2 (zornPullback Φ) = MvPolynomial.C (1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 1 Φ) := by
  induction Φ using MvPolynomial.induction_on
  case C c => simp [zornPullback_C, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
  case add p q hp hq => simp [map_add, mul_add, hp, hq]
  case mul_X p k hp =>
    have hX : MvPolynomial.pderiv 2 (zornPullback (MvPolynomial.X k)) = MvPolynomial.C (1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 1 (MvPolynomial.X k)) := by revert k; intro k; fin_cases k <;> simp [zornPullback_X, splitToZorn, map_add, map_sub, map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single, Function.update, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
    simp [map_add, map_mul, hp, hX, mul_add, MvPolynomial.pderiv_mul]; ring

lemma pullback_pderiv_3 (Φ : SplitWavePolynomial) : MvPolynomial.pderiv 3 (zornPullback Φ) = MvPolynomial.C (1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 3 Φ) := by
  induction Φ using MvPolynomial.induction_on
  case C c => simp [zornPullback_C, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
  case add p q hp hq => simp [map_add, mul_add, hp, hq]
  case mul_X p k hp =>
    have hX : MvPolynomial.pderiv 3 (zornPullback (MvPolynomial.X k)) = MvPolynomial.C (1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 3 (MvPolynomial.X k)) := by revert k; intro k; fin_cases k <;> simp [zornPullback_X, splitToZorn, map_add, map_sub, map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single, Function.update, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
    simp [map_add, map_mul, hp, hX, mul_add, MvPolynomial.pderiv_mul]; ring

lemma pullback_pderiv_4 (Φ : SplitWavePolynomial) : MvPolynomial.pderiv 4 (zornPullback Φ) = 0 := by
  induction Φ using MvPolynomial.induction_on
  case C c => simp [zornPullback_C, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
  case add p q hp hq => simp [map_add, hp, hq]
  case mul_X p k hp =>
    have hX : MvPolynomial.pderiv 4 (zornPullback (MvPolynomial.X k)) = 0 := by revert k; intro k; fin_cases k <;> simp [zornPullback_X, splitToZorn, map_add, map_sub, map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single, Function.update, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
    simp [map_add, map_mul, hp, hX]

lemma pullback_pderiv_5 (Φ : SplitWavePolynomial) : MvPolynomial.pderiv 5 (zornPullback Φ) = MvPolynomial.C (-1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 1 Φ) := by
  induction Φ using MvPolynomial.induction_on
  case C c => simp [zornPullback_C, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
  case add p q hp hq => simp [map_add, mul_add, hp, hq]
  case mul_X p k hp =>
    have hX : MvPolynomial.pderiv 5 (zornPullback (MvPolynomial.X k)) = MvPolynomial.C (-1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 1 (MvPolynomial.X k)) := by revert k; intro k; fin_cases k <;> simp [zornPullback_X, splitToZorn, map_add, map_sub, map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single, Function.update, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
    simp [map_add, map_mul, hp, hX, mul_add, MvPolynomial.pderiv_mul]; ring

lemma pullback_pderiv_6 (Φ : SplitWavePolynomial) : MvPolynomial.pderiv 6 (zornPullback Φ) = MvPolynomial.C (1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 3 Φ) := by
  induction Φ using MvPolynomial.induction_on
  case C c => simp [zornPullback_C, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
  case add p q hp hq => simp [map_add, mul_add, hp, hq]
  case mul_X p k hp =>
    have hX : MvPolynomial.pderiv 6 (zornPullback (MvPolynomial.X k)) = MvPolynomial.C (1/2 : ℝ) * zornPullback (MvPolynomial.pderiv 3 (MvPolynomial.X k)) := by revert k; intro k; fin_cases k <;> simp [zornPullback_X, splitToZorn, map_add, map_sub, map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single, Function.update, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
    simp [map_add, map_mul, hp, hX, mul_add, MvPolynomial.pderiv_mul]; ring

lemma pullback_pderiv_7 (Φ : SplitWavePolynomial) : MvPolynomial.pderiv 7 (zornPullback Φ) = 0 := by
  induction Φ using MvPolynomial.induction_on
  case C c => simp [zornPullback_C, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
  case add p q hp hq => simp [map_add, hp, hq]
  case mul_X p k hp =>
    have hX : MvPolynomial.pderiv 7 (zornPullback (MvPolynomial.X k)) = 0 := by revert k; intro k; fin_cases k <;> simp [zornPullback_X, splitToZorn, map_add, map_sub, map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single, Function.update, MvPolynomial.pderiv_C] <;> try { rw [← map_neg]; congr 1; norm_num }
    simp [map_add, map_mul, hp, hX]

lemma pderiv_comm_split (i j : Fin 4) (ψ : SplitWavePolynomial) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j ψ) = MvPolynomial.pderiv j (MvPolynomial.pderiv i ψ) := by
  exact SplitQuaternionWheelerDeWitt.pderiv_comm i j ψ

theorem zornBox_restricts_to_deWittBox (Φ : SplitWavePolynomial) :
    zornRestriction (zornBox (zornPullback Φ)) = MvPolynomial.C (1/4 : ℝ) * SplitQuaternionWheelerDeWitt.deWittBox Φ := by
  unfold zornBox SplitQuaternionWheelerDeWitt.deWittBox SplitQuaternionWheelerDeWitt.secondDerivative SplitQuaternionWheelerDeWitt.pderiv
  rw [pullback_pderiv_1, pullback_pderiv_5, pullback_pderiv_6, pullback_pderiv_7]
  have h1 : MvPolynomial.pderiv 0 (MvPolynomial.C (1 / 2 : ℝ) * zornPullback (MvPolynomial.pderiv 0 Φ - MvPolynomial.pderiv 2 Φ)) =
    MvPolynomial.C (1 / 4 : ℝ) * zornPullback (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 Φ - MvPolynomial.pderiv 2 Φ) + MvPolynomial.pderiv 2 (MvPolynomial.pderiv 0 Φ - MvPolynomial.pderiv 2 Φ)) := by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add, pullback_pderiv_0, ← mul_assoc]
    have hn : (MvPolynomial.C (1/2 : ℝ) : ZornWavePolynomial) * MvPolynomial.C (1/2 : ℝ) = MvPolynomial.C (1/4 : ℝ) := by
      rw [← map_mul]
      norm_num
    rw [hn]
  rw [h1]
  have h2 : MvPolynomial.pderiv 2 (MvPolynomial.C (-1 / 2 : ℝ) * zornPullback (MvPolynomial.pderiv 1 Φ)) =
    MvPolynomial.C (-1 / 4 : ℝ) * zornPullback (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 Φ)) := by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add, pullback_pderiv_2, ← mul_assoc]
    have hn : (MvPolynomial.C (-1/2 : ℝ) : ZornWavePolynomial) * MvPolynomial.C (1/2 : ℝ) = MvPolynomial.C (-1/4 : ℝ) := by
      rw [← map_mul]
      norm_num
    rw [hn]
  rw [h2]
  have h3 : MvPolynomial.pderiv 3 (MvPolynomial.C (1 / 2 : ℝ) * zornPullback (MvPolynomial.pderiv 3 Φ)) =
    MvPolynomial.C (1 / 4 : ℝ) * zornPullback (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 Φ)) := by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add, pullback_pderiv_3, ← mul_assoc]
    have hn : (MvPolynomial.C (1/2 : ℝ) : ZornWavePolynomial) * MvPolynomial.C (1/2 : ℝ) = MvPolynomial.C (1/4 : ℝ) := by
      rw [← map_mul]
      norm_num
    rw [hn]
  rw [h3]
  have h4 : MvPolynomial.pderiv 4 (0 : ZornWavePolynomial) = 0 := map_zero (MvPolynomial.pderiv 4)
  rw [h4, map_sub, map_sub, map_sub]
  simp only [map_mul, map_add, map_sub, zornRestriction_zornPullback, map_zero, zornRestriction_C]
  rw [pderiv_comm_split 2 0]
  have h_neg : (MvPolynomial.C (-1 / 4 : ℝ) : SplitWavePolynomial) = - MvPolynomial.C (1 / 4 : ℝ) := by
    rw [← map_neg]
    congr 1
    norm_num
  rw [h_neg]
  ring

theorem zornWheelerDeWitt_restricts
    (m : ℝ) (Φ : SplitWavePolynomial) :
    MvPolynomial.C (4 : ℝ) * zornRestriction (zornWheelerDeWittOperator (m^2) (zornPullback Φ)) =
      SplitQuaternionWheelerDeWitt.freeWheelerDeWitt (2 * m) Φ := by
  unfold zornWheelerDeWittOperator SplitQuaternionWheelerDeWitt.freeWheelerDeWitt
  rw [map_add, map_neg, zornBox_restricts_to_deWittBox]
  rw [map_mul, zornRestriction_C, zornRestriction_zornPullback]
  have h1 : MvPolynomial.C (4 : ℝ) * (- (MvPolynomial.C (1 / 4 : ℝ) * SplitQuaternionWheelerDeWitt.deWittBox Φ) + MvPolynomial.C (m ^ 2) * Φ) =
    - SplitQuaternionWheelerDeWitt.deWittBox Φ + MvPolynomial.C (4 : ℝ) * MvPolynomial.C (m ^ 2) * Φ := by
    rw [mul_add, mul_neg, ← mul_assoc, ← map_mul]
    have hn : (4 : ℝ) * (1 / 4) = 1 := by norm_num
    rw [hn, map_one, one_mul, mul_assoc]
  rw [h1]
  have h2 : MvPolynomial.C (4 : ℝ) * MvPolynomial.C (m ^ 2) = (MvPolynomial.C ((2 * m) ^ 2) : SplitWavePolynomial) := by
    rw [← map_mul]; congr 1; ring
  rw [h2]

theorem IsZornWheelerDeWittSolution_restricts
    {m : ℝ} {Φ : SplitWavePolynomial}
    (hΦ : IsZornWheelerDeWittSolution (m^2) (zornPullback Φ)) :
    SplitQuaternionWheelerDeWitt.IsWheelerDeWittSolution (2 * m) Φ := by
  unfold IsZornWheelerDeWittSolution at hΦ
  unfold SplitQuaternionWheelerDeWitt.IsWheelerDeWittSolution
  have h1 := congr_arg zornRestriction hΦ
  rw [map_zero] at h1
  have h2 := zornWheelerDeWitt_restricts m Φ
  have h3 : MvPolynomial.C (4 : ℝ) * zornRestriction (zornWheelerDeWittOperator (m ^ 2) (zornPullback Φ)) = 0 := by
    rw [h1, mul_zero]
  rw [h3] at h2
  exact h2.symm

end ZornWheelerDeWittExtension