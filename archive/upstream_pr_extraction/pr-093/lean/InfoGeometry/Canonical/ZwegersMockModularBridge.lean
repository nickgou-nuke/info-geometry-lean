import Mathlib.Tactic
import InfoGeometry.Lie.Pin55KreinConformalBridge

open InfoGeometry.Lie.Pin55KreinConformalBridge

noncomputable section

namespace InfoGeometry.Canonical.ZwegersMockModularBridge

abbrev Vector32 := Fin 32 → ℝ

/-- Krein (16,16) Inner Product on ℝ³² -/
def kreinInner16_16 (x y : Vector32) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun (i : Fin 32) => i.val < 16), x i * y i) -
  (∑ i ∈ Finset.univ.filter (fun (i : Fin 32) => 16 ≤ i.val), x i * y i)

/-- Krein Norm Squared ⟨v, v⟩_{16,16} -/
def kreinNormSq16_16 (v : Vector32) : ℝ :=
  kreinInner16_16 v v

theorem kreinInner16_16_eq_B_krein (x y : Vector32) :
    kreinInner16_16 x y = B_krein_signature x y := by
  simpa [kreinInner16_16, B_krein_signature]

/-- Three-valued sign of a real number, used in the Zwegers kernel. -/
def zwegersRealSign (r : ℝ) : ℝ :=
  if 0 < r then 1 else if r < 0 then -1 else 0

/-- Zwegers Sign Factor E_{c₁, c₂}(v) = (sgn(⟨c₁, v⟩) - sgn(⟨c₂, v⟩)) / 2 -/
def zwegersSignFactor (c1 c2 v : Vector32) : ℝ :=
  (zwegersRealSign (kreinInner16_16 c1 v) -
    zwegersRealSign (kreinInner16_16 c2 v)) / 2

/-- Theorem: When c₁ = c₂, Zwegers sign factor vanishes identically -/
theorem zwegers_sign_factor_same (c v : Vector32) :
    zwegersSignFactor c c v = 0 := by
  dsimp [zwegersSignFactor]
  ring

theorem abs_sign_le_one (r : ℝ) : |zwegersRealSign r| ≤ 1 := by
  dsimp [zwegersRealSign]
  split_ifs <;> norm_num

/-- Theorem: Zwegers sign factor is bounded in absolute value by 1 -/
theorem zwegers_sign_factor_abs_le_one (c1 c2 v : Vector32) :
    |zwegersSignFactor c1 c2 v| ≤ 1 := by
  dsimp [zwegersSignFactor]
  have h1 : |zwegersRealSign (kreinInner16_16 c1 v)| ≤ 1 := abs_sign_le_one _
  have h2 : |zwegersRealSign (kreinInner16_16 c2 v)| ≤ 1 := abs_sign_le_one _
  rw [abs_div, abs_two]
  linarith [abs_sub (zwegersRealSign (kreinInner16_16 c1 v))
    (zwegersRealSign (kreinInner16_16 c2 v))]

/-- Theorem: Zwegers sign factor is antisymmetric under endpoint swap -/
theorem zwegers_sign_factor_antisymm (c1 c2 v : Vector32) :
    zwegersSignFactor c2 c1 v = -zwegersSignFactor c1 c2 v := by
  dsimp [zwegersSignFactor]
  ring

/-- Theorem: Krein inner product is symmetric -/
theorem kreinInner16_16_symm (x y : Vector32) :
    kreinInner16_16 x y = kreinInner16_16 y x := by
  dsimp [kreinInner16_16]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- Theorem: Krein inner product is linear in the first argument -/
theorem kreinInner16_16_add_left (x1 x2 y : Vector32) :
    kreinInner16_16 (x1 + x2) y = kreinInner16_16 x1 y + kreinInner16_16 x2 y := by
  simp [kreinInner16_16, add_mul, Finset.sum_add_distrib]
  ring

/-- Theorem: Krein inner product scalar multiplication -/
theorem kreinInner16_16_smul_left (a : ℝ) (x y : Vector32) :
    kreinInner16_16 (a • x) y = a * kreinInner16_16 x y := by
  simp [kreinInner16_16, mul_assoc, ← Finset.mul_sum]
  ring

end InfoGeometry.Canonical.ZwegersMockModularBridge
