import Mathlib
import InfoGeometry.Lie.Pin55KreinConformalBridge

open InfoGeometry.Lie.Pin55KreinConformalBridge

noncomputable section

namespace InfoGeometry.Canonical.ZwegersMockModularBridgeTest

abbrev Vector32 := Fin 32 → ℝ

/-- Krein (16,16) Inner Product on ℝ³² -/
def kreinInner16_16 (x y : Vector32) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun (i : Fin 32) => i.val < 16), x i * y i) -
  (∑ i ∈ Finset.univ.filter (fun (i : Fin 32) => 16 ≤ i.val), x i * y i)

/-- Krein Norm Squared ⟨v, v⟩_{16,16} -/
def kreinNormSq16_16 (v : Vector32) : ℝ :=
  kreinInner16_16 v v

theorem kreinInner16_16_eq_B_krein (x y : Vector32) :
    kreinInner16_16 x y = B_krein_signature x y := rfl

/-- Zwegers Sign Factor E_{c₁, c₂}(v) = (sgn(⟨c₁, v⟩) - sgn(⟨c₂, v⟩)) / 2 -/
def zwegersSignFactor (c1 c2 v : Vector32) : ℝ :=
  (Real.sign (kreinInner16_16 c1 v) - Real.sign (kreinInner16_16 c2 v)) / 2

/-- Theorem: When c₁ = c₂, Zwegers sign factor vanishes identically -/
theorem zwegers_sign_factor_same (c v : Vector32) :
    zwegersSignFactor c c v = 0 := by
  dsimp [zwegersSignFactor]
  ring

theorem abs_sign_le_one (r : ℝ) : |Real.sign r| ≤ 1 := by
  rcases Real.sign_apply r with h | h | h <;> rw [h] <;> norm_num

/-- Theorem: Zwegers sign factor is bounded in absolute value by 1 -/
theorem zwegers_sign_factor_abs_le_one (c1 c2 v : Vector32) :
    |zwegersSignFactor c1 c2 v| ≤ 1 := by
  dsimp [zwegersSignFactor]
  have h1 : |Real.sign (kreinInner16_16 c1 v)| ≤ 1 := abs_sign_le_one _
  have h2 : |Real.sign (kreinInner16_16 c2 v)| ≤ 1 := abs_sign_le_one _
  have h_sub : |Real.sign (kreinInner16_16 c1 v) - Real.sign (kreinInner16_16 c2 v)| ≤ 2 := by
    calc |Real.sign (kreinInner16_16 c1 v) - Real.sign (kreinInner16_16 c2 v)|
      _ ≤ |Real.sign (kreinInner16_16 c1 v)| + |-Real.sign (kreinInner16_16 c2 v)| := abs_add _ _
      _ = |Real.sign (kreinInner16_16 c1 v)| + |Real.sign (kreinInner16_16 c2 v)| := by rw [abs_neg]
      _ ≤ 1 + 1 := by linarith [h1, h2]
      _ = 2 := by norm_num
  rw [abs_div, abs_two]
  linarith

/-- Appell-Lerch Non-Holomorphic Shadow Structure over (16,16) Krein Space -/
structure ZwegersIndefiniteThetaPacket where
  kreinForm : Vector32 → Vector32 → ℝ
  h_krein_eq : ∀ x y, kreinForm x y = B_krein_signature x y
  signFactor : Vector32 → Vector32 → Vector32 → ℝ
  h_same_zero : ∀ c v, signFactor c c v = 0
  h_bounded : ∀ c1 c2 v, |signFactor c1 c2 v| ≤ 1

theorem zwegers_indefinite_theta_packet_exists :
    Nonempty ZwegersIndefiniteThetaPacket :=
  ⟨⟨kreinInner16_16, kreinInner16_16_eq_B_krein, zwegersSignFactor, zwegers_sign_factor_same, zwegers_sign_factor_abs_le_one⟩⟩

end InfoGeometry.Canonical.ZwegersMockModularBridgeTest
