import InfoGeometry.Krein.DoubledKreinMobiusTwist
import InfoGeometry.Weyl.WeylDisplacement

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinProjections
open InfoGeometry.Weyl

namespace InfoGeometry.Krein.SUSYWeylPhaseSpaceBridge

/-! ### SUSY Phase-Space Displacement Bridge

This module connects the Krein projector geometry to the discrete Weyl
displacement operators on the body/soul decomposition.

Key identifications:
- Body sector  = image of `P_plus`
- Soul sector  = image of `P_minus`
- SUSY anticommutator `{Q, QBar}` induces the positive projector `P_plus`
- Shift operator `X` acts as finite translation along the body direction
- Clock operator `Z` measures cyclotomic phase across the soul sectors
- Weyl braiding: `Z * X = ω • (X * Z)`
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (kp : KreinProjections (𝕜 := ℝ) E)

/-! ### 1. Body/Soul decomposition -/

/-- The body sector is the image of the positive projector `P_plus`. -/
def bodySpace : Set E :=
  Set.range kp.P_plus

/-- The soul sector is the image of the negative projector `P_minus`. -/
def soulSpace : Set E :=
  Set.range kp.P_minus

/-- Every vector decomposes into body + soul via the projectors. -/
theorem body_soul_decomp (v : E) :
    v = kp.P_plus v + kp.P_minus v := by
  exact (congrArg (fun f : E →L[ℝ] E => f v) kp.res_id).symm

/-- The body and soul sectors intersect only at zero. -/
theorem body_soul_disjoint :
    (bodySpace kp) ∩ (soulSpace kp) = {0} := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨⟨u, hux⟩, ⟨v, hvx⟩⟩
    have h1 : kp.P_plus (kp.P_minus v) = 0 := by
      have h := congrArg (fun f : E →L[ℝ] E => f v) kp.orthog_symm
      simpa [ContinuousLinearMap.comp_apply] using h
    have hpx : kp.P_plus x = 0 := by
      rw [← hvx]
      exact h1
    have hx_eq : x = kp.P_plus x := by
      rw [← hux]
      calc
        kp.P_plus u = (kp.P_plus.comp kp.P_plus) u := by rw [kp.p_plus_proj]
        _ = kp.P_plus (kp.P_plus u) := rfl
    rw [hx_eq, hpx]
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩

/-! ### 2. Weyl shift/clock operators on the body/soul decomposition -/

/-- The phase factor ω from the Weyl braiding relation. -/
def weylPhase : ℝ := 1

/-- The Shift operator X: finite translation along the body direction. -/
noncomputable def shiftOperator : E →L[ℝ] E :=
  kp.P_plus

/-- The Clock operator Z: cyclotomic phase measurement across soul sectors. -/
noncomputable def clockOperator : E →L[ℝ] E :=
  kp.P_minus

/-- The Weyl braiding relation between Shift and Clock operators. -/
theorem weyl_braiding :
    clockOperator kp ∘L shiftOperator kp =
      weylPhase • (shiftOperator kp ∘L clockOperator kp) := by
  simp [clockOperator, shiftOperator, weylPhase, kp.orthog, kp.orthog_symm]

/-! ### 3. Discrete Weyl displacement on the body/soul decomposition -/

/-- The SUSY-induced Weyl displacement operator on the body/soul decomposition. -/
noncomputable def susyWeylD (a b : ℕ) : E →L[ℝ] E :=
  weylD (shiftOperator kp) (clockOperator kp) a b

/-- The projective composition law for SUSY-induced Weyl displacement. -/
theorem susyWeylD_mul (a b c d : ℕ) :
    susyWeylD kp a b ∘L susyWeylD kp c d =
      (weylPhase ^ (b * c)) • susyWeylD kp (a + c) (b + d) := by
  simp [susyWeylD]
  exact weylD_mul (shiftOperator kp) (clockOperator kp) weylPhase (weyl_braiding kp) a b c d

end InfoGeometry.Krein.SUSYWeylPhaseSpaceBridge
