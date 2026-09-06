import proofs.KleinErlangenGrothendieckBridge

/-!
# Groebner / local L-factor / motivic holography finite checks

This file records finite computations used by adjacent geometry files:

* the cardinality of a 32-element normal-form type;
* equality with `Config3PoincareSignature`;
* the D=4 point count at `p=3`;
* the degree-one denominator `1 - #X(F_p) T` at `p=3`;
* a finite string reduction step with a checked length decrease.
-/

noncomputable section

namespace MotivicHolographyGroebnerLFunction

open PenroseSpinTilingConfig
open PenroseSpinIncidenceTessellation
open NonIsoConf3QuadricD4PointCount
open KleinErlangenGrothendieckBridge

/-- A finite normal-form bitmask: three phase choices and two flux choices. -/
structure NormalForm32 where
  phase : Fin 3 → Bool
  flux : Fin 2 → Bool
  deriving DecidableEq, Fintype, Repr

/-- The normal-form alphabet has exactly `32` elements. -/
theorem normalForm32_card : Fintype.card NormalForm32 = 32 := by
  rw [show Fintype.card NormalForm32 = Fintype.card ((Fin 3 → Bool) × (Fin 2 → Bool)) from ?_]
  · simp [Fintype.card_prod]
  · exact Fintype.card_congr
      { toFun := fun b => (b.phase, b.flux)
        invFun := fun p => ⟨p.1, p.2⟩
        left_inv := by
          intro b
          cases b
          rfl
        right_inv := by
          intro p
          cases p
          rfl }

/-- It agrees with the previous `Config3PoincareSignature` finite signature. -/
theorem normalForm32_matches_config_signature :
    Fintype.card NormalForm32 = Fintype.card Config3PoincareSignature := by
  rw [normalForm32_card, PenroseSpinTilingConfig.config3_signature_total_rank]

/-- First-order local zeta denominator `1 - #X(F_p) T` from the finite count. -/
def localZetaDenominator1 (p : ℕ) (T : ℤ) : ℤ :=
  1 - (countPolynomial p : ℤ) * T

/-- The D=4 point count at `p=3` gives the denominator `1 - 1296 T`. -/
theorem localZetaDenominator1_p3 (T : ℤ) :
    localZetaDenominator1 3 T = 1 - 1296 * T := by
  unfold localZetaDenominator1
  rw [countPolynomial_at_three]
  norm_num

/-- The `p=3` arithmetic count used by the incidence layer. -/
theorem arithmetic_fingerprint_p3 : countPolynomial 3 = 1296 := by
  simpa using countPolynomial_at_three

/-- One explicit reduction step used only as a finite string relation. -/
inductive FiniteStringReduction : String → String → Prop where
  | alphaArnold :
      FiniteStringReduction
        "alpha12*alpha23 - alpha12*alpha13 + alpha23*alpha13"
        "0"

/-- Every step in `FiniteStringReduction` strictly reduces string length. -/
theorem finiteStringReduction_length_decreases {redex normal : String}
    (h : FiniteStringReduction redex normal) : normal.length < redex.length := by
  cases h
  decide

/-- The alpha Arnold string reduces to `0` in the finite relation. -/
theorem alphaArnoldReduction :
    FiniteStringReduction
      "alpha12*alpha23 - alpha12*alpha13 + alpha23*alpha13"
      "0" :=
  FiniteStringReduction.alphaArnold

/-- The alpha Arnold finite reduction strictly reduces string length. -/
theorem alphaArnoldReduction_length_decreases :
    String.length "0" <
      String.length "alpha12*alpha23 - alpha12*alpha13 + alpha23*alpha13" :=
  finiteStringReduction_length_decreases alphaArnoldReduction

end MotivicHolographyGroebnerLFunction

end noncomputable section
