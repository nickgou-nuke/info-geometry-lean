import proofs.TitsBruhatBrillouinKlein
import proofs.TwoSheetThreeColorWeyl

/-!
# Klein-bottle glide and the sixfold cyclotomic family fibre

This owner combines two independently checked actions without identifying their
carriers.  The affine factor is the standard Klein glide `F`, with `F² = Tx`.
The internal factor is the six-state sheet/family carrier.  Its reflection
reverses the order-three family cycle, while sheet parity times that cycle is
the order-six cyclotomic lift.

No quotient topology, neutrino phenomenology, or analytic Tomita theory is
claimed here.
-/

noncomputable section

namespace KleinBottleSixfoldCyclotomic

open TwoSheetThreeColorWeyl

abbrev AffineFrame := TitsBruhatBrillouinKlein.M3Q
abbrev InternalOperator := M6C
abbrev TotalState := AffineFrame × InternalOperator

/-- The internal family cycle `I₂ ⊗ X`. -/
def familyCycle : InternalOperator := tensor (1 : M2C) colorShift

/-- Sheet exchange combined with reversal of the family triangle. -/
def internalGlide : InternalOperator := tensor sheetFlip colorReflection

/-- The lifted sheet parity. -/
def internalParity : InternalOperator := tensor sheetGamma (1 : M3C)

/-- The affine Klein glide acts on the base and the internal glide acts on the fibre. -/
def totalGlide (S : TotalState) : TotalState :=
  (TitsBruhatBrillouinKlein.F * S.1, internalGlide * S.2)

/-- One full longitudinal translation; the internal fibre has closed after two glides. -/
def totalLongTranslation (S : TotalState) : TotalState :=
  (TitsBruhatBrillouinKlein.Tx * S.1, S.2)

theorem familyCycle_cube (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    familyCycle ^ 3 = (1 : InternalOperator) := by
  have hX : colorShift ^ 3 = (1 : M3C) := (color_weyl ω hω).1
  calc
    familyCycle ^ 3 = tensor ((1 : M2C) ^ 3) (colorShift ^ 3) := by
      simp [familyCycle, pow_succ, tensor_mul, Matrix.mul_assoc]
    _ = (1 : InternalOperator) := by rw [hX]; simp

/-- Internal monodromy is an involution and reverses the `C₃` generator. -/
theorem internal_klein_relations (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    internalGlide * internalGlide = (1 : InternalOperator) ∧
    internalGlide * familyCycle * internalGlide = familyCycle ^ 2 := by
  rcases orientation_reversing_relations ω hω with ⟨hG, hGX, _⟩
  constructor
  · exact hG
  · calc
      internalGlide * familyCycle * internalGlide =
          tensor (1 : M2C) (colorShift ^ 2) := hGX
      _ = familyCycle ^ 2 := by
        symm
        simp [familyCycle, pow_two, tensor_mul]

/-- The square of the total glide is the full base translation.  This is the
associated-fibre form of the ordinary Klein-bottle glide relation. -/
theorem totalGlide_sq (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (S : TotalState) :
    totalGlide (totalGlide S) = totalLongTranslation S := by
  rcases internal_klein_relations ω hω with ⟨hG, _⟩
  apply Prod.ext
  · dsimp [totalGlide, totalLongTranslation]
    rw [← Matrix.mul_assoc, TitsBruhatBrillouinKlein.F_sq_eq_Tx]
  · dsimp [totalGlide, totalLongTranslation]
    rw [← Matrix.mul_assoc, hG, Matrix.one_mul]

/-- The internal inversion is the finite image of the Klein relation
`b a b⁻¹ = a⁻¹`: because `X³=1`, its inverse is represented by `X²`. -/
theorem familyCycle_inverse_certificate (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    familyCycle * familyCycle ^ 2 = (1 : InternalOperator) ∧
    internalGlide * familyCycle * internalGlide = familyCycle ^ 2 := by
  constructor
  · simpa [pow_succ, pow_two, Matrix.mul_assoc] using familyCycle_cube ω hω
  · exact (internal_klein_relations ω hω).2

/-- Two operators commute after passage to a quotient that identifies the
central scalar signs `I` and `-I`.  This is only the relation needed for the
`V₄` shadow; it is not itself a constructed quotient group. -/
def CommuteModuloSign (A B : InternalOperator) : Prop :=
  A * B = B * A ∨ A * B = -(B * A)

theorem sheetFlip_parity_anticommute :
    tensor sheetFlip (1 : M3C) * internalParity =
      -(internalParity * tensor sheetFlip (1 : M3C)) := by
  have hSheet : sheetFlip * sheetGamma = -(sheetGamma * sheetFlip) := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sheetFlip, sheetGamma, sheetPlus, sheetMinus,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [internalParity, tensor_mul, tensor_mul, hSheet]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [tensor, Matrix.kroneckerMap_apply]

/-- The sheet reflection and parity therefore commute in the central-sign
projective quotient, giving the precise relation behind the proposed `V₄` shadow. -/
theorem sheet_V4_projective_shadow :
    CommuteModuloSign (tensor sheetFlip (1 : M3C)) internalParity := by
  exact Or.inr sheetFlip_parity_anticommute

/-- Complete reconciliation packet: ordinary affine glide, internal family
inversion, sixfold cyclotomic lift, and projective sheet `V₄` relation. -/
theorem klein_sixfold_reconciliation (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    TitsBruhatBrillouinKlein.F * TitsBruhatBrillouinKlein.F =
        TitsBruhatBrillouinKlein.Tx ∧
    internalGlide * internalGlide = (1 : InternalOperator) ∧
    internalGlide * familyCycle * internalGlide = familyCycle ^ 2 ∧
    sixfoldTriality ^ 3 = internalParity ∧
    sixfoldTriality ^ 6 = (1 : InternalOperator) ∧
    CommuteModuloSign (tensor sheetFlip (1 : M3C)) internalParity := by
  rcases internal_klein_relations ω hω with ⟨hG, hInv⟩
  exact ⟨TitsBruhatBrillouinKlein.F_sq_eq_Tx, hG, hInv,
    sixfoldTriality_cube ω hω, sixfoldTriality_sixth ω hω,
    sheet_V4_projective_shadow⟩

end KleinBottleSixfoldCyclotomic

end noncomputable section
