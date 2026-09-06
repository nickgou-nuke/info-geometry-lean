import Mathlib.GroupTheory.SemidirectProduct
import InfoGeometry.OperatorAlgebra.SplitOctonionF2SectorExchange

noncomputable section

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

private theorem zmodTwo_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hzlt : z.val < 2 := ZMod.val_lt z
  have hz : z.val = 0 ∨ z.val = 1 := by omega
  rcases hz with hz | hz
  · exact Or.inl ((ZMod.val_eq_zero z).mp hz)
  · exact Or.inr ((ZMod.val_eq_one (by decide) z).mp hz)

def splitOctSectorExchangeAction : Multiplicative (ZMod 2) →* SplitOctF2Aut where
  toFun z := if z.toAdd = 0 then 1 else sectorExchangeF2Aut
  map_one' := by simp
  map_mul' x y := by
    have hx : x = Multiplicative.ofAdd 0 ∨ x = Multiplicative.ofAdd 1 := by
      rcases zmodTwo_cases x.toAdd with hx | hx
      · exact Or.inl (Multiplicative.ext hx)
      · exact Or.inr (Multiplicative.ext hx)
    have hy : y = Multiplicative.ofAdd 0 ∨ y = Multiplicative.ofAdd 1 := by
      rcases zmodTwo_cases y.toAdd with hy | hy
      · exact Or.inl (Multiplicative.ext hy)
      · exact Or.inr (Multiplicative.ext hy)
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · rfl
    · rfl
    · change (if (1 + 1 : ZMod 2) = 0 then 1 else sectorExchangeF2Aut) =
        sectorExchangeF2Aut * sectorExchangeF2Aut
      rw [if_pos (by decide)]
      exact sectorExchangeF2Aut_sq.symm

@[simp] theorem splitOctSectorExchangeAction_zero :
    splitOctSectorExchangeAction (Multiplicative.ofAdd (0 : ZMod 2)) =
      (1 : SplitOctF2Aut) := by
  rfl

@[simp] theorem splitOctSectorExchangeAction_one :
    splitOctSectorExchangeAction (Multiplicative.ofAdd (1 : ZMod 2)) =
      sectorExchangeF2Aut := by
  rfl

/-- The sector exchange acts on the automorphism group by inner conjugation. -/
def splitOctSectorConjugationAction : Multiplicative (ZMod 2) →*
    MulAut SplitOctF2Aut :=
  (MulAut.conj : SplitOctF2Aut →* MulAut SplitOctF2Aut).comp
    splitOctSectorExchangeAction

@[simp] theorem splitOctSectorConjugationAction_one (g : SplitOctF2Aut) :
    splitOctSectorConjugationAction (Multiplicative.ofAdd 1) g =
      sectorExchangeF2Aut * g * sectorExchangeF2Aut⁻¹ := by
  rfl

@[simp] theorem splitOctSectorConjugationAction_one_exchange :
    splitOctSectorConjugationAction (Multiplicative.ofAdd (1 : ZMod 2))
        sectorExchangeF2Aut = sectorExchangeF2Aut := by
  rw [splitOctSectorConjugationAction_one]
  calc
    sectorExchangeF2Aut * sectorExchangeF2Aut * sectorExchangeF2Aut⁻¹ =
        sectorExchangeF2Aut *
          (sectorExchangeF2Aut * sectorExchangeF2Aut⁻¹) := by rw [mul_assoc]
    _ = sectorExchangeF2Aut := by simp

abbrev splitOctAutKleinSemidirect :=
  SemidirectProduct SplitOctF2Aut (Multiplicative (ZMod 2))
    splitOctSectorConjugationAction

def splitOctKleinGlide : splitOctAutKleinSemidirect :=
  SemidirectProduct.inr (Multiplicative.ofAdd 1)

def splitOctKleinTranslation (g : SplitOctF2Aut) : splitOctAutKleinSemidirect :=
  SemidirectProduct.inl g

theorem splitOctKlein_glide_square :
    splitOctKleinGlide ^ 2 = 1 := by
  change (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) :
      splitOctAutKleinSemidirect) ^ 2 = 1
  rw [← (SemidirectProduct.inr : Multiplicative (ZMod 2) →*
    splitOctAutKleinSemidirect).map_pow]
  apply congrArg SemidirectProduct.inr
  rfl

theorem splitOctKlein_glide_conjugates_translation (g : SplitOctF2Aut) :
    splitOctKleinGlide * splitOctKleinTranslation g * splitOctKleinGlide⁻¹ =
      splitOctKleinTranslation
        (splitOctSectorConjugationAction (Multiplicative.ofAdd 1) g) := by
  simpa [splitOctKleinGlide, splitOctKleinTranslation] using
    (SemidirectProduct.inl_aut (φ := splitOctSectorConjugationAction)
      (Multiplicative.ofAdd 1) g).symm

theorem splitOctKlein_glide_conjugates_exchange_translation :
    splitOctKleinGlide * splitOctKleinTranslation sectorExchangeF2Aut *
        splitOctKleinGlide⁻¹ =
      (splitOctKleinTranslation sectorExchangeF2Aut)⁻¹ := by
  rw [splitOctKlein_glide_conjugates_translation]
  rw [show splitOctSectorConjugationAction (Multiplicative.ofAdd 1)
      sectorExchangeF2Aut = sectorExchangeF2Aut⁻¹ by
    simp [splitOctSectorConjugationAction, splitOctSectorExchangeAction,
      sectorExchangeF2Aut_sq]]
  exact (SemidirectProduct.inl :
    SplitOctF2Aut →* splitOctAutKleinSemidirect).map_inv sectorExchangeF2Aut

theorem splitOctKlein_glide_conjugates_translation_of_fixed_self_inverse
    (g : SplitOctF2Aut)
    (hfixed : splitOctSectorConjugationAction (Multiplicative.ofAdd 1) g = g)
    (hinv : g⁻¹ = g) :
    splitOctKleinGlide * splitOctKleinTranslation g *
        splitOctKleinGlide⁻¹ =
      (splitOctKleinTranslation g)⁻¹ := by
  rw [splitOctKlein_glide_conjugates_translation, hfixed]
  symm
  change (SemidirectProduct.inl g : splitOctAutKleinSemidirect)⁻¹ =
    SemidirectProduct.inl g
  rw [← (SemidirectProduct.inl :
    SplitOctF2Aut →* splitOctAutKleinSemidirect).map_inv, hinv]

theorem splitOctKlein_glide_conjugates_translation_of_inverted
    (g : SplitOctF2Aut)
    (hinverted : splitOctSectorConjugationAction
      (Multiplicative.ofAdd 1) g = g⁻¹) :
    splitOctKleinGlide * splitOctKleinTranslation g *
        splitOctKleinGlide⁻¹ =
      (splitOctKleinTranslation g)⁻¹ := by
  rw [splitOctKlein_glide_conjugates_translation, hinverted]
  exact ((SemidirectProduct.inl :
    SplitOctF2Aut →* splitOctAutKleinSemidirect).map_inv g)

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
