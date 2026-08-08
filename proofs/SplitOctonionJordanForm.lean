import proofs.CanonicalZornRealSpin44

/-!
# Real `(4,4)` form of the full split-octonion Jordan carrier

This file reuses the existing real eight-dimensional carrier and its
isometric embedding into canonical Zorn coordinates.  It owns the normalized
polar form, proves nondegeneracy by coordinate probes, and exhibits explicit
orthogonal four-dimensional positive and negative summands.
-/

noncomputable section

namespace SplitOctonionJordanForm

open CanonicalZornRealSpin44
open CanonicalZornCompositionTriality
open SplitOctonionBraidSU3

abbrev RealJordan := CanonicalZornRealSpin44.RealSplit44
abbrev quadratic44 := CanonicalZornRealSpin44.realQuadratic44

/-- Normalized polarization of the split norm. -/
def normPolar (x y : RealJordan) : ℝ :=
  (quadratic44 (x + y) - quadratic44 x - quadratic44 y) / 2

theorem normPolar_formula (x y : RealJordan) :
    normPolar x y =
      (∑ i, x.1 i * y.1 i) - ∑ i, x.2 i * y.2 i := by
  simp [normPolar, CanonicalZornRealSpin44.realQuadratic44_apply,
    Fin.sum_univ_four]
  ring

theorem normPolar_symmetric (x y : RealJordan) :
    normPolar x y = normPolar y x := by
  rw [normPolar_formula, normPolar_formula]
  apply congrArg₂ (· - ·) <;>
    apply Finset.sum_congr rfl <;> intro i _ <;> ring

def axis4 (k : Fin 4) : Fin 4 → ℝ := fun i => if i = k then 1 else 0

def positiveProbe (k : Fin 4) : RealJordan := (axis4 k, 0)
def negativeProbe (k : Fin 4) : RealJordan := (0, axis4 k)

theorem normPolar_positiveProbe (x : RealJordan) (k : Fin 4) :
    normPolar x (positiveProbe k) = x.1 k := by
  rw [normPolar_formula]
  simp [positiveProbe, axis4]

theorem normPolar_negativeProbe (x : RealJordan) (k : Fin 4) :
    normPolar x (negativeProbe k) = -x.2 k := by
  rw [normPolar_formula]
  simp [negativeProbe, axis4]

/-- The polar form has zero radical. -/
theorem normPolar_nondegenerate (x : RealJordan)
    (h : ∀ y : RealJordan, normPolar x y = 0) : x = 0 := by
  apply Prod.ext
  · funext k
    have hk := h (positiveProbe k)
    rw [normPolar_positiveProbe] at hk
    simpa using hk
  · funext k
    have hk := h (negativeProbe k)
    rw [normPolar_negativeProbe] at hk
    exact neg_eq_zero.mp hk

/-- Canonical positive and negative summand embeddings. -/
def positiveEmbed (p : Fin 4 → ℝ) : RealJordan := (p, 0)
def negativeEmbed (n : Fin 4 → ℝ) : RealJordan := (0, n)

theorem positive_negative_decomposition (x : RealJordan) :
    x = positiveEmbed x.1 + negativeEmbed x.2 := by
  apply Prod.ext <;> funext i <;>
    simp [positiveEmbed, negativeEmbed]

theorem positive_negative_orthogonal (p n : Fin 4 → ℝ) :
    normPolar (positiveEmbed p) (negativeEmbed n) = 0 := by
  simp [normPolar_formula, positiveEmbed, negativeEmbed]

theorem positive_restriction (p : Fin 4 → ℝ) :
    quadratic44 (positiveEmbed p) = ∑ i, p i ^ 2 := by
  simp [positiveEmbed, CanonicalZornRealSpin44.realQuadratic44_apply]

theorem negative_restriction (n : Fin 4 → ℝ) :
    quadratic44 (negativeEmbed n) = -(∑ i, n i ^ 2) := by
  simp [negativeEmbed, CanonicalZornRealSpin44.realQuadratic44_apply]

theorem positive_finrank : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
  simpa using Module.finrank_fin_fun ℝ

theorem negative_finrank : Module.finrank ℝ (Fin 4 → ℝ) = 4 :=
  positive_finrank

/-- The theorem-bearing signature certificate: an orthogonal decomposition
into a positive four-plane and a negative four-plane. -/
theorem normPolar_signature_4_4 :
    (∀ p, quadratic44 (positiveEmbed p) = ∑ i, p i ^ 2) ∧
    (∀ n, quadratic44 (negativeEmbed n) = -(∑ i, n i ^ 2)) ∧
    (∀ p n, normPolar (positiveEmbed p) (negativeEmbed n) = 0) ∧
    Module.finrank ℝ (Fin 4 → ℝ) = 4 ∧
    Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
  exact ⟨positive_restriction, negative_restriction,
    positive_negative_orthogonal, positive_finrank, negative_finrank⟩

/-! ## Compatibility with the existing canonical Zorn real locus -/

def realZorn (x : RealJordan) : Zorn := (realSplit44ToVector8 x).val

theorem realZorn_injective : Function.Injective realZorn := by
  intro x y h
  apply realSplit44ToVector8_injective
  apply ZornCopy.ext
  exact h

theorem realZorn_norm (x : RealJordan) :
    zornNorm (realZorn x) = (quadratic44 x : ℂ) := by
  have h := vectorQuadratic_realSplit44ToVector8 x
  rw [CanonicalZornCliffordRepresentation.vectorQuadratic_apply] at h
  exact h

theorem real_form_synthesis (x : RealJordan) :
    zornNorm (realZorn x) = (quadratic44 x : ℂ) ∧
    (∀ y, (∀ z, normPolar y z = 0) → y = 0) ∧
    x = positiveEmbed x.1 + negativeEmbed x.2 := by
  exact ⟨realZorn_norm x, fun y => normPolar_nondegenerate y,
    positive_negative_decomposition x⟩

end SplitOctonionJordanForm

end noncomputable section
