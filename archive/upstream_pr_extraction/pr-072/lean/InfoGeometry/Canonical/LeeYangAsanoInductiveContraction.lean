import InfoGeometry.Analysis.MultiaffinePolynomialSlices
import InfoGeometry.Canonical.LeeYangAsanoFullReduction

/-!
# Native multiaffine Asano induction

This module combines the canonical coordinate-slice theorem with the proved
closed/bounded Asano contraction.  Separately-affine witnesses and the abstract
Asano-Ruelle source-claim parameter do not occur in the resulting theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoInductiveContraction

open MvPolynomial
open InfoGeometry.Analysis.MultiaffinePolynomialSlices
open InfoGeometry.Canonical.LeeYangAsanoDigest
open InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoInduction
open InfoGeometry.Canonical.LeeYangAsanoNativeCore

/--
One repeated Asano contraction step for a multiaffine polynomial, using the
native closed/bounded topological theorem.
-/
theorem asanoInductiveStep_closed_bounded
    {n : ℕ}
    (P : MvPolynomial (Fin 2 ⊕ Fin n) ℂ)
    (hmulti : ∀ m ∈ P.support, ∀ i, (m i : ℕ) ≤ 1)
    (K : Fin 2 ⊕ Fin n → Set ℂ)
    (hzero : ∀ i, 0 ∉ K i)
    (hclosed₀ : IsClosed (K (Sum.inl 0)))
    (hclosed₁ : IsClosed (K (Sum.inl 1)))
    (hbdd :
      Bornology.IsBounded (K (Sum.inl 0)) ∨
        Bornology.IsBounded (K (Sum.inl 1)))
    (hfree :
      ∀ z : Fin 2 ⊕ Fin n → ℂ,
        (∀ i, z i ∉ K i) → eval z P ≠ 0)
    (w : Fin n → ℂ)
    (hw : ∀ j, w j ∉ K (Sum.inr j))
    (z : ℂ)
    (hz :
      z ∉ asanoForbiddenSet
        (K (Sum.inl 0)) (K (Sum.inl 1))) :
    (toTwoVar P w).contract z ≠ 0 := by
  have h₀ :
      ∀ y : ℂ, ∃ a b : ℂ, ∀ x : ℂ,
        splitEval P x y w = a + b * x := by
    intro y
    let g : Fin 2 ⊕ Fin n → ℂ := fun i =>
      match i with
      | Sum.inl i => Fin.cases 0 (fun _ => y) i
      | Sum.inr j => w j
    rcases eval_update_affine P hmulti (Sum.inl 0) g with ⟨a, b, hab⟩
    exact ⟨a, b, fun x => by
      rw [← hab x]
      unfold splitEval
      apply congrArg (fun h : Fin 2 ⊕ Fin n → ℂ => MvPolynomial.eval h P)
      funext i
      rcases i with i | j
      · fin_cases i
        · simp [g]
        · change y = y
          rfl
      · simp [g]⟩
  have h₁ :
      ∀ x : ℂ, ∃ a b : ℂ, ∀ y : ℂ,
        splitEval P x y w = a + b * y := by
    intro x
    let g : Fin 2 ⊕ Fin n → ℂ := fun i =>
      match i with
      | Sum.inl i => Fin.cases x (fun _ => 0) i
      | Sum.inr j => w j
    rcases eval_update_affine P hmulti (Sum.inl 1) g with ⟨a, b, hab⟩
    exact ⟨a, b, fun y => by
      rw [← hab y]
      unfold splitEval
      apply congrArg (fun h : Fin 2 ⊕ Fin n → ℂ => MvPolynomial.eval h P)
      funext i
      rcases i with i | j
      · fin_cases i <;> simp [g]
      · simp [g]⟩
  apply asano_contraction_full_of_topological_combined
    (K₁ := K (Sum.inl 0)) (K₂ := K (Sum.inl 1))
    (A := (toTwoVar P w).A) (B := (toTwoVar P w).B)
    (C := (toTwoVar P w).C) (D := (toTwoVar P w).D)
    (z := z)
    (hzero (Sum.inl 0)) (hzero (Sum.inl 1))
    hclosed₀ hclosed₁ hbdd
  · intro z₀ z₁ hz₀ hz₁
    have heval : (toTwoVar P w).eval z₀ z₁ ≠ 0 := by
      rw [toTwoVar_eval_eq_of_separatelyAffine P w h₀ h₁]
      apply hfree
      intro i
      cases i with
      | inl i =>
          fin_cases i
          · exact hz₀
          · exact hz₁
      | inr j =>
          exact hw j
    simpa [asanoPhi, TwoVarAffinePolynomial.eval] using heval
  · simpa [negProductSet, asanoForbiddenSet] using hz

end InfoGeometry.Canonical.LeeYangAsanoInductiveContraction
