import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.FieldTheory.Separable
import InfoGeometry.Canonical.SixStateSpectralBridge

open scoped Matrix

namespace InfoGeometry.Canonical.SixStateCharacteristicPolynomial

open Matrix Polynomial
open InfoGeometry.Canonical.SixStateSpectralBridge
open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.HexagonalSixRootTiling

abbrev SixEnd := Module.End ℂ SixVector

def sixTrialityEnd : SixEnd := Matrix.toLin' sixTriality

def spectralEigenvalue (zeta : HexColor → ℂ) (n : HexIndex) : ℂ :=
  if (sheetColorEquiv n).1 = .positive then
    zeta (sheetColorEquiv n).2
  else -zeta (sheetColorEquiv n).2

abbrev BlockIndex := Fin 3 ⊕ Fin 3

def blockEquiv : BlockIndex ≃ (Fin 2 × Fin 3) where
  toFun x := match x with
    | Sum.inl i => (0, i)
    | Sum.inr i => (1, i)
  invFun p := match p.1 with
    | 0 => Sum.inl p.2
    | 1 => Sum.inr p.2
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro p
    rcases p with ⟨i, j⟩
    fin_cases i <;> rfl

def blockTriality : Matrix BlockIndex BlockIndex ℂ :=
  Matrix.fromBlocks colorShift 0 0 (-colorShift)

theorem blockTriality_reindex :
    Matrix.reindex blockEquiv.symm blockEquiv.symm sixTriality = blockTriality := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [Matrix.reindex_apply, blockEquiv, blockTriality,
            sixTriality, sheetParity, uPlus, uMinus,
            Matrix.kroneckerMap_apply]
      | inr j =>
          simp [Matrix.reindex_apply, blockEquiv, blockTriality,
            sixTriality, sheetParity, uPlus, uMinus,
            Matrix.kroneckerMap_apply]
  | inr i =>
      cases j with
      | inl j =>
          simp [Matrix.reindex_apply, blockEquiv, blockTriality,
            sixTriality, sheetParity, uPlus, uMinus,
            Matrix.kroneckerMap_apply]
      | inr j =>
          simp [Matrix.reindex_apply, blockEquiv, blockTriality,
            sixTriality, sheetParity, uPlus, uMinus,
            Matrix.kroneckerMap_apply]

theorem colorShift_charpoly :
    colorShift.charpoly = X ^ 3 - 1 := by
  unfold Matrix.charpoly Matrix.charmatrix
  rw [Matrix.det_fin_three]
  simp [colorShift]
  ring

theorem neg_colorShift_charpoly :
    (-colorShift).charpoly = X ^ 3 + 1 := by
  unfold Matrix.charpoly Matrix.charmatrix
  rw [Matrix.det_fin_three]
  simp [colorShift]
  ring

theorem blockTriality_charpoly :
    blockTriality.charpoly = (X ^ 3 - 1) * (X ^ 3 + 1) := by
  simp [blockTriality, colorShift_charpoly, neg_colorShift_charpoly]

theorem sixTriality_charpoly :
    sixTriality.charpoly = X ^ 6 - 1 := by
  rw [← Matrix.charpoly_reindex blockEquiv.symm sixTriality]
  rw [blockTriality_reindex, blockTriality_charpoly]
  ring

theorem sixTriality_charpoly_separable :
    sixTriality.charpoly.Separable := by
  rw [sixTriality_charpoly]
  exact Polynomial.separable_X_pow_sub_C 1 (by norm_num) (by norm_num)

theorem sixTriality_charpoly_splits :
    sixTriality.charpoly.Splits := by
  exact IsAlgClosed.splits _

theorem sixTriality_charpoly_squarefree :
    Squarefree sixTriality.charpoly :=
  sixTriality_charpoly_separable.squarefree

theorem sixTriality_charpoly_cyclotomic_factorization :
    sixTriality.charpoly =
      (X - 1) * (X + 1) * (X ^ 2 + X + 1) * (X ^ 2 - X + 1) := by
  rw [sixTriality_charpoly]
  ring

theorem sixTriality_charpoly_positive_cubic_factor :
    sixTriality.charpoly =
      ((X - 1) * (X ^ 2 + X + 1)) *
        ((X + 1) * (X ^ 2 - X + 1)) := by
  rw [sixTriality_charpoly]
  ring

theorem spectralVector_mem_eigenspace
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (n : HexIndex) :
    spectralVector zeta n ∈
      sixTrialityEnd.eigenspace (spectralEigenvalue zeta n) := by
  rw [Module.End.mem_eigenspace_iff]
  change sixTriality *ᵥ spectralVector zeta n =
    spectralEigenvalue zeta n • spectralVector zeta n
  exact spectralVector_triality zeta hzeta n

theorem spectral_eigenspace_ne_bot
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (n : HexIndex) :
    sixTrialityEnd.eigenspace (spectralEigenvalue zeta n) ≠ ⊥ := by
  have hv := spectralVector_mem_eigenspace zeta hzeta n
  have hvnz := spectralVector_ne_zero zeta n
  intro hbot
  have hvbot : spectralVector zeta n ∈ (⊥ : Submodule ℂ SixVector) := by
    rw [← hbot]
    exact hv
  exact hvnz ((Submodule.mem_bot ℂ).mp hvbot)

theorem spectralEigenvalue_pow_six
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (n : HexIndex) :
    spectralEigenvalue zeta n ^ 6 = 1 := by
  by_cases h : (sheetColorEquiv n).1 = .positive
  · rw [show spectralEigenvalue zeta n = zeta (sheetColorEquiv n).2 by
      simp [spectralEigenvalue, h]]
    calc
      zeta (sheetColorEquiv n).2 ^ 6 =
          (zeta (sheetColorEquiv n).2 ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hzeta]; norm_num
  · rw [show spectralEigenvalue zeta n = -zeta (sheetColorEquiv n).2 by
      simp [spectralEigenvalue, h]]
    calc
      (-zeta (sheetColorEquiv n).2) ^ 6 =
          (zeta (sheetColorEquiv n).2) ^ 6 := by ring
      _ = 1 := by
        calc
          zeta (sheetColorEquiv n).2 ^ 6 =
              (zeta (sheetColorEquiv n).2 ^ 3) ^ 2 := by ring
          _ = 1 := by rw [hzeta]; norm_num

theorem spectralEigenvalue_pairwise
    (zeta : HexColor → ℂ)
    (hinj : Function.Injective zeta)
    (hneg : ∀ a b, zeta a ≠ -zeta b) :
    ∀ ⦃n m : HexIndex⦄, n ≠ m →
      spectralEigenvalue zeta n ≠ spectralEigenvalue zeta m := by
  intro n m hnm hval
  have hsame : ∀ {a b : HexColor}, a ≠ b → zeta a ≠ zeta b := by
    intro a b hab heq
    exact hab (hinj heq)
  have hneg' : ∀ a b : HexColor, -zeta a ≠ zeta b := by
    intro a b heq
    apply hneg b a
    simpa [eq_comm] using heq
  fin_cases n <;> fin_cases m <;>
    simp [spectralEigenvalue, sheetColorEquiv, sheetOf, colorOf] at hnm hval ⊢ <;>
    first
    | exact hneg _ _ hval
    | exact hneg' _ _ hval
    | exact hsame (by decide) hval

theorem spectralVector_linearIndependent
    (zeta : HexColor → ℂ)
    (hzeta : ∀ a, zeta a ^ 3 = 1)
    (hinj : Function.Injective zeta)
    (hneg : ∀ a b, zeta a ≠ -zeta b) :
    LinearIndependent ℂ (spectralVector zeta) := by
  have hμ : Function.Injective (spectralEigenvalue zeta) := by
    intro n m h
    by_contra hnm
    exact (spectralEigenvalue_pairwise zeta hinj hneg hnm) h
  apply Module.End.eigenvectors_linearIndependent' sixTrialityEnd
    (spectralEigenvalue zeta) hμ (spectralVector zeta)
  intro n
  exact ⟨spectralVector_mem_eigenspace zeta hzeta n,
    spectralVector_ne_zero zeta n⟩

noncomputable def spectralBasis
    (zeta : HexColor → ℂ)
    (hzeta : ∀ a, zeta a ^ 3 = 1)
    (hinj : Function.Injective zeta)
    (hneg : ∀ a b, zeta a ≠ -zeta b) :
    Module.Basis HexIndex ℂ SixVector := by
  let hli := spectralVector_linearIndependent zeta hzeta hinj hneg
  apply Module.Basis.mk hli
  rw [← hli.span_eq_top_of_card_eq_finrank]
  simp [SixVector]

theorem spectralBasis_apply
    (zeta : HexColor → ℂ)
    (hzeta : ∀ a, zeta a ^ 3 = 1)
    (hinj : Function.Injective zeta)
    (hneg : ∀ a b, zeta a ≠ -zeta b)
    (n : HexIndex) :
    spectralBasis zeta hzeta hinj hneg n = spectralVector zeta n := by
  simp [spectralBasis]

theorem spectralBasis_triality
    (zeta : HexColor → ℂ)
    (hzeta : ∀ a, zeta a ^ 3 = 1)
    (hinj : Function.Injective zeta)
    (hneg : ∀ a b, zeta a ≠ -zeta b)
    (n : HexIndex) :
    sixTriality *ᵥ spectralBasis zeta hzeta hinj hneg n =
      spectralEigenvalue zeta n • spectralBasis zeta hzeta hinj hneg n := by
  rw [spectralBasis_apply]
  exact spectralVector_triality zeta hzeta n

theorem spectralBasis_parity
    (zeta : HexColor → ℂ)
    (hzeta : ∀ a, zeta a ^ 3 = 1)
    (hinj : Function.Injective zeta)
    (hneg : ∀ a b, zeta a ≠ -zeta b)
    (n : HexIndex) :
    sixParity *ᵥ spectralBasis zeta hzeta hinj hneg n =
      (if (sheetColorEquiv n).1 = .positive then
          spectralBasis zeta hzeta hinj hneg n
       else -spectralBasis zeta hzeta hinj hneg n) := by
  rw [spectralBasis_apply]
  exact spectralVector_parity zeta n

theorem spectralEigenvalue_isRoot_charpoly
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (n : HexIndex) :
    sixTriality.charpoly.IsRoot (spectralEigenvalue zeta n) := by
  have he : sixTrialityEnd.HasEigenvalue (spectralEigenvalue zeta n) :=
    (Module.End.hasEigenvalue_iff).2 (spectral_eigenspace_ne_bot zeta hzeta n)
  have hr :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly
      sixTrialityEnd (spectralEigenvalue zeta n)).1 he
  simpa [sixTrialityEnd, Matrix.charpoly_toLin'] using hr

theorem spectral_eigenspace_finrank_eq_one
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (n : HexIndex) :
    Module.finrank ℂ
        (sixTrialityEnd.eigenspace (spectralEigenvalue zeta n)) = 1 := by
  have hne :
      sixTrialityEnd.eigenspace (spectralEigenvalue zeta n) ≠ ⊥ :=
    spectral_eigenspace_ne_bot zeta hzeta n
  have hlow :
      1 ≤ Module.finrank ℂ
        (sixTrialityEnd.eigenspace (spectralEigenvalue zeta n)) :=
    (Submodule.one_le_finrank_iff).2 hne
  have hsep : sixTrialityEnd.charpoly.Separable := by
    rw [sixTrialityEnd, Matrix.charpoly_toLin']
    exact sixTriality_charpoly_separable
  have hupp :
      Module.finrank ℂ
        (sixTrialityEnd.eigenspace (spectralEigenvalue zeta n)) ≤ 1 :=
    (LinearMap.finrank_eigenspace_le sixTrialityEnd (spectralEigenvalue zeta n)).trans
      (Polynomial.rootMultiplicity_le_one_of_separable hsep
        (spectralEigenvalue zeta n))
  exact Nat.le_antisymm hupp hlow

theorem spectral_eigenspace_eq_span
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (n : HexIndex) :
    sixTrialityEnd.eigenspace (spectralEigenvalue zeta n) =
      Submodule.span ℂ {spectralVector zeta n} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · refine Submodule.span_le.2 ?_
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact spectralVector_mem_eigenspace zeta hzeta n
  · rw [spectral_eigenspace_finrank_eq_one zeta hzeta n]
    exact finrank_span_singleton (spectralVector_ne_zero zeta n)

end InfoGeometry.Canonical.SixStateCharacteristicPolynomial
