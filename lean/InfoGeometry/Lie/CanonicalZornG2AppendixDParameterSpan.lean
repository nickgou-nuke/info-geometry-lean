import InfoGeometry.Lie.CanonicalZornG2AppendixDSourceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.Lie.CanonicalZornG2AppendixDParameterSpan

open InfoGeometry.Lie.CanonicalZornG2AppendixDSourceBridge
open InfoGeometry.Lie.CanonicalZornG2AppendixDGenerators
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge
open InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge

/-- The calibrated Appendix-D parameter table, with the three diagonal entries
included separately and the off-diagonal entries indexed by their ordered
pair. -/
noncomputable def family : Fin 15 → Params
  | 0 => appendixDCalibratedParameterXnn 0
  | 1 => appendixDCalibratedParameterXnn 1
  | 2 => appendixDCalibratedParameterXnn 2
  | 3 => appendixDCalibratedParameterXn0 0
  | 4 => appendixDCalibratedParameterXn0 1
  | 5 => appendixDCalibratedParameterXn0 2
  | 6 => appendixDCalibratedParameterX0n 0
  | 7 => appendixDCalibratedParameterX0n 1
  | 8 => appendixDCalibratedParameterX0n 2
  | 9 => appendixDCalibratedParameterXnm 0 1
  | 10 => appendixDCalibratedParameterXnm 0 2
  | 11 => appendixDCalibratedParameterXnm 1 0
  | 12 => appendixDCalibratedParameterXnm 1 2
  | 13 => appendixDCalibratedParameterXnm 2 0
  | 14 => appendixDCalibratedParameterXnm 2 1

private def S : Submodule ℝ Params :=
  Submodule.span ℝ (Set.range family)

private theorem family_mem (i : Fin 15) : family i ∈ S :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem scaled_unit_mem (j : Fin 14) (r : ℝ) (hr : r ≠ 0)
    (h : parameterUnit j r ∈ S) : parameterUnit j ∈ S := by
  have hs := S.smul_mem r⁻¹ h
  have heq : r⁻¹ • parameterUnit j r = parameterUnit j := by
    rw [parameterUnit_eq_smul, smul_smul, inv_mul_cancel₀ hr, one_smul]
  exact heq ▸ hs

theorem parameterUnit_mem_span (j : Fin 14) :
    parameterUnit j ∈ S := by
  have h0 : (1 / 3 : ℝ) • (parameterUnit 6 + parameterUnit 13) ∈ S := by
    simpa [S, family, appendixDCalibratedParameterXnn] using family_mem 0
  have h1 : (-2 / 3 : ℝ) • parameterUnit 6 +
      (1 / 3 : ℝ) • parameterUnit 13 ∈ S := by
    simpa [S, family, appendixDCalibratedParameterXnn] using family_mem 1
  fin_cases j
  · exact scaled_unit_mem 0 1 (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterXn0,
        appendixDParameterXn0Zero] using family_mem 3)
  · exact scaled_unit_mem 1 (-1) (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterXnm] using family_mem 9)
  · exact scaled_unit_mem 2 1 (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterXnm] using family_mem 10)
  · exact scaled_unit_mem 3 1 (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterXn0,
        appendixDParameterXn0One] using family_mem 4)
  · exact scaled_unit_mem 4 1 (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterX0n,
        appendixDParameterX0nTwo] using family_mem 8)
  · exact scaled_unit_mem 5 (-1) (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterXnm] using family_mem 11)
  · have hx := S.sub_mem h0 h1
    convert hx using 1 <;> funext i <;> fin_cases i <;>
      simp [parameterUnit] <;> ring
  · exact scaled_unit_mem 7 1 (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterXnm] using family_mem 12)
  · exact scaled_unit_mem 8 (-1) (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterXn0,
        appendixDParameterXn0Two] using family_mem 5)
  · exact scaled_unit_mem 9 1 (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterX0n,
        appendixDParameterX0nOne] using family_mem 7)
  · exact scaled_unit_mem 10 (-1) (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterX0n,
        appendixDParameterX0nZero] using family_mem 6)
  · exact scaled_unit_mem 11 1 (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterXnm] using family_mem 13)
  · exact scaled_unit_mem 12 1 (by norm_num) (by
      simpa [S, family, appendixDCalibratedParameterXnm] using family_mem 14)
  · have hx := S.add_mem (S.smul_mem 2 h0) h1
    convert hx using 1 <;> funext i <;> fin_cases i <;>
      simp [parameterUnit] <;> ring

theorem span_eq_top : S = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro p
  have hp : p = ∑ i : Fin 14, p i • parameterUnit i := by
    funext j
    simp [parameterUnit]
  rw [hp]
  exact Submodule.sum_mem _ (fun i _ => S.smul_mem _ (parameterUnit_mem_span i))

noncomputable def canonicalFamily : Fin 15 →
    InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  fun i => canonicalParameterLinearEquiv (family i)

theorem canonical_span_eq_top :
    Submodule.span ℝ (Set.range canonicalFamily) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro D
  let T : Submodule ℝ
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
    Submodule.span ℝ (Set.range canonicalFamily)
  let L : Params →ₗ[ℝ]
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
    canonicalParameterLinearEquiv.toLinearMap
  let p : Params := canonicalParameterLinearEquiv.symm D
  have hp : p ∈ S := by
    rw [span_eq_top]
    exact Submodule.mem_top
  have hLp : L p ∈ T := by
    refine Submodule.span_induction (p := fun x _ => L x ∈ T) ?_ ?_ ?_ ?_ hp
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · simpa [L] using T.zero_mem
    · intro x y hx hy hx' hy'
      simpa [L] using T.add_mem hx' hy'
    · intro a x hx hx'
      simpa [L] using T.smul_mem a hx'
  simpa [T, L, p, canonicalFamily] using hLp

theorem canonicalFamily_span_eq_standardDerivationSpan :
    Submodule.span ℝ (Set.range canonicalFamily) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.standardDerivationSpan := by
  rw [canonical_span_eq_top,
    InfoGeometry.Lie.SplitOctonionStandardDerivation.standardDerivations_span_top]

theorem parameterAction_eq_canonicalParameter (p : Params)
    (X : InfoGeometry.Canonical.ZornMatrix ℝ) :
    canonicalVectorEquiv.symm
        (parameterAction p (canonicalVectorEquiv X)) =
      (canonicalParameterLinearEquiv p).1 X := by
  rfl

theorem paper_parameterAction_eq_paperDerivation (p : Params)
    (X : InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge.PaperZorn) :
    paperCanonicalLinearEquiv.symm
        (canonicalVectorEquiv.symm
          (parameterAction p
            (canonicalVectorEquiv (paperCanonicalLinearEquiv X)))) =
      paperDerivation (canonicalParameterLinearEquiv p) X := by
  rfl

theorem appendixDXn0_calibrated_eq_paperDerivation
    (n : Fin 3) (v : InfoGeometry.Lie.CanonicalZornG2AppendixDSourceBridge.Vector) :
    appendixDCalibratedVectorToPaper ((appendixDXn0 n) v) =
      paperDerivation
        (canonicalParameterLinearEquiv (appendixDCalibratedParameterXn0 n))
        (appendixDCalibratedVectorToPaper v) := by
  rw [appendixDXn0_calibrated_eq_parameterAction]
  exact paper_parameterAction_eq_paperDerivation _ _

theorem appendixDX0n_calibrated_eq_paperDerivation
    (n : Fin 3) (v : InfoGeometry.Lie.CanonicalZornG2AppendixDSourceBridge.Vector) :
    appendixDCalibratedVectorToPaper ((appendixDX0n n) v) =
      paperDerivation
        (canonicalParameterLinearEquiv (appendixDCalibratedParameterX0n n))
        (appendixDCalibratedVectorToPaper v) := by
  rw [appendixDX0n_calibrated_eq_parameterAction]
  exact paper_parameterAction_eq_paperDerivation _ _

theorem appendixDXnm_calibrated_eq_paperDerivation
    (n m : Fin 3) (h : n ≠ m)
    (v : InfoGeometry.Lie.CanonicalZornG2AppendixDSourceBridge.Vector) :
    appendixDCalibratedVectorToPaper ((appendixDXnm n m h) v) =
      paperDerivation
        (canonicalParameterLinearEquiv (appendixDCalibratedParameterXnm n m))
        (appendixDCalibratedVectorToPaper v) := by
  rw [appendixDXnm_calibrated_eq_parameterAction]
  exact paper_parameterAction_eq_paperDerivation _ _

end InfoGeometry.Lie.CanonicalZornG2AppendixDParameterSpan
