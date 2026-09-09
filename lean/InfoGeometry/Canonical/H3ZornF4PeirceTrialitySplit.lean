import Mathlib
import InfoGeometry.Algebra.F4Derivations
import InfoGeometry.Algebra.SplitAlbertF4BasisTrace
import InfoGeometry.Canonical.H3ZornS3JordanTopologicalReadout
import InfoGeometry.Canonical.F4ActionMatrixRationalCertificate

noncomputable section

namespace InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical
open InfoGeometry.Canonical.F4ActionMatrixRationalCertificate

abbrev H3 := H3Zorn ℝ
abbrev EndH3 := Module.End ℝ H3
abbrev Zorn := ZornVectorMatrix ℝ

/-- First 24 entries of the certified `f4Basis`: the three eight-dimensional
Peirce shift families. -/
def shiftIndex (i : Fin 24) : Fin 52 := ⟨i.1, by omega⟩

/-- Last 28 entries of the certified `f4Basis`: pairwise inner derivations of
one eight-dimensional Peirce slot. -/
def trialityIndex (i : Fin 28) : Fin 52 := ⟨24 + i.1, by omega⟩

theorem shiftIndex_injective : Function.Injective shiftIndex := by
  intro i j h
  apply Fin.ext
  simpa [shiftIndex] using congrArg Fin.val h

theorem trialityIndex_injective : Function.Injective trialityIndex := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [trialityIndex] using hv

/-- Actual native derivations in the 24-entry Peirce-shift block. -/
def shiftDerivation (i : Fin 24) : EndH3 :=
  (f4Basis (shiftIndex i)).1

/-- Actual native derivations in the 28-entry triality block. -/
def trialityDerivation (i : Fin 28) : EndH3 :=
  (f4Basis (trialityIndex i)).1

/-- Span of the first 24 certified derivations. -/
def peirceShiftBasisSpan : Submodule ℝ EndH3 :=
  Submodule.span ℝ (Set.range shiftDerivation)

/-- Span of the last 28 certified derivations. -/
def trialityBasisSpan : Submodule ℝ EndH3 :=
  Submodule.span ℝ (Set.range trialityDerivation)

/-- Every member of the 24-generator span is a genuine Jordan derivation. -/
theorem peirceShiftBasisSpan_le_F4 :
    peirceShiftBasisSpan ≤ H3ZornF4Derivations := by
  rw [peirceShiftBasisSpan]
  refine Submodule.span_le.mpr ?_
  rintro D ⟨i, rfl⟩
  exact (f4Basis (shiftIndex i)).property

/-- Every member of the 28-generator triality span is a genuine Jordan
derivation. -/
theorem trialityBasisSpan_le_F4 :
    trialityBasisSpan ≤ H3ZornF4Derivations := by
  rw [trialityBasisSpan]
  refine Submodule.span_le.mpr ?_
  rintro D ⟨i, rfl⟩
  exact (f4Basis (trialityIndex i)).property

/-- Arbitrary insertion into the `J₁₂` off-diagonal Peirce slot. -/
def embedJ12 (x : Zorn) : H3 :=
  { α₁ := 0, α₂ := 0, α₃ := 0, a := x, b := 0, c := 0 }

/-- Seed Peirce inner derivation.  The certified basis uses this same mechanism
on coordinate basis elements. -/
def peirceInnerDeriv12 (x : Zorn) : EndH3 :=
  (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 x) : EndH3)

/-- The seed Peirce family consists of genuine `F4` derivations. -/
theorem peirceInnerDeriv12_mem_F4 (x : Zorn) :
    peirceInnerDeriv12 x ∈ H3ZornF4Derivations := by
  exact h3ZornJordanInnerDerivation_mem_F4 h3_diag₁ (embedJ12 x)

/-- `S₃` conjugation of every seed Peirce derivation remains in the native
Jordan derivation algebra.  This reuses the already-proved automorphism
conjugation theorem instead of recomputing the other Peirce slots. -/
theorem S3_conjugate_peirceInnerDeriv12_mem_F4
    (σ : S3Perm) (x : Zorn) :
    S3ConjugateEnd σ (peirceInnerDeriv12 x) ∈ H3ZornF4Derivations := by
  exact S3ConjugateEnd_mem_H3ZornF4Derivations σ _
    (peirceInnerDeriv12_mem_F4 x)

/-- The full `S₃`-generated Peirce-shift orbit span. -/
def peirceShiftOrbitSpan : Submodule ℝ EndH3 :=
  Submodule.span ℝ
    {D | ∃ (σ : S3Perm) (x : Zorn),
      D = S3ConjugateEnd σ (peirceInnerDeriv12 x)}

/-- The orbit-span construction lands in the native `F4` derivation algebra. -/
theorem peirceShiftOrbitSpan_le_F4 :
    peirceShiftOrbitSpan ≤ H3ZornF4Derivations := by
  rw [peirceShiftOrbitSpan]
  refine Submodule.span_le.mpr ?_
  intro D hD
  rcases hD with ⟨σ, x, rfl⟩
  exact S3_conjugate_peirceInnerDeriv12_mem_F4 σ x

/-! ## Certified action-row dimensions

The repository's exact rational/real action certificate proves all 52 rows are
linearly independent.  Restricting that family to indices `0..23` and
`24..51` gives independent 24- and 28-element families.  These theorems are
kernel-level dimension certificates for the explicit Peirce/triality basis
partition.  They do not, by themselves, identify the abstract stabilizer Lie
algebra with a particular real form of `so(8)`.
-/

abbrev ActionRow := Fin 729 → ℝ

def shiftActionRow (i : Fin 24) : ActionRow :=
  f4ActionMatrixReal (shiftIndex i)

def trialityActionRow (i : Fin 28) : ActionRow :=
  f4ActionMatrixReal (trialityIndex i)

theorem shiftActionRow_linearIndependent :
    LinearIndependent ℝ shiftActionRow := by
  exact f4ActionMatrixReal_linearIndependent.comp
    shiftIndex shiftIndex_injective

theorem trialityActionRow_linearIndependent :
    LinearIndependent ℝ trialityActionRow := by
  exact f4ActionMatrixReal_linearIndependent.comp
    trialityIndex trialityIndex_injective

/-- Exact dimension of the certified 24-row Peirce-shift action sector. -/
theorem shiftActionSpan_finrank :
    Module.finrank ℝ
      (Submodule.span ℝ (Set.range shiftActionRow)) = 24 := by
  simpa using finrank_span_eq_card shiftActionRow_linearIndependent

/-- Exact dimension of the certified 28-row triality action sector. -/
theorem trialityActionSpan_finrank :
    Module.finrank ℝ
      (Submodule.span ℝ (Set.range trialityActionRow)) = 28 := by
  simpa using finrank_span_eq_card trialityActionRow_linearIndependent

/-- The explicit basis partition has the expected `24 + 28 = 52` size. -/
theorem peirce_triality_dimension_arithmetic : 24 + 28 = 52 := by
  norm_num

/-- The alternative `14 + 22 + 16` count is retained only as dimension
arithmetic.  A real-form-specific chain `g₂ ⊂ so(9) ⊂ f₄` is not inferred for
the split Albert algebra without an explicit stabilizer embedding theorem. -/
theorem g2_flag_dimension_arithmetic : 14 + 22 + 16 = 52 := by
  norm_num

/-- Current remaining structural obligation: promote the certified 24/28 basis
partition from action-row dimension certificates to an intrinsic direct-sum
identity of submodules inside `H3ZornF4Derivations`, and identify the
28-dimensional stabilizer with its correct split real orthogonal form. -/
def peirce_triality_intrinsic_closure_debt : String :=
  "Open: prove intrinsic directness/spanning of peirceShiftBasisSpan and trialityBasisSpan inside H3ZornF4Derivations, then identify the 28D idempotent stabilizer with the correct split real triality algebra."

end InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit
