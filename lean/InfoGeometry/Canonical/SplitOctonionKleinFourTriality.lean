import Mathlib
import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication

namespace InfoGeometry.Canonical

/-! The four-sector grading of the executable coordinate multiplication table.

This owner deliberately does not identify the independently defined
`splitOctonionMul` implementation with `basisMul`; that is a separate bridge
requiring a consistent multiplication convention.
-/

abbrev KleinFour := ZMod 2 × ZMod 2

def gradeOfBasis : IntegralSplitBasis → KleinFour
  | .one => (0, 0)
  | .l => (0, 0)
  | .i => (1, 0)
  | .il => (1, 0)
  | .j => (0, 1)
  | .jl => (0, 1)
  | .k => (1, 1)
  | .kl => (1, 1)

/-- Mapping from StandardIntegralSplitOctonion to its KleinFour grade. -/
def gradeOfOct (x : StandardIntegralSplitOctonion) : KleinFour :=
  if x = oneOct then (0, 0)
  else if x = lOct then (0, 0)
  else if x = iOct then (1, 0)
  else if x = ilOct then (1, 0)
  else if x = jOct then (0, 1)
  else if x = jlOct then (0, 1)
  else if x = kOct then (1, 1)
  else (1, 1)

def gradeGenerators (g : KleinFour) : Set StandardIntegralSplitOctonion :=
  match g with
  | (0, 0) => {oneOct, lOct}
  | (1, 0) => {iOct, ilOct}
  | (0, 1) => {jOct, jlOct}
  | (1, 1) => {kOct, klOct}

def planeComponent (g : KleinFour) :
    Submodule ℤ StandardIntegralSplitOctonion :=
  Submodule.span ℤ (gradeGenerators g)

@[simp] theorem zmodTwo_one_add_one :
    (1 : ZMod 2) + 1 = 0 := by
  decide

@[simp] theorem zmodTwo_two :
    (2 : ZMod 2) = 0 := by
  decide

theorem gradeOfBasis_neutral (p : IntegralSplitBasis) :
    gradeOfBasis p = (0, 0) ↔ p = .one ∨ p = .l := by
  cases p <;> simp [gradeOfBasis]

theorem red_green_basisProduct_mem_blue :
    basisMul .i .j ∈ planeComponent ((1, 0) + (0, 1)) := by
  change kOct ∈ planeComponent ((1, 0) + (0, 1))
  change kOct ∈ Submodule.span ℤ {kOct, klOct}
  exact Submodule.subset_span (by simp)

/-!
The executable multiplication table is graded on every basis pair.  This is
the coordinate-level statement from which the corresponding bilinear sector
closure is obtained; no auxiliary ``evidence'' structure is needed.
-/
theorem basisMul_mem_grade_add
    (p q : IntegralSplitBasis) :
    basisMul p q ∈ planeComponent (gradeOfBasis p + gradeOfBasis q) := by
  cases p <;> cases q <;>
    norm_num [basisMul, planeComponent, gradeOfBasis, gradeGenerators,
      zmodTwo_one_add_one, zmodTwo_two]
  all_goals
    apply Submodule.subset_span
    simp [splitBasisVector, oneOct, lOct, iOct, ilOct,
      jOct, jlOct, kOct, klOct]


def swapGrade : KleinFour ≃+ KleinFour where
  toFun := fun g => (g.2, g.1)
  invFun := fun g => (g.2, g.1)
  left_inv := by intro g; cases g; rfl
  right_inv := by intro g; cases g; rfl
  map_add' := by intro g h; rfl

theorem swapGrade_zero : swapGrade 0 = 0 := rfl

theorem swapGrade_preserves_nonzero
    {g : KleinFour} (hg : g ≠ 0) : swapGrade g ≠ 0 := by
  intro h
  apply hg
  have hs := congrArg swapGrade.symm h
  simpa using hs

end InfoGeometry.Canonical
