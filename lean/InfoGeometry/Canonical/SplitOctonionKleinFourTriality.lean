import Mathlib
import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Geometry.KleinFourTag

namespace InfoGeometry.Canonical

/-! The four-sector grading of the executable coordinate multiplication table.

This owner deliberately does not identify the independently defined
`splitOctonionMul` implementation with `basisMul`; that is a separate bridge
requiring a consistent multiplication convention.
-/

abbrev KleinFour := InfoGeometry.Geometry.KleinFourTag.Tag

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

lemma splitBasisVector_injective :
    Function.Injective splitBasisVector := by
  intro p q h
  have hfs : Finsupp.single p (1 : ℤ) = Finsupp.single q 1 := by
    ext r
    simpa [splitBasisVector, Finsupp.single_eq_pi_single] using congrFun h r
  exact Finsupp.single_left_injective (by norm_num) hfs

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

/-!
The table above is a basis tensor.  `basisMulExtend` is its finite
bilinear extension to the coordinate carrier; keeping this definition
explicit avoids pretending that the table itself supplies a global algebra
instance.
-/
noncomputable def basisMulExtend
    (x y : StandardIntegralSplitOctonion) : StandardIntegralSplitOctonion :=
  ∑ p : IntegralSplitBasis, ∑ q : IntegralSplitBasis,
    (x p * y q) • basisMul p q

theorem basisMulExtend_basis (p q : IntegralSplitBasis) :
    basisMulExtend (splitBasisVector p) (splitBasisVector q) = basisMul p q := by
  classical
  simp [basisMulExtend, splitBasisVector, Pi.single_apply]

lemma basis_of_gradeGenerator_mem
    {g : KleinFour} {x : StandardIntegralSplitOctonion}
    (hx : x ∈ gradeGenerators g) :
    ∃ p : IntegralSplitBasis, x = splitBasisVector p := by
  rcases g with ⟨a, b⟩
  fin_cases a <;> fin_cases b
  all_goals
    simp [gradeGenerators] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

lemma gradeOfBasis_eq_of_generator_mem
    {g : KleinFour} {p : IntegralSplitBasis}
    (hp : splitBasisVector p ∈ gradeGenerators g) :
    gradeOfBasis p = g := by
  rcases g with ⟨a, b⟩
  fin_cases a <;> fin_cases b
  · simp [gradeGenerators] at hp
    rcases hp with hp | hp
    · have hp' : p = .one := splitBasisVector_injective (by simpa [oneOct] using hp)
      subst p
      norm_num [gradeOfBasis]
    · have hp' : p = .l := splitBasisVector_injective (by simpa [lOct] using hp)
      subst p
      norm_num [gradeOfBasis]
  · simp [gradeGenerators] at hp
    rcases hp with hp | hp
    · have hp' : p = .j := splitBasisVector_injective (by simpa [jOct] using hp)
      subst p
      norm_num [gradeOfBasis]
    · have hp' : p = .jl := splitBasisVector_injective (by simpa [jlOct] using hp)
      subst p
      norm_num [gradeOfBasis]
  · simp [gradeGenerators] at hp
    rcases hp with hp | hp
    · have hp' : p = .i := splitBasisVector_injective (by simpa [iOct] using hp)
      subst p
      norm_num [gradeOfBasis]
    · have hp' : p = .il := splitBasisVector_injective (by simpa [ilOct] using hp)
      subst p
      norm_num [gradeOfBasis]
  · simp [gradeGenerators] at hp
    rcases hp with hp | hp
    · have hp' : p = .k := splitBasisVector_injective (by simpa [kOct] using hp)
      subst p
      norm_num [gradeOfBasis]
    · have hp' : p = .kl := splitBasisVector_injective (by simpa [klOct] using hp)
      subst p
      norm_num [gradeOfBasis]

lemma basisMulExtend_add_left (x₁ x₂ y : StandardIntegralSplitOctonion) :
    basisMulExtend (x₁ + x₂) y =
      basisMulExtend x₁ y + basisMulExtend x₂ y := by
  ext r
  simp [basisMulExtend, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    mul_assoc, mul_left_comm, mul_comm]

lemma basisMulExtend_add_right (x y₁ y₂ : StandardIntegralSplitOctonion) :
    basisMulExtend x (y₁ + y₂) =
      basisMulExtend x y₁ + basisMulExtend x y₂ := by
  simp [basisMulExtend, Pi.add_apply, mul_add, add_mul,
    Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_comm]

lemma basisMulExtend_smul_left (a : ℤ) (x y : StandardIntegralSplitOctonion) :
    basisMulExtend (a • x) y = a • basisMulExtend x y := by
  ext r
  simp [basisMulExtend, Pi.smul_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

lemma basisMulExtend_smul_right (a : ℤ) (x y : StandardIntegralSplitOctonion) :
    basisMulExtend x (a • y) = a • basisMulExtend x y := by
  ext r
  simp [basisMulExtend, Pi.smul_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

lemma basisMulExtend_generator_mem
    {g h : KleinFour}
    {x y : StandardIntegralSplitOctonion}
    (hx : x ∈ gradeGenerators g)
    (hy : y ∈ gradeGenerators h) :
    basisMulExtend x y ∈ planeComponent (g + h) := by
  rcases basis_of_gradeGenerator_mem hx with ⟨p, hp⟩
  rcases basis_of_gradeGenerator_mem hy with ⟨q, hq⟩
  have hpg : gradeOfBasis p = g :=
    gradeOfBasis_eq_of_generator_mem (by simpa [← hp] using hx)
  have hqg : gradeOfBasis q = h :=
    gradeOfBasis_eq_of_generator_mem (by simpa [← hq] using hy)
  rw [hp, hq, basisMulExtend_basis]
  rw [← hpg, ← hqg]
  exact basisMul_mem_grade_add p q

theorem plane_mul_mem
    {g h : KleinFour}
    {x y : StandardIntegralSplitOctonion}
    (hx : x ∈ planeComponent g)
    (hy : y ∈ planeComponent h) :
    basisMulExtend x y ∈ planeComponent (g + h) := by
  induction hx using Submodule.span_induction with
  | mem p hp =>
      induction hy using Submodule.span_induction with
      | mem q hq =>
          exact basisMulExtend_generator_mem hp hq
      | zero =>
          simp [basisMulExtend]
      | add y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
          rw [basisMulExtend_add_right]
          exact (planeComponent (g + h)).add_mem ih₁ ih₂
      | smul a y hy ih =>
          rw [basisMulExtend_smul_right]
          exact (planeComponent (g + h)).smul_mem a ih
  | zero =>
      simp [basisMulExtend]
  | add x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
      rw [basisMulExtend_add_left]
      exact (planeComponent (g + h)).add_mem ih₁ ih₂
  | smul a x hx ih =>
      rw [basisMulExtend_smul_left]
      exact (planeComponent (g + h)).smul_mem a ih


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
