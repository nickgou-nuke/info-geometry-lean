import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SL2SpinorLadder

noncomputable section

namespace InfoGeometry.Canonical.NuclearBathCommutant

open InfoGeometry.Canonical.SL2SpinorLadder

/-!
# Bath commutants for the native five-graded nuclear carrier

The bath is represented by a set of elements of the existing
`SL2SpinorLadder.Alg` carrier.  This file introduces no new operator carrier;
it records the intrinsic commutant predicate and its linear closure.
-/

/-- Elements whose native Lie bracket with every bath observable vanishes. -/
def CommutesWithBath (bath : Set Alg) (X : Alg) : Prop :=
  ∀ ⦃B : Alg⦄, B ∈ bath → Alg.br X B = 0

/-! ## Native associative operator realization -/

/-- The adjoint action realizes the native Lie carrier as associative linear
operators on itself.  This is the carrier on which the repository's KMS/GNS
owners can later be instantiated. -/
abbrev AdjointOperator := Module.End ℝ Alg

def adjointOperator (X : Alg) : AdjointOperator :=
  LieAlgebra.ad ℝ Alg X

@[simp] theorem adjointOperator_apply (X Y : Alg) :
    adjointOperator X Y = ⁅X, Y⁆ := by
  rfl

theorem adjointOperator_commutes_of_bracket_zero
    {X Y : Alg} (hXY : ⁅X, Y⁆ = 0) :
    adjointOperator X * adjointOperator Y =
      adjointOperator Y * adjointOperator X := by
  have h := (LieAlgebra.ad ℝ Alg).map_lie X Y
  rw [LieRing.of_associative_ring_bracket, hXY] at h
  have h' :
      (LieAlgebra.ad ℝ Alg X) * (LieAlgebra.ad ℝ Alg Y) -
          (LieAlgebra.ad ℝ Alg Y) * (LieAlgebra.ad ℝ Alg X) = 0 := by
    simpa [LieRing.of_associative_ring_bracket] using h.symm
  exact sub_eq_zero.mp h'

/-- The associative operator image of a native Lie bath. -/
def adjointOperatorSet (bath : Set Alg) : Set AdjointOperator :=
  {T | ∃ B ∈ bath, T = adjointOperator B}

theorem adjointOperator_mem_set
    {bath : Set Alg} {B : Alg} (hB : B ∈ bath) :
    adjointOperator B ∈ adjointOperatorSet bath :=
  ⟨B, hB, rfl⟩

theorem adjointOperator_commutes_with_bath_image
    {bath : Set Alg} {X : Alg}
    (hX : CommutesWithBath bath X) :
    ∀ T ∈ adjointOperatorSet bath,
      adjointOperator X * T = T * adjointOperator X := by
  intro T hT
  rcases hT with ⟨B, hB, rfl⟩
  exact adjointOperator_commutes_of_bracket_zero (hX hB)

@[simp] theorem commutesWithBath_empty (X : Alg) :
    CommutesWithBath (∅ : Set Alg) X := by
  intro B hB
  exact False.elim hB

@[simp] theorem commutesWithBath_zero (bath : Set Alg) :
    CommutesWithBath bath (0 : Alg) := by
  intro B hB
  ext <;> dsimp [Alg.br] <;> ring

theorem commutesWithBath_add
    (bath : Set Alg) (X Y : Alg)
    (hX : CommutesWithBath bath X)
    (hY : CommutesWithBath bath Y) :
    CommutesWithBath bath (X + Y) := by
  intro B hB
  rw [Alg.br_add_left, hX hB, hY hB, add_zero]

theorem commutesWithBath_smul
    (bath : Set Alg) (c : ℝ) (X : Alg)
    (hX : CommutesWithBath bath X) :
    CommutesWithBath bath (c • X) := by
  intro B hB
  rw [Alg.br_smul_left, hX hB, smul_zero]

theorem commutesWithBath_bracket
    (bath : Set Alg) (X Y : Alg)
    (hX : CommutesWithBath bath X)
    (hY : CommutesWithBath bath Y) :
    CommutesWithBath bath ⁅X, Y⁆ := by
  intro B hB
  have hxy := Alg.br_jacobi B X Y
  have hYX : Alg.br Y B = 0 := hY hB
  have hXX : Alg.br X B = 0 := hX hB
  have hBX : Alg.br B X = 0 := by
    rw [Alg.br_skew, hXX, neg_zero]
  have hx0 : Alg.br X 0 = 0 := by
    ext <;> dsimp [Alg.br] <;> ring
  have hy0 : Alg.br Y 0 = 0 := by
    ext <;> dsimp [Alg.br] <;> ring
  rw [hYX, hBX, hx0, hy0] at hxy
  have hxy' : Alg.br B (Alg.br X Y) = 0 := by
    simpa only [add_zero] using hxy
  change Alg.br (Alg.br X Y) B = 0
  rw [Alg.br_skew, hxy', neg_zero]

/-! A grading is supplied as data together with its bracket law.  This keeps
the physical grade interpretation separate from the commutant predicate. -/

def GradedBracketLaw (grade : ℤ → Submodule ℝ Alg) : Prop :=
  ∀ (i j : ℤ) (X Y : Alg),
    X ∈ grade i → Y ∈ grade j →
      ⁅X, Y⁆ ∈ grade (i + j)

def GradedCommutesWithBath
    (grade : ℤ → Submodule ℝ Alg)
    (bath : Set Alg) (i : ℤ) : Set Alg :=
  {X | X ∈ grade i ∧ CommutesWithBath bath X}

/-- The homogeneous bath commutant is a native submodule. -/
def gradedCommutesWithBathSubmodule
    (grade : ℤ → Submodule ℝ Alg)
    (bath : Set Alg) (i : ℤ) : Submodule ℝ Alg where
  carrier := GradedCommutesWithBath grade bath i
  zero_mem' := by
    exact ⟨(grade i).zero_mem, commutesWithBath_zero bath⟩
  add_mem' := by
    intro X Y hX hY
    exact ⟨(grade i).add_mem hX.1 hY.1,
      commutesWithBath_add bath X Y hX.2 hY.2⟩
  smul_mem' := by
    intro c X hX
    exact ⟨(grade i).smul_mem c hX.1,
      commutesWithBath_smul bath c X hX.2⟩

@[simp] theorem mem_gradedCommutesWithBathSubmodule_iff
    (grade : ℤ → Submodule ℝ Alg)
    (bath : Set Alg) (i : ℤ) (X : Alg) :
    X ∈ gradedCommutesWithBathSubmodule grade bath i ↔
      X ∈ GradedCommutesWithBath grade bath i :=
  Iff.rfl

theorem gradedCommutesWithBath_add
    (grade : ℤ → Submodule ℝ Alg)
    (bath : Set Alg) (i : ℤ) {X Y : Alg}
    (hX : X ∈ GradedCommutesWithBath grade bath i)
    (hY : Y ∈ GradedCommutesWithBath grade bath i) :
    X + Y ∈ GradedCommutesWithBath grade bath i :=
  (gradedCommutesWithBathSubmodule grade bath i).add_mem hX hY

theorem gradedCommutesWithBath_smul
    (grade : ℤ → Submodule ℝ Alg)
    (bath : Set Alg) (i : ℤ) (c : ℝ) {X : Alg}
    (hX : X ∈ GradedCommutesWithBath grade bath i) :
    c • X ∈ GradedCommutesWithBath grade bath i :=
  (gradedCommutesWithBathSubmodule grade bath i).smul_mem c hX

theorem gradedCommutesWithBath_bracket
    (grade : ℤ → Submodule ℝ Alg)
    (hgrade : GradedBracketLaw grade)
    (bath : Set Alg) (i j : ℤ) {X Y : Alg}
    (hX : X ∈ GradedCommutesWithBath grade bath i)
    (hY : Y ∈ GradedCommutesWithBath grade bath j) :
    ⁅X, Y⁆ ∈ GradedCommutesWithBath grade bath (i + j) := by
  exact ⟨hgrade i j X Y hX.1 hY.1,
    commutesWithBath_bracket bath X Y hX.2 hY.2⟩

end InfoGeometry.Canonical.NuclearBathCommutant
