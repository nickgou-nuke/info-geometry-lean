import InfoGeometry.Physics.Algebra.TripotentLeftRightPeirceProjectors

/-!
# Range submodules for the five Peirce weights

This file packages the already-proved grouped projectors as submodules.  It
does not assert a direct-sum equivalence or a TKK structure.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics.Algebra

variable {R : Type*} [Ring R] [Algebra ℝ R]

def gradeNegTwoSubmodule (e : R) : Submodule ℝ R :=
  LinearMap.range (gradeNegTwoProjector e)

def gradeNegOneSubmodule (e : R) : Submodule ℝ R :=
  LinearMap.range (gradeNegOneProjector e)

def gradeZeroSubmodule (e : R) : Submodule ℝ R :=
  LinearMap.range (gradeZeroProjector e)

def gradePosOneSubmodule (e : R) : Submodule ℝ R :=
  LinearMap.range (gradePosOneProjector e)

def gradePosTwoSubmodule (e : R) : Submodule ℝ R :=
  LinearMap.range (gradePosTwoProjector e)

theorem mem_gradeNegTwoSubmodule {e x : R} :
    x ∈ gradeNegTwoSubmodule e ↔
      ∃ y, gradeNegTwoProjector e y = x := Iff.rfl

theorem mem_gradeNegOneSubmodule {e x : R} :
    x ∈ gradeNegOneSubmodule e ↔
      ∃ y, gradeNegOneProjector e y = x := Iff.rfl

theorem mem_gradeZeroSubmodule {e x : R} :
    x ∈ gradeZeroSubmodule e ↔
      ∃ y, gradeZeroProjector e y = x := Iff.rfl

theorem mem_gradePosOneSubmodule {e x : R} :
    x ∈ gradePosOneSubmodule e ↔
      ∃ y, gradePosOneProjector e y = x := Iff.rfl

theorem mem_gradePosTwoSubmodule {e x : R} :
    x ∈ gradePosTwoSubmodule e ↔
      ∃ y, gradePosTwoProjector e y = x := Iff.rfl

theorem gradeNegTwoSubmodule_adjoint_weight
    {e : R} (he : e * e * e = e) {x : R}
    (hx : x ∈ gradeNegTwoSubmodule e) :
    e * x - x * e = (-2 : ℝ) • x := by
  rcases hx with ⟨y, rfl⟩
  exact gradeNegTwo_adjoint_weight he y

theorem gradeNegOneSubmodule_adjoint_weight
    {e : R} (he : e * e * e = e) {x : R}
    (hx : x ∈ gradeNegOneSubmodule e) :
    e * x - x * e = (-1 : ℝ) • x := by
  rcases hx with ⟨y, rfl⟩
  exact gradeNegOne_adjoint_weight he y

theorem gradeZeroSubmodule_adjoint_weight
    {e : R} (he : e * e * e = e) {x : R}
    (hx : x ∈ gradeZeroSubmodule e) :
    e * x - x * e = 0 := by
  rcases hx with ⟨y, rfl⟩
  exact gradeZero_adjoint_weight he y

theorem gradePosOneSubmodule_adjoint_weight
    {e : R} (he : e * e * e = e) {x : R}
    (hx : x ∈ gradePosOneSubmodule e) :
    e * x - x * e = (1 : ℝ) • x := by
  rcases hx with ⟨y, rfl⟩
  exact gradePosOne_adjoint_weight he y

theorem gradePosTwoSubmodule_adjoint_weight
    {e : R} (he : e * e * e = e) {x : R}
    (hx : x ∈ gradePosTwoSubmodule e) :
    e * x - x * e = (2 : ℝ) • x := by
  rcases hx with ⟨y, rfl⟩
  exact gradePosTwo_adjoint_weight he y

end InfoGeometry.Canonical
