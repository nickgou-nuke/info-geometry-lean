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

structure GradedBracketLaw (grade : ℤ → Submodule ℝ Alg) : Prop where
  bracket_mem : ∀ (i j : ℤ) (X Y : Alg),
    X ∈ grade i → Y ∈ grade j →
      ⁅X, Y⁆ ∈ grade (i + j)

def GradedCommutesWithBath
    (grade : ℤ → Submodule ℝ Alg)
    (bath : Set Alg) (i : ℤ) : Set Alg :=
  {X | X ∈ grade i ∧ CommutesWithBath bath X}

theorem gradedCommutesWithBath_bracket
    (grade : ℤ → Submodule ℝ Alg)
    (hgrade : GradedBracketLaw grade)
    (bath : Set Alg) (i j : ℤ) {X Y : Alg}
    (hX : X ∈ GradedCommutesWithBath grade bath i)
    (hY : Y ∈ GradedCommutesWithBath grade bath j) :
    ⁅X, Y⁆ ∈ GradedCommutesWithBath grade bath (i + j) := by
  exact ⟨hgrade.bracket_mem i j X Y hX.1 hY.1,
    commutesWithBath_bracket bath X Y hX.2 hY.2⟩

end InfoGeometry.Canonical.NuclearBathCommutant
