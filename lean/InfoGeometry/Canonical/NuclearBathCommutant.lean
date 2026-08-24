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

end InfoGeometry.Canonical.NuclearBathCommutant
