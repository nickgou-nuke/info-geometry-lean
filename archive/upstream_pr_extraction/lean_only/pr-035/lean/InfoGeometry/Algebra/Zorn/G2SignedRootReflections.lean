import InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge

/-!
# The two simple reflections on the signed `G₂` root carrier

The positive-root labels alone are not closed under reflection.  This owner
therefore uses a sign together with a positive-root label, and records the
two simple reflections by their finite root tables.  The coordinate theorem
below identifies these tables with the integer-coordinate reflections in
`G2PositiveRootsInvariance`.
-/

namespace InfoGeometry.Algebra.Zorn.G2SignedRootReflections

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Algebra.Zorn.G2Roots

abbrev SignedPositiveRoot := Bool × G2PositiveRoot

def negPair (v : ℤ × ℤ) : ℤ × ℤ := (-v.1, -v.2)

def signedRootCoordinates : SignedPositiveRoot → ℤ × ℤ
  | (true, α) => rootCoordinates α
  | (false, α) => negPair (rootCoordinates α)

def simpleReflectionOne : SignedPositiveRoot → SignedPositiveRoot
  | (sign, .alpha) => (!sign, .alpha)
  | (sign, .beta) => (sign, .three_alpha_beta)
  | (sign, .alpha_add_beta) => (sign, .two_alpha_beta)
  | (sign, .two_alpha_beta) => (sign, .alpha_add_beta)
  | (sign, .three_alpha_beta) => (sign, .beta)
  | (sign, .three_alpha_two_beta) => (sign, .three_alpha_two_beta)

def simpleReflectionTwo : SignedPositiveRoot → SignedPositiveRoot
  | (sign, .alpha) => (sign, .alpha_add_beta)
  | (sign, .beta) => (!sign, .beta)
  | (sign, .alpha_add_beta) => (sign, .alpha)
  | (sign, .two_alpha_beta) => (sign, .two_alpha_beta)
  | (sign, .three_alpha_beta) => (sign, .three_alpha_two_beta)
  | (sign, .three_alpha_two_beta) => (sign, .three_alpha_beta)

theorem simpleReflectionOne_involutive (r : SignedPositiveRoot) :
    simpleReflectionOne (simpleReflectionOne r) = r := by
  cases r with
  | mk sign α => cases sign <;> cases α <;> rfl

theorem simpleReflectionTwo_involutive (r : SignedPositiveRoot) :
    simpleReflectionTwo (simpleReflectionTwo r) = r := by
  cases r with
  | mk sign α => cases sign <;> cases α <;> rfl

theorem simpleReflectionOne_coordinate (r : SignedPositiveRoot) :
    signedRootCoordinates (simpleReflectionOne r) =
      s1 (signedRootCoordinates r) := by
  cases r with
  | mk sign α => cases sign <;> cases α <;>
      simp [simpleReflectionOne, signedRootCoordinates, rootCoordinates,
        negPair, s1]

theorem simpleReflectionTwo_coordinate (r : SignedPositiveRoot) :
    signedRootCoordinates (simpleReflectionTwo r) =
      s2 (signedRootCoordinates r) := by
  cases r with
  | mk sign α => cases sign <;> cases α <;>
      simp [simpleReflectionTwo, signedRootCoordinates, rootCoordinates,
        negPair, s2]

/-- Apply a finite word in the two simple reflections.  `true` denotes the
first reflection and `false` the second. -/
def simpleWordAction : List Bool → SignedPositiveRoot → SignedPositiveRoot
  | [], r => r
  | bit :: word, r =>
      simpleWordAction word
        (if bit then simpleReflectionOne r else simpleReflectionTwo r)

theorem simpleWordAction_coordinate
    (word : List Bool) (r : SignedPositiveRoot) :
    signedRootCoordinates (simpleWordAction word r) =
      (word.foldl (fun v bit =>
        if bit then s1 v else s2 v) (signedRootCoordinates r)) := by
  induction word generalizing r with
  | nil => rfl
  | cons bit word ih =>
      simp only [simpleWordAction, List.foldl_cons]
      by_cases hbit : bit
      · simp [hbit, simpleReflectionOne_coordinate, ih]
      · simp [hbit, simpleReflectionTwo_coordinate, ih]

/-- Positive roots sent to the negative half by a finite simple-reflection
word.  This is the genuine inversion set for the word action above. -/
def wordInversionRoots (word : List Bool) : Finset G2PositiveRoot :=
  Finset.univ.filter (fun α =>
    (simpleWordAction word (true, α)).1 = false)

theorem mem_wordInversionRoots_iff (word : List Bool) (α : G2PositiveRoot) :
    α ∈ wordInversionRoots word ↔
      (simpleWordAction word (true, α)).1 = false := by
  simp [wordInversionRoots]

theorem wordInversionRoots_single_one_card :
    (wordInversionRoots [true]).card = 1 := by
  decide

theorem wordInversionRoots_single_zero_card :
    (wordInversionRoots [false]).card = 1 := by
  decide

theorem wordInversionRoots_two_letter_card :
    (wordInversionRoots [true, false]).card = 2 := by
  decide

end InfoGeometry.Algebra.Zorn.G2SignedRootReflections
