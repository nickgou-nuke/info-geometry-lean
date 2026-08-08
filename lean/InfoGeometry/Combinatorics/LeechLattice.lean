import InfoGeometry.Combinatorics.GolayConstructionA
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt

/-!
# The Leech lattice numerator construction

This file restores the genuine Golay congruence construction that was hidden
behind the former numerical `LeechLatticeNormData` property.

We first construct the integral numerator set.  Its conventional real
realization is obtained by multiplying every coordinate by `1 / sqrt 8`.
Using the extended binary Golay code `C`, the two numerator branches are

* `2 c + 4 z`, with `sum z` even;
* `1 + 2 c + 4 z`, with `sum z` odd.

Here a binary codeword is lifted coordinatewise to `{0,1} ⊂ Z`.  This is an
equivalent standard Construction-B/neighbor presentation of the Leech
lattice.  It is strictly stronger than ordinary Construction A: the parity
condition removes the roots of the naive code lattice.

The minimum-norm, integrality, and unimodularity theorems are separate
obligations.  They are not represented by evidence fields in this owner.
-/

namespace InfoGeometry.Combinatorics.LeechLattice

open InfoGeometry.Combinatorics.ExtendedBinaryGolay
open InfoGeometry.Combinatorics.GolayConstructionA

/-- Canonical integral representative of a binary scalar. -/
def bitLift (b : F₂) : ℤ :=
  if b = 0 then 0 else 1

@[simp]
theorem bitLift_zero :
    bitLift 0 = 0 := by
  simp [bitLift]

@[simp]
theorem bitLift_one :
    bitLift 1 = 1 := by
  simp [bitLift]

/-- Coordinatewise `{0,1}` lift of a binary word. -/
def wordLift (c : Word24) : IntegerWord24 :=
  fun i => bitLift (c i)

@[simp]
theorem wordLift_zero :
    wordLift 0 = 0 := by
  funext i
  simp [wordLift]

@[simp]
theorem wordLift_one :
    wordLift 1 = 1 := by
  funext i
  simp [wordLift]

/-- Sum of the integral coordinates of a length-24 word. -/
def coordinateSum (z : IntegerWord24) : ℤ :=
  ∑ i, z i

@[simp]
theorem coordinateSum_zero :
    coordinateSum 0 = 0 := by
  simp [coordinateSum]

/-- Even numerator branch `2 c + 4 z`. -/
def evenNumerator (c : Word24) (z : IntegerWord24) : IntegerWord24 :=
  fun i => 2 * wordLift c i + 4 * z i

/-- Odd numerator branch `1 + 2 c + 4 z`. -/
def oddNumerator (c : Word24) (z : IntegerWord24) : IntegerWord24 :=
  fun i => 1 + 2 * wordLift c i + 4 * z i

/-- Native even branch of the Golay neighbor construction. -/
def evenBranch : Set IntegerWord24 :=
  {a | ∃ c ∈ codeSubmodule, ∃ z, Even (coordinateSum z) ∧
      a = evenNumerator c z}

/-- Native odd branch of the Golay neighbor construction. -/
def oddBranch : Set IntegerWord24 :=
  {a | ∃ c ∈ codeSubmodule, ∃ z, Odd (coordinateSum z) ∧
      a = oddNumerator c z}

/--
Integral numerator carrier of the Leech lattice.  The geometric lattice is
its image under coordinatewise multiplication by `1 / sqrt 8`.
-/
def numerator : Set IntegerWord24 :=
  evenBranch ∪ oddBranch

theorem evenNumerator_mem
    {c : Word24} (hc : c ∈ codeSubmodule)
    {z : IntegerWord24} (hz : Even (coordinateSum z)) :
    evenNumerator c z ∈ numerator := by
  left
  exact ⟨c, hc, z, hz, rfl⟩

theorem oddNumerator_mem
    {c : Word24} (hc : c ∈ codeSubmodule)
    {z : IntegerWord24} (hz : Odd (coordinateSum z)) :
    oddNumerator c z ∈ numerator := by
  right
  exact ⟨c, hc, z, hz, rfl⟩

/-- The Leech numerator carrier contains the origin. -/
theorem zero_mem_numerator :
    (0 : IntegerWord24) ∈ numerator := by
  have hz : Even (coordinateSum (0 : IntegerWord24)) := by
    simp
  simpa [evenNumerator] using
    evenNumerator_mem (c := (0 : Word24)) codeSubmodule.zero_mem hz

/-- Every even-branch numerator has even coordinates. -/
theorem evenNumerator_coordinate_even
    (c : Word24) (z : IntegerWord24) (i : Fin 24) :
    Even (evenNumerator c z i) := by
  refine ⟨wordLift c i + 2 * z i, ?_⟩
  simp [evenNumerator]
  ring

/-- Every odd-branch numerator has odd coordinates. -/
theorem oddNumerator_coordinate_odd
    (c : Word24) (z : IntegerWord24) (i : Fin 24) :
    Odd (oddNumerator c z i) := by
  refine ⟨wordLift c i + 2 * z i, ?_⟩
  simp [oddNumerator]
  ring

/-- All coordinates of an integral word have the same parity. -/
def HasCommonParity (a : IntegerWord24) : Prop :=
  (∀ i, Even (a i)) ∨ (∀ i, Odd (a i))

/--
The common-parity condition is derived from membership in the Leech
numerator carrier; it is not stored as a Boolean marker.
-/
theorem hasCommonParity_of_mem
    {a : IntegerWord24} (ha : a ∈ numerator) :
    HasCommonParity a := by
  rcases ha with ha | ha
  · rcases ha with ⟨c, hc, z, hz, rfl⟩
    exact Or.inl (evenNumerator_coordinate_even c z)
  · rcases ha with ⟨c, hc, z, hz, rfl⟩
    exact Or.inr (oddNumerator_coordinate_odd c z)

/-- Conventional coordinatewise real scaling by `1 / sqrt 8`. -/
noncomputable def scaledRealization
    (a : IntegerWord24) : Fin 24 → ℝ :=
  fun i => (a i : ℝ) / Real.sqrt 8

/-- Integral squared-norm numerator used before the `1 / sqrt 8` scaling. -/
def normSqNumerator (a : IntegerWord24) : ℤ :=
  ∑ i, a i * a i

@[simp]
theorem normSqNumerator_zero :
    normSqNumerator 0 = 0 := by
  simp [normSqNumerator]

/--
Squared Euclidean norm of the scaled realization, expressed by the integral
numerator.  This is the normalization bridge needed by the future rootlessness
and minimum-norm proof.
-/
theorem scaledRealization_normSq (a : IntegerWord24) :
    ∑ i, scaledRealization a i * scaledRealization a i =
      (normSqNumerator a : ℝ) / 8 := by
  simp only [scaledRealization, normSqNumerator, Int.cast_sum, Int.cast_mul]
  calc
    (∑ i, (a i : ℝ) / Real.sqrt 8 * ((a i : ℝ) / Real.sqrt 8)) =
        ∑ i, ((a i : ℝ) * (a i : ℝ)) / 8 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_mul_div_comm]
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    _ = (∑ i, (a i : ℝ) * (a i : ℝ)) / 8 := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]

end InfoGeometry.Combinatorics.LeechLattice
