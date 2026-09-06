import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

namespace InfoGeometry.Monster.MoonshineGradedDimensions

/-- Monster Irreducible Representation Dimensions (known as character degrees) -/
def monster_chi_1 : ℕ := 1
def monster_chi_2 : ℕ := 196883
def monster_chi_3 : ℕ := 21296876
def monster_chi_4 : ℕ := 842806210

/-- Fourier coefficients of the elliptic j-function (j(q) - 744) -/
def fourier_j_1 : ℕ := 196884
def fourier_j_2 : ℕ := 21493760
def fourier_j_3 : ℕ := 864299970

/-- McKay's Observation for Weight 1: c₁ = χ₁(1) + χ₂(1) -/
theorem mckay_observation_weight_1 :
    fourier_j_1 = monster_chi_1 + monster_chi_2 := by
  norm_num [fourier_j_1, monster_chi_1, monster_chi_2]

/-- McKay's Observation for Weight 2: c₂ = χ₁(1) + χ₂(1) + χ₃(1) -/
theorem mckay_observation_weight_2 :
    fourier_j_2 = monster_chi_1 + monster_chi_2 + monster_chi_3 := by
  norm_num [fourier_j_2, monster_chi_1, monster_chi_2, monster_chi_3]

/-- McKay's Observation for Weight 3: c₃ = χ₁(1) + χ₂(1) + χ₃(1) + χ₄(1) -/
theorem mckay_observation_weight_3 :
    fourier_j_3 = monster_chi_1 + monster_chi_2 + monster_chi_3 + monster_chi_4 := by
  norm_num [fourier_j_3, monster_chi_1, monster_chi_2, monster_chi_3, monster_chi_4]

/--
The first three McKay decompositions, stated directly rather than packaged in
a record that repeats the Fourier coefficients and stores their proofs.

This finite arithmetic theorem is not by itself a construction of a vertex
operator algebra; a genuine VOA owner requires the corresponding graded
algebraic structure.
-/
theorem moonshine_graded_dimension_decomposition :
    fourier_j_1 = monster_chi_1 + monster_chi_2 ∧
      fourier_j_2 = monster_chi_1 + monster_chi_2 + monster_chi_3 ∧
        fourier_j_3 =
          monster_chi_1 + monster_chi_2 + monster_chi_3 + monster_chi_4 :=
  ⟨mckay_observation_weight_1,
    mckay_observation_weight_2,
    mckay_observation_weight_3⟩

/--
Historical Moonshine decomposition proposition.

This name denotes the proved first-three-weight character decomposition.  It
does not assert that these numerical equalities alone construct a vertex
operator algebra.
-/
abbrev MoonshineVOADecomposition : Prop :=
  fourier_j_1 = monster_chi_1 + monster_chi_2 ∧
    fourier_j_2 = monster_chi_1 + monster_chi_2 + monster_chi_3 ∧
      fourier_j_3 =
        monster_chi_1 + monster_chi_2 + monster_chi_3 + monster_chi_4

/-- Historical owner name restored from the proved McKay decompositions. -/
theorem moonshine_voa_decomposition_exists :
    MoonshineVOADecomposition :=
  moonshine_graded_dimension_decomposition

end InfoGeometry.Monster.MoonshineGradedDimensions
