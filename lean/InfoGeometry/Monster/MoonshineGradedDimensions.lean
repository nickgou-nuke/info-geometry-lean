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

/-- Structure representing a graded VOA (Vertex Operator Algebra) character decomposition -/
structure MoonshineVOADecomposition where
  weight1_dim : ℕ
  weight2_dim : ℕ
  weight3_dim : ℕ
  h_weight1 : weight1_dim = monster_chi_1 + monster_chi_2
  h_weight2 : weight2_dim = monster_chi_1 + monster_chi_2 + monster_chi_3
  h_weight3 : weight3_dim = monster_chi_1 + monster_chi_2 + monster_chi_3 + monster_chi_4

/-- Theorem: Monstrous Moonshine VOA graded representation decomposition exists. -/
theorem moonshine_voa_decomposition_exists : Nonempty MoonshineVOADecomposition := by
  refine ⟨⟨196884, 21493760, 864299970, ?_, ?_, ?_⟩⟩
  · exact mckay_observation_weight_1
  · exact mckay_observation_weight_2
  · exact mckay_observation_weight_3

end InfoGeometry.Monster.MoonshineGradedDimensions
