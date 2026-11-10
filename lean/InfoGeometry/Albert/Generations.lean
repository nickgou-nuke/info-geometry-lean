import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite fermion quantum-number table

This owner records only the finite list of quantum-number labels and the
identities that follow from that list.  It does **not** identify the table
with a split-octonion or Albert-algebra decomposition: that realization needs
an explicit carrier map and is a separate theorem obligation.
-/

namespace InfoGeometry.Albert.Generations

/-- Color charges for the Standard Model fermions. -/
inductive Color where
  | singlet
  | red
  | green
  | blue
  deriving DecidableEq

/-- Finite quantum-number labels for one listed generation.  The connection
to Peirce components is not part of this owner. -/
structure FermionQuantumNumbers where
  charge : ℚ        -- electric charge
  weakIsospin : ℚ   -- T₃
  hypercharge : ℚ   -- Y
  color : Color     -- RGB singlet/triplet
  deriving DecidableEq

/-- The eight labels in the finite one-generation table. -/
def singleGenFermions : List FermionQuantumNumbers := [
  ⟨0, 1/2, -1, Color.singlet⟩,       -- ν (neutrino)
  ⟨-1, -1/2, -1, Color.singlet⟩,     -- e⁻ / μ⁻ / τ⁻
  ⟨2/3, 1/2, 1/3, Color.red⟩,        -- u_R / c_R / t_R
  ⟨2/3, 1/2, 1/3, Color.green⟩,      -- u_G / c_G / t_G
  ⟨2/3, 1/2, 1/3, Color.blue⟩,       -- u_B / c_B / t_B
  ⟨-1/3, -1/2, 1/3, Color.red⟩,      -- d_R / s_R / b_R
  ⟨-1/3, -1/2, 1/3, Color.green⟩,    -- d_G / s_G / b_G
  ⟨-1/3, -1/2, 1/3, Color.blue⟩      -- d_B / s_B / b_B
]

/-- The finite table obtained by listing three copies of the one-generation
quantum-number table.  No geometric realization is asserted here. -/
def threeGenerationsFermions : List FermionQuantumNumbers :=
  singleGenFermions ++ singleGenFermions ++ singleGenFermions

/-- Every label in the finite table satisfies the declared charge relation
`Q = T₃ + Y/2`.  This checks the quantum-number assignments entry by entry. -/
theorem single_generation_charge_relation (q : FermionQuantumNumbers)
    (hq : q ∈ singleGenFermions) :
    q.charge = q.weakIsospin + q.hypercharge / 2 := by
  simp [singleGenFermions] at hq
  rcases hq with h | h | h | h | h | h | h | h <;> subst q <;> norm_num

/-- The same charge relation holds for every entry in the three-copy table. -/
theorem three_generation_charge_relation (q : FermionQuantumNumbers)
    (hq : q ∈ threeGenerationsFermions) :
    q.charge = q.weakIsospin + q.hypercharge / 2 := by
  change q ∈ singleGenFermions ++ singleGenFermions ++ singleGenFermions at hq
  rcases List.mem_append.mp hq with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · exact single_generation_charge_relation q h1
    · exact single_generation_charge_relation q h2
  · exact single_generation_charge_relation q h3

/-- The total charge of the finite 24-entry table is zero. -/
theorem three_generations_charge_sum_zero :
    (threeGenerationsFermions.map FermionQuantumNumbers.charge).sum = 0 := by
  dsimp [threeGenerationsFermions, singleGenFermions]
  norm_num

end InfoGeometry.Albert.Generations
