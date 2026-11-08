import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Nuclear.Praseodymium134

open Real

/-!
# Finite scalar model for a proposed nuclear-chirality readout

This file defines a coordinate scalar triple product and proves that its
weighted value vanishes when two input vectors are proportional. The names
`134` and the spin labels are model labels only: no empirical data, nuclear
Hamiltonian, torsion, Nieh-Yan invariant, or physical symmetry restoration
is derived here.
-/
abbrev Vec3 := Fin 3 → ℝ

def cross_product (u v : Vec3) : Vec3 :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

def dot_product (u v : Vec3) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def scalar_triple_readout (ω j_p j_n : Vec3) : ℝ :=
  dot_product ω (cross_product j_p j_n)

structure EmergentSpacetime where
  omega : Vec3
  j_p : Vec3
  j_n : Vec3
  G_eff : ℝ

def weighted_scalar_readout (S : EmergentSpacetime) : ℝ :=
  S.G_eff * scalar_triple_readout S.omega S.j_p S.j_n

/-- Proportional current inputs make this scalar triple-product readout zero. -/
theorem collinear_inputs_zero_weighted_readout (S : EmergentSpacetime) (c : ℝ)
    (h_collinear : ∀ i, S.j_n i = c * S.j_p i) :
    weighted_scalar_readout S = 0 := by
  dsimp [weighted_scalar_readout, scalar_triple_readout, dot_product, cross_product]
  have h0 : S.j_n 0 = c * S.j_p 0 := h_collinear 0
  have h1 : S.j_n 1 = c * S.j_p 1 := h_collinear 1
  have h2 : S.j_n 2 = c * S.j_p 2 := h_collinear 2
  rw [h0, h1, h2]
  ring


/-!
# Candidate input functions
The following functions are abstract real-vector inputs indexed by a real
parameter. Their labels do not assert measured nuclear kinematics.
-/

section PraseodymiumKinematics

/-- The collective spin of the nucleus (in units of ℏ). -/
abbrev Spin := ℝ

-- Candidate vector-valued inputs indexed by a parameter called spin.
variable (j_p : Spin → Vec3)
variable (j_n : Spin → Vec3)
variable (omega_coll : Spin → Vec3)
variable (G_effective : ℝ)

/-- Candidate model inputs evaluated at a real parameter labelled by spin. -/
def Pr134_State (I : Spin) : EmergentSpacetime :=
  ⟨omega_coll I, j_p I, j_n I, G_effective⟩

/-- A candidate non-collinearity predicate at parameter `14`. -/
def candidateNoncollinearAt14 (j_p j_n : Spin → Vec3) : Prop :=
  cross_product (j_p 14) (j_n 14) ≠ ![0, 0, 0]

/-- A candidate proportionality predicate at parameter `16`. -/
def candidateAlignedAt16 (j_p j_n : Spin → Vec3) (c : ℝ) : Prop :=
  ∀ i, j_n 16 i = c * j_p 16 i

end PraseodymiumKinematics


/-!
# Conditional scalar-readout consequence
This is a conditional calculation for the candidate input functions above;
it supplies neither empirical alignment data nor a symmetry-restoration
result for a nuclear Hamiltonian.
-/

section TheMasterTheorem

/-- At the model label `16`, the stated alignment hypothesis forces the
    weighted scalar readout to vanish. No empirical or spectral conclusion
    is included. -/
theorem pr134_weighted_readout_zero_of_alignment_at_16
    (j_p j_n : Spin → Vec3)
    (omega_coll : Spin → Vec3)
    (G_eff : ℝ)
    (c : ℝ)
    (h_aligned : candidateAlignedAt16 j_p j_n c) :
    weighted_scalar_readout (Pr134_State j_p j_n omega_coll G_eff 16) = 0 := by
  -- The candidate input record at parameter 16.
  let S_16 := Pr134_State j_p j_n omega_coll G_eff 16
  
  -- Apply the finite scalar identity under the stated proportionality input.
  exact collinear_inputs_zero_weighted_readout S_16 c h_aligned

end TheMasterTheorem

end InfoGeometry.Nuclear.Praseodymium134
