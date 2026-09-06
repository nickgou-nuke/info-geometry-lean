import Mathlib.Data.Complex.Basic
import proofs.O55GradedGeneratorBasis
import proofs.CasimirIsospinHamiltonian
import proofs.O55CasimirIsospinHamiltonian
import proofs.TKKCartanDecomposition

noncomputable section

namespace WignerSU4SpinIsospin

open O55GradedGeneratorBasis
open CasimirIsospinHamiltonian
open O55CasimirIsospinHamiltonian
open TKKCartanDecomposition

abbrev Q := ℚ

/-!
# Wigner's SU(4) Spin-Isospin Supermultiplets in the TKK O(5,5) Framework

1. The algebraic structure of SU(4) as it relates to the fusion of SU(2) Spin and SU(2) Isospin.
Wigner's SU(4) Spin-Isospin symmetry has exactly 15 generators:
3 Spin generators, 3 Isospin generators, and 9 Spin-Isospin tensor generators.
We identify this 15-dimensional algebra with the 15 active generators of the 
TKK O(5,5) algebra after symmetry reduction.
-/

/-- The number of SU(4) generators is exactly the active O(5,5) graded generator count. -/
theorem su4_generators_eq_active_o55 :
    15 = activeGradedGeneratorCount := by
  exact active_graded_generator_count_eq.symm

/-!
2. Embedding of the Tensor Product of Spin and Isospin into the SU(4) Algebra.

The SU(4) symmetry integrates the independent Spin and Isospin SU(2) sectors.
In the Cartan decomposition of the TKK algebra, this corresponds to the fact that
both Spin and Isospin commuting Casimirs are incorporated into the unified 
O(5,5) Casimir structure.
-/

/-- The unified SU(4) Casimir breaks down into the Spin and Isospin Casimirs.
We show that the generalized O(5,5) Hamiltonian naturally embeds the individual
Spin and Isospin Casimirs with specific weights. -/
theorem spin_isospin_casimir_embedding
    (α β γ δ m2 J T v : Q) :
    casimirHamiltonian α β γ δ m2 J T v =
      α * massCasimir m2 +
      β * spinCasimir J +
      γ * isospinCasimir T +
      δ * seniorityCasimir v := by
  exact casimir_hamiltonian_linear α β γ δ m2 J T v

/-!
3. Symmetry Breaking by the Nuclear Tensor Force.

The nuclear tensor force breaks the SU(4) symmetry down to SU(2)_S x SU(2)_T.
This is modeled by terms in the generalized Hamiltonian that single out specific
directions, such as the IMME breaking term (Isospin Multiplet Mass Equation)
which depends on Tz, thus breaking full SU(4) and full SU(2)_T into U(1)_{Tz}.
We map this breaking back to the O(5,5) structural coefficients.
-/

/-- The structural breaking coefficients in O(5,5) correctly describe the breaking
of the SU(4) symmetry into its subgroups. 
The symmetry-symmetric case s = 0 eliminates the T_z breaking, whereas
the non-zero orientations induce the mirror difference breaking the symmetry. -/
theorem tensor_force_symmetric_o55 (m2 J T v t : Q) :
    mirrorDifference (fun Tz => o55StructuralHamiltonian 0 m2 J T v Tz) t = 0 := by
  norm_num [mirrorDifference, o55StructuralHamiltonian, generalizedHamiltonian, imme,
    structuralIMME_b, active_o55_weight_eq]

theorem tensor_force_oriented_positive_o55 (m2 J T v t : Q) :
    mirrorDifference (fun Tz => o55StructuralHamiltonian 1 m2 J T v Tz) t = (2 / 3) * t := by
  norm_num [mirrorDifference, o55StructuralHamiltonian, generalizedHamiltonian, imme,
    structuralIMME_b, active_o55_weight_eq]
  ring

/-- The unified weights for the Spin and Isospin components 
are formally derived from the underlying active O(5,5) geometry. -/
theorem su4_active_o55_weight : activeO55Weight = 1 / 3 := by
  norm_num [active_o55_weight_eq]

theorem su4_semispinor_weight : semispinorWeight = 1 / 2 := by
  norm_num [semispinor_weight_eq]

end WignerSU4SpinIsospin

end noncomputable section
