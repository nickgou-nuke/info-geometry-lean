import InfoGeometry.Canonical.ProjectiveSectorDecomposition
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

/-!
# InfoGeometry.Canonical.ProjectiveAlgebraComparison

Purified comparison bridge for the Projective-Mathlib lane. 

This file formalizes the 'Explicit Comparison' doctrine, proving that the 
repo's foundational definitions of grading and involution coincide with 
the Mathlib-standard CliffordAlgebra.involute.
-/

namespace InfoGeometry.Canonical.ProjectiveAlgebraComparison

open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Canonical.ProjectiveSplitQ11Realization
open InfoGeometry.Canonical.ProjectiveSectorDecomposition
open CliffordAlgebra

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "ProjectiveH" => ProjectiveCarrier (E := E)

/--
**COMPARISON: The Grading Automorphism**
The repo's `spectral_epsilon` is exactly the `involute` automorphism 
of the realized Mathlib Clifford algebra.
-/
theorem epsilon_is_mathlib_involute :
    (doubledRealizesCl11 (E := E)).toLinearMap.comp (CliffordAlgebra.involute (InfoGeometry.Clifford.splitQ11)).toLinearMap 
      = 
    (spectral_epsilon (E := E)).toLinearMap.comp (doubledRealizesCl11 (E := E)).toLinearMap := by
  -- Both sides are algebra automorphisms that act as -1 on the generators J and K.
  -- The RealSplitClifford definition ensures this identity on the basis.
  apply AlgEquiv.toLinearMap_injective
  apply CliffordAlgebra.algHom_ext
  intro v
  simp [doubledRealizesCl11]
  -- Both act as -1 on the vector generators by definition of the grading
  exact (InfoGeometry.Krein.spectral_epsilon_iota_eq_neg_iota (E := E) v).symm

end InfoGeometry.Canonical.ProjectiveAlgebraComparison
