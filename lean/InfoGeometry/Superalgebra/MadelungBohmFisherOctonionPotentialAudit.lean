/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.MadelungBohmFisherOctonionPotential

/-!
# Audit Module for Sections 141 and 142: Vector Madelung Fluid and Bohm Quantum Potential
Target: `InfoGeometry/Superalgebra/MadelungBohmFisherOctonionPotentialAudit.lean`

Provides concrete integer (`ℤ`) evaluations and non-degeneracy checks by `decide`.
-/

namespace InfoGeometry.Superalgebra.MadelungBohmOctonionAudit

open InfoGeometry.Superalgebra.MadelungBohmOctonion

/-- Concrete integer evaluation of the Madelung vortex Jacobiator on standard basis vectors. -/
theorem audit_madelung_vortex_jacobiator_int :
    SplitOctonion.jacobiator
      (SplitOctonion.quark (⟨1, 0, 0⟩ : ColorVec3 ℤ))
      (SplitOctonion.quark (⟨0, 1, 0⟩ : ColorVec3 ℤ))
      (SplitOctonion.quark (⟨0, 0, 1⟩ : ColorVec3 ℤ)) =
    SplitOctonion.scale (-6 : ℤ) SplitOctonion.paraSymplecticK0 := by decide

/-- Concrete non-vanishing of the Madelung vortex Jacobiator over `ℤ`. -/
theorem audit_madelung_vortex_nonzero_int :
    SplitOctonion.jacobiator
      (SplitOctonion.quark canonicalMadelungStateInt.u_S)
      (SplitOctonion.quark canonicalMadelungStateInt.grad_a)
      (SplitOctonion.quark canonicalMadelungStateInt.grad_b) ≠
    SplitOctonion.zero := by decide

/-- Concrete integer evaluation of the Bohm Dirac gradient square on `⟨1, 2, 3⟩` (`normSq = 14`). -/
theorem audit_bohm_dirac_laplacian_central_int :
    SplitOctonion.mul
      (SplitOctonion.diracGradient canonicalColorVec3Int)
      (SplitOctonion.diracGradient canonicalColorVec3Int) =
    SplitOctonion.scale (14 : ℤ) SplitOctonion.one := by decide

/-- Concrete integer non-commutativity of split-octonion multiplication. -/
theorem audit_split_octonion_noncommutative_int :
    SplitOctonion.mul octonionBasisU1Int octonionBasisU2Int ≠
      SplitOctonion.mul octonionBasisU2Int octonionBasisU1Int := by decide

/-- Concrete integer non-associativity of split-octonion multiplication. -/
theorem audit_split_octonion_nonassociative_int :
    SplitOctonion.mul
      (SplitOctonion.mul
        (SplitOctonion.quark (⟨1, 0, 0⟩ : ColorVec3 ℤ))
        (SplitOctonion.quark (⟨0, 1, 0⟩ : ColorVec3 ℤ)))
      (SplitOctonion.quark (⟨0, 0, 1⟩ : ColorVec3 ℤ)) ≠
    SplitOctonion.mul
      (SplitOctonion.quark (⟨1, 0, 0⟩ : ColorVec3 ℤ))
      (SplitOctonion.mul
        (SplitOctonion.quark (⟨0, 1, 0⟩ : ColorVec3 ℤ))
        (SplitOctonion.quark (⟨0, 0, 1⟩ : ColorVec3 ℤ))) := by decide

end InfoGeometry.Superalgebra.MadelungBohmOctonionAudit
