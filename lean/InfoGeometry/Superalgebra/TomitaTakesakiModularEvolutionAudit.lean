/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.TomitaTakesakiModularEvolution

/-!
# Audit Module for Sections 143 and 144: Tomita-Takesaki Modular Evolution
Target: `InfoGeometry/Superalgebra/TomitaTakesakiModularEvolutionAudit.lean`

Provides concrete integer (`ℤ`) evaluations and checks by `decide`.
-/

namespace InfoGeometry.Superalgebra.TomitaTakesakiAudit

open InfoGeometry.Superalgebra.TomitaTakesaki

/-- Concrete integer evaluation of the modular blue-shift for `(c, s) = (2, 1)` (`(c + s)^2 = 9`). -/
theorem audit_quark_blue_shift_int :
    SplitOctonion.tomitaTakesakiFlow (2 : ℤ) (1 : ℤ)
      (SplitOctonion.quark canonicalColorVec3Int) =
    SplitOctonion.quark ⟨9, 18, 27⟩ := by decide

/-- Concrete integer evaluation of the modular red-shift for `(c, s) = (2, 1)` (`(c - s)^2 = 1`). -/
theorem audit_antiquark_red_shift_int :
    SplitOctonion.tomitaTakesakiFlow (2 : ℤ) (1 : ℤ)
      (SplitOctonion.antiquark canonicalColorVec3Int) =
    SplitOctonion.antiquark ⟨1, 2, 3⟩ := by decide

/-- Concrete integer KMS pairing invariance at the trivial hyperbolic point `(c, s) = (1, 0)`. -/
theorem audit_kms_invariant_trivial_point_int :
    SplitOctonion.anticommutator
      (SplitOctonion.tomitaTakesakiFlow (1 : ℤ) (0 : ℤ) (SplitOctonion.quark canonicalColorVec3Int))
      (SplitOctonion.tomitaTakesakiFlow (1 : ℤ) (0 : ℤ) (SplitOctonion.antiquark ⟨1, 0, -1⟩)) =
    SplitOctonion.scale (-2 : ℤ) SplitOctonion.one := by decide

/-- Concrete integer evaluation of the modular Hamiltonian for `I_surp = 5`. -/
theorem audit_modular_hamiltonian_int :
    SplitOctonion.modularHamiltonian (5 : ℤ) =
    ⟨5, ColorVec3.zero, ColorVec3.zero, -5⟩ := by decide

/-- Concrete integer non-commutativity of split-octonion multiplication. -/
theorem audit_split_octonion_noncommutative_int :
    SplitOctonion.mul octonionBasisU1Int octonionBasisU2Int ≠
      SplitOctonion.mul octonionBasisU2Int octonionBasisU1Int := by decide

end InfoGeometry.Superalgebra.TomitaTakesakiAudit
