import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import InfoGeometry.External.Virasoro.HeisenbergAlgebra

/-!
# Level Separation: The Finite Atom Is Not the Heisenberg Algebra

This file proves the basic dimension obstruction separating the finite
Tomita-Krein / split-quaternion atom from the infinite Heisenberg current
algebra.

The result is intentionally modest and categorical: the finite atom can feed a
mode construction, but it is not isomorphic to the completed current algebra.
-/

namespace InfoGeometry.Canonical.LevelSeparationNoIso

open VirasoroProject

/-- The finite local atom, represented by the real `2 × 2` matrix algebra. -/
abbrev FiniteTomitaKreinAtom : Type :=
  Matrix (Fin 2) (Fin 2) ℝ

/--
The underlying free real vector-space carrier with one central generator and
integer-labeled current generators.

`none` is the central `K`; `some n` is the mode generator `a_n`.
-/
abbrev HeisenbergFreeCarrier : Type :=
  Option ℤ →₀ ℝ

/-- The finite atom has real Hamel dimension `4`. -/
theorem finiteTomitaKreinAtom_finrank :
    Module.finrank ℝ FiniteTomitaKreinAtom = 4 := by
  simp [FiniteTomitaKreinAtom, Module.finrank_matrix, Module.finrank_self]

/-- The free Heisenberg carrier is not finite-dimensional over `ℝ`. -/
theorem heisenbergFreeCarrier_not_finiteDimensional :
    ¬ FiniteDimensional ℝ HeisenbergFreeCarrier := by
  intro h
  letI : FiniteDimensional ℝ HeisenbergFreeCarrier := h
  haveI : Fintype (Option ℤ) :=
    FiniteDimensional.fintypeBasisIndex
      (Finsupp.basisSingleOne : Module.Basis (Option ℤ) ℝ HeisenbergFreeCarrier)
  exact Fintype.false (α := Option ℤ) inferInstance

/--
The actual external Heisenberg algebra is not finite-dimensional over `ℝ`.

This uses its canonical basis `HeisenbergAlgebra.basisJK`, indexed by
`Option ℤ`.
-/
theorem heisenbergAlgebra_not_finiteDimensional :
    ¬ FiniteDimensional ℝ (HeisenbergAlgebra ℝ) := by
  intro h
  letI : FiniteDimensional ℝ (HeisenbergAlgebra ℝ) := h
  haveI : Fintype (Option ℤ) :=
    FiniteDimensional.fintypeBasisIndex (HeisenbergAlgebra.basisJK ℝ)
  exact Fintype.false (α := Option ℤ) inferInstance

/-- There is no real-linear equivalence from the finite atom to the free Heisenberg carrier. -/
theorem finiteAtom_not_linearEquiv_heisenbergFreeCarrier :
    ¬ Nonempty (FiniteTomitaKreinAtom ≃ₗ[ℝ] HeisenbergFreeCarrier) := by
  rintro ⟨e⟩
  exact heisenbergFreeCarrier_not_finiteDimensional e.finiteDimensional

/-- There is no real-linear equivalence from the finite atom to the external Heisenberg algebra. -/
theorem finiteAtom_not_linearEquiv_heisenbergAlgebra :
    ¬ Nonempty (FiniteTomitaKreinAtom ≃ₗ[ℝ] HeisenbergAlgebra ℝ) := by
  rintro ⟨e⟩
  exact heisenbergAlgebra_not_finiteDimensional e.finiteDimensional

/--
There is no Lie-algebra equivalence from the commutator Lie algebra of the
finite atom to the external Heisenberg Lie algebra.
-/
theorem finiteAtom_not_lieEquiv_heisenbergAlgebra :
    ¬ Nonempty (FiniteTomitaKreinAtom ≃ₗ⁅ℝ⁆ HeisenbergAlgebra ℝ) := by
  rintro ⟨e⟩
  exact finiteAtom_not_linearEquiv_heisenbergAlgebra ⟨e.toLinearEquiv⟩

end InfoGeometry.Canonical.LevelSeparationNoIso
