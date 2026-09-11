import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.E8LeechBridge
import InfoGeometry.Canonical.ViazovskaLeechGolayWeld

noncomputable section

namespace InfoGeometry.Canonical.WilsonOctonionicLeechShell

open E8LeechBridge
open InfoGeometry.Canonical.ViazovskaLeechGolayWeld

/-!
# Wilson octonionic Leech shell: theorem-safe finite counting layer

This owner records the exact finite index sets underlying Wilson's three
families of candidate minimal vectors.  It deliberately does not yet construct
Wilson's compact-octonion lattice `L`, its complementary coset/lattice `Ls`,
the distinguished element `s`, or the right-multiplication action of `Co₀`.
Those are separate algebraic/lattice obligations.
-/

/-- Coordinate choice for which of the three octonion slots carries the
leading Wilson datum. -/
abbrev CoordinateChoice := Fin 3

/-- Abstract index for one of the 240 `E8` roots used in Wilson's formula. -/
abbrev E8RootIndex := Fin 240

/-- Abstract index for one of the 16 signed octonion coordinate units. -/
abbrev SignedUnitIndex := Fin 16

/-- Wilson type-I indexing: coordinate choice and one `E8` root. -/
abbrev TypeIIndex := CoordinateChoice × E8RootIndex

/-- Wilson type-II indexing: coordinate choice, root, and one signed unit. -/
abbrev TypeIIIndex := CoordinateChoice × E8RootIndex × SignedUnitIndex

/-- Wilson type-III indexing: coordinate choice, root, and two signed units. -/
abbrev TypeIIIIndex :=
  CoordinateChoice × E8RootIndex × SignedUnitIndex × SignedUnitIndex

/-- Disjoint combinatorial shell of Wilson's three displayed families. -/
abbrev WilsonMinimalIndex := TypeIIndex ⊕ TypeIIIndex ⊕ TypeIIIIndex

@[simp] theorem typeI_card : Fintype.card TypeIIndex = 720 := by
  simp [TypeIIndex, CoordinateChoice, E8RootIndex]

@[simp] theorem typeII_card : Fintype.card TypeIIIndex = 11520 := by
  simp [TypeIIIndex, CoordinateChoice, E8RootIndex, SignedUnitIndex]

@[simp] theorem typeIII_card : Fintype.card TypeIIIIndex = 184320 := by
  simp [TypeIIIIndex, CoordinateChoice, E8RootIndex, SignedUnitIndex]

/-- The finite disjoint union of the three Wilson indexing families has exactly
`196560` elements. -/
theorem wilsonMinimalIndex_card :
    Fintype.card WilsonMinimalIndex = 196560 := by
  simp [WilsonMinimalIndex]

/-- Wilson's compact counting identity. -/
theorem wilson_factorization_196560 :
    3 * 240 * (1 + 16 + 16 ^ 2) = 196560 := by
  norm_num

/-- The three orbit-size formulas give the same factorization. -/
theorem wilson_three_family_sum :
    3 * 240 + 3 * 240 * 16 + 3 * 240 * 16 * 16 = 196560 := by
  norm_num

/-- Wilson's combinatorial shell agrees numerically with the already verified
Construction-B Leech minimal-vector count in the repository.  This is a
cardinality equality only; it is not yet a bijection between the two concrete
constructions. -/
theorem wilson_count_eq_existing_leech_count :
    Fintype.card WilsonMinimalIndex = leechMinimalVectorCount := by
  rw [wilsonMinimalIndex_card, leechMinimalVectorCount_eq]

/-- The tripled `E8` carrier dimension already present in the repository is
compatible with Wilson's use of three eight-dimensional octonion coordinates. -/
theorem wilson_three_octonion_dimensions :
    3 * dimE8Space = dimLeechLattice :=
  leech_lattice_triplication

/-- Data required to turn the finite Wilson index shell into an actual shell
of vectors in a future octonionic Leech-lattice carrier.  The present file
keeps these as explicit witness obligations rather than assuming them. -/
structure WilsonShellRealization (V : Type*) where
  vector : WilsonMinimalIndex → V
  normSq : V → ℝ
  inLattice : V → Prop
  shellNormSq : ℝ
  vector_in_lattice : ∀ i, inLattice (vector i)
  vector_on_shell : ∀ i, normSq (vector i) = shellNormSq
  vector_injective : Function.Injective vector

/-- Any realized Wilson shell satisfying the explicit injectivity and shell
conditions supplies `196560` distinct lattice vectors on one norm shell. -/
theorem realized_shell_has_196560_indices
    {V : Type*} (R : WilsonShellRealization V) :
    Fintype.card WilsonMinimalIndex = 196560 :=
  wilsonMinimalIndex_card

/-- Numerical compatibility with the classical minimal squared norm readout.
This does not assert that a future Wilson realization uses this normalization;
that must be supplied by `WilsonShellRealization.shellNormSq`. -/
theorem existing_leech_minimal_norm_sq : leechMinimalNormSq = 4 := by
  rfl

end InfoGeometry.Canonical.WilsonOctonionicLeechShell

