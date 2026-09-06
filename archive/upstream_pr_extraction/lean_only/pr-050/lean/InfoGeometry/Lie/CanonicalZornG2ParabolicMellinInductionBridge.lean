import InfoGeometry.Lie.CanonicalZornG2ParabolicMellinCharacterBridge

/-!
# A theorem-honest parabolic-induction interface

This file records the representation-theoretic *parameter* edge suggested by
the Langlands `P = M A N` picture.  It deliberately does not define a
reductive group, a normalized induction functor, or a generic irreducibility
theorem.  Those require substantially more representation-theoretic data than
the canonical rank-two Cartan owner currently provides.

The only concrete readout is the split-Cartan character already owned by
`CanonicalZornG2ParabolicMellinCharacterBridge`.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2ParabolicMellinInductionBridge

open InfoGeometry.Lie.CanonicalZornG2ParabolicMellinCharacterBridge
open InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
open InfoGeometry.Lie.CanonicalZornG2SplitCartanCharacter
open InfoGeometry.Lie.CanonicalZornRootSystemComparison

abbrev Cartan :=
  InfoGeometry.Lie.CanonicalZornG2ParabolicMellinCharacterBridge.Cartan

/-! ## The type-level `P = M A N` interface -/

/-- Minimal factorization data for a parabolic label.

`factor` is intentionally only a supplied multiplication/factorization map;
no bijectivity or group structure is inferred from it.  This keeps the
interface usable before a concrete reductive-group implementation exists.
-/
structure LanglandsParabolicData where
  G : Type*
  P : Type*
  M : Type*
  A : Type*
  N : Type*
  inclusion : P → G
  factor : M × A × N → P

/-- A Levi datum together with a complex split-Cartan spectral parameter.

This is the finite parameter object underlying the notation
`π_M ⊗ χ_ν`; `leviParameter` is deliberately opaque because no representation
of `M` is owned in this layer.
-/
structure InducedRepresentationParameter (LeviParameter : Type*) where
  leviParameter : LeviParameter
  spectralParameter : Fin 2 → ℂ

/-! ## The concrete A-character readout -/

/-- The A-character attached to the spectral component of an induced
parameter, evaluated in the canonical logarithmic Cartan coordinate.
-/
def inducedACharacter {LeviParameter : Type*}
    (q : InducedRepresentationParameter LeviParameter) (x : Cartan) : ℂ :=
  logarithmicACharacter q.spectralParameter x

theorem inducedACharacter_eq_parabolicReadout
    {LeviParameter : Type*}
    (q : InducedRepresentationParameter LeviParameter) (x : Cartan) :
    inducedACharacter q x =
      Complex.exp (∑ i : Fin 2,
        q.spectralParameter i *
          (simpleWeightOnCartan i x : ℂ)) := by
  rfl

theorem inducedACharacter_eq_mellin
    {LeviParameter : Type*}
    (q : InducedRepresentationParameter LeviParameter) (x : Cartan) :
    inducedACharacter q x =
      canonicalG2CartanMellinCharacter
        (fun i => -q.spectralParameter i) x := by
  simpa [inducedACharacter] using
    (logarithmicACharacter_eq_mellin_neg q.spectralParameter x)

theorem inducedACharacter_parameter_dictionary
    {LeviParameter : Type*}
    (q : InducedRepresentationParameter LeviParameter) (x : Cartan) :
    inducedACharacter
        { leviParameter := q.leviParameter
          spectralParameter := fun i => -q.spectralParameter i } x =
      canonicalG2CartanMellinCharacter q.spectralParameter x := by
  simpa [inducedACharacter] using
    (logarithmicACharacter_neg_eq_mellin q.spectralParameter x)

theorem inducedACharacter_add
    {LeviParameter : Type*}
    (q : InducedRepresentationParameter LeviParameter) (x y : Cartan) :
    inducedACharacter q (x + y) =
      inducedACharacter q x * inducedACharacter q y := by
  simpa [inducedACharacter] using
    (logarithmicACharacter_add q.spectralParameter x y)

theorem inducedACharacter_ne_zero
    {LeviParameter : Type*}
    (q : InducedRepresentationParameter LeviParameter) (x : Cartan) :
    inducedACharacter q x ≠ 0 := by
  simpa [inducedACharacter] using
    (logarithmicACharacter_ne_zero q.spectralParameter x)

end InfoGeometry.Lie.CanonicalZornG2ParabolicMellinInductionBridge
