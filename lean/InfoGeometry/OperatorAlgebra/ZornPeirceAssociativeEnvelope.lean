import InfoGeometry.OperatorAlgebra.CanonicalZornCircularCARProjectors

/-!
# The associative envelope of the circular Peirce readouts

The split-octonion carrier is not associative.  Its right-regular readouts,
however, are endomorphisms of the carrier and therefore live in the
associative ring `Module.End ℝ CZ`.  This file records the corresponding
native subalgebra and its CAR generators.  No associative multiplication is
added to the split-octonion carrier itself.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CanonicalZornCircularCARProjectors

abbrev PeirceAssociativeEnvelope := Subalgebra ℝ EndCZ

def peirceAssociativeEnvelope : PeirceAssociativeEnvelope :=
  Algebra.adjoin ℝ
    (Set.range creation ∪ Set.range annihilation)

theorem creation_mem_peirceAssociativeEnvelope (i : Fin 3) :
    creation i ∈ peirceAssociativeEnvelope := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_left _ (Set.mem_range_self i)

theorem annihilation_mem_peirceAssociativeEnvelope (i : Fin 3) :
    annihilation i ∈ peirceAssociativeEnvelope := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_right _ (Set.mem_range_self i)

theorem peirce_envelope_closed_under_composition
    {X Y : EndCZ}
    (hX : X ∈ peirceAssociativeEnvelope)
    (hY : Y ∈ peirceAssociativeEnvelope) :
    X * Y ∈ peirceAssociativeEnvelope := by
  exact peirceAssociativeEnvelope.mul_mem hX hY

theorem peirce_envelope_CAR (i : Fin 3) :
    annihilation i * creation i + creation i * annihilation i =
      (1 : EndCZ) := by
  exact annihilation_creation_CAR i

theorem peirce_envelope_CAR_mem (i : Fin 3) :
    annihilation i * creation i + creation i * annihilation i ∈
      peirceAssociativeEnvelope := by
  exact peirceAssociativeEnvelope.add_mem
    (peirceAssociativeEnvelope.mul_mem
      (annihilation_mem_peirceAssociativeEnvelope i)
      (creation_mem_peirceAssociativeEnvelope i))
    (peirceAssociativeEnvelope.mul_mem
      (creation_mem_peirceAssociativeEnvelope i)
      (annihilation_mem_peirceAssociativeEnvelope i))

theorem peirce_envelope_creation_square_zero (i : Fin 3) :
    creation i * creation i = 0 :=
  creation_sq_zero i

theorem peirce_envelope_annihilation_square_zero (i : Fin 3) :
    annihilation i * annihilation i = 0 :=
  annihilation_sq_zero i

end InfoGeometry.OperatorAlgebra.CanonicalZornCircularCARProjectors
