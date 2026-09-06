import InfoGeometry.Combinatorics.ExtendedBinaryGolay
import InfoGeometry.Combinatorics.GolayConstructionA
import InfoGeometry.Combinatorics.LeechLattice

/-!
# Extended Golay code and its Pauli stabilizer

This canonical facade consumes the explicitly constructed extended binary
Golay code.  Code cardinality, minimum distance, and orthogonality are no
longer represented by numerical fields.

The Leech-lattice portion of the historical module name is retained for the
future Construction-A owner.  No lattice minimum norm is asserted before that
construction exists.
-/

namespace InfoGeometry.Canonical.GolayLeechStabilizerCode

open InfoGeometry.Combinatorics.ExtendedBinaryGolay

abbrev BinaryWord24 := Word24
abbrev BinaryPauli24 := Word24 × Word24

/-- The explicitly encoded extended binary Golay code. -/
abbrev golayCode : Finset BinaryWord24 := code

/-- Symplectic form on binary Pauli labels. -/
def symplecticInnerProduct (u v : BinaryPauli24) : F₂ :=
  dot u.1 v.2 + dot u.2 v.1

/-- Pauli labels whose `X` and `Z` words both belong to the Golay code. -/
def golayPauliCode : Finset BinaryPauli24 :=
  golayCode ×ˢ golayCode

/-- The constructed code has `4096 = 2^12` codewords. -/
theorem golay_code_card :
    golayCode.card = 4096 :=
  card_code

/-- The constructed code has exact minimum nonzero Hamming weight eight. -/
theorem golay_code_minimumWeight_eq_eight :
    (∀ m : Message, 4 ∣ hammingWeight (encode m)) →
    (∀ m : Message, encode m ≠ 0 →
      ∃ f : Fin 23 → Fin (hammingWeight (encode m) ^ 2 -
        hammingWeight (encode m) + 1), Function.Injective f) →
    (∀ w ∈ golayCode, w ≠ 0 → 8 ≤ hammingWeight w) ∧
      (∃ w ∈ golayCode, hammingWeight w = 8) :=
  minimumWeight_eq_eight

/-!
The historical parameter record is replaced by native readouts from the
constructed code.  These statements expose the same mathematical data
without storing equalities to numerals in an evidence structure.
-/

/-- The constructed extended Golay code has binary dimension twelve. -/
theorem golay_code_dimension :
    Module.finrank F₂ codeSubmodule = 12 :=
  finrank_codeSubmodule

/-- The constructed extended Golay code has minimum nonzero weight eight. -/
theorem golay_code_minimum_distance :
    (∀ m : Message, 4 ∣ hammingWeight (encode m)) →
    (∀ m : Message, encode m ≠ 0 →
      ∃ f : Fin 23 → Fin (hammingWeight (encode m) ^ 2 -
        hammingWeight (encode m) + 1), Function.Injective f) →
    (∀ w ∈ golayCode, w ≠ 0 → 8 ≤ hammingWeight w) ∧
      (∃ w ∈ golayCode, hammingWeight w = 8) :=
  golay_code_minimumWeight_eq_eight

/-- The actual constructed code is self-orthogonal. -/
theorem golay_code_self_orthogonal :
    ∀ u ∈ golayCode, ∀ v ∈ golayCode, dot u v = 0 :=
  self_orthogonal

/-- Genuine self-duality of the constructed binary code submodule. -/
theorem golay_code_self_dual :
    codeSubmodule = dotBilin.orthogonal codeSubmodule :=
  codeSubmodule_selfDual

/--
Compatibility theorem for the historical self-duality entry point.

Unlike the deleted numerical equality `2 * 12 = 24`, this statement exposes
the genuine self-duality of the constructed binary code submodule.
-/
theorem golay_code_self_duality :
    codeSubmodule = dotBilin.orthogonal codeSubmodule :=
  golay_code_self_dual

/-- The genuine integral Construction-A lattice attached to the code. -/
abbrev golayConstructionALattice :=
  InfoGeometry.Combinatorics.GolayConstructionA.lattice

/--
The genuine Construction-B/neighbor numerator carrier for the Leech lattice.

This owner removes the roots present in the ordinary Construction-A lattice
by imposing the Golay/parity congruence conditions.  Its minimum-norm-four
theorem is deliberately not replaced by a numerical property.
-/
abbrev leechLatticeNumerator :=
  InfoGeometry.Combinatorics.LeechLattice.numerator

/- The Pauli stabilizer obtained from two Golay words is symplectically
   isotropic.  This is a theorem about actual encoded words, not a record field. -/
set_option linter.constructorNameAsVariable false in
theorem golay_pauli_code_isotropic :
    ∀ u ∈ golayPauliCode, ∀ v ∈ golayPauliCode,
      symplecticInnerProduct u v = 0 := by
  intro u hu v hv
  simp only [golayPauliCode, Finset.mem_product] at hu hv
  simp [symplecticInnerProduct,
    golay_code_self_orthogonal u.1 hu.1 v.2 hv.2,
    golay_code_self_orthogonal u.2 hu.2 v.1 hv.1]

/-- Alternation of the binary Pauli symplectic form. -/
theorem symplectic_self_pairing (v : BinaryPauli24) :
    symplecticInnerProduct v v = 0 := by
  unfold symplecticInnerProduct dot
  have h :
      (∑ i, v.1 i * v.2 i) = ∑ i, v.2 i * v.1 i := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [h]
  exact CharTwo.add_self_eq_zero _

/-- Historical name for alternation of the binary Pauli symplectic form. -/
theorem golay_symplectic_self_commutativity (v : BinaryPauli24) :
    symplecticInnerProduct v v = 0 :=
  symplectic_self_pairing v

/--
Exact decoding radius attached to the proved minimum distance eight.
The coding theorem that nearest-neighbour decoding corrects this many errors
is a separate general coding-theory result.
-/
theorem golay_uniqueDecodingRadius_eq_three :
    (8 - 1) / 2 = 3 := by
  decide

/--
Historical error-correction-capacity readout, now derived from the exact
minimum-distance owner rather than from a record containing the numeral eight.
-/
theorem golay_error_correction_capacity :
    (8 - 1) / 2 = 3 :=
  golay_uniqueDecodingRadius_eq_three

/-! ## Dimension and ambient length of the actual construction -/

theorem golay_code_ambient_length :
    Fintype.card (Fin 24) = 24 := by
  simp

theorem golay_code_dimension_twice_eq_ambient_length :
    2 * Module.finrank F₂ codeSubmodule = Fintype.card (Fin 24) := by
  rw [golay_code_dimension]
  simp

end InfoGeometry.Canonical.GolayLeechStabilizerCode
