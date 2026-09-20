import InfoGeometry.Arithmetic.LectureStructureAndRandomness

namespace InfoGeometry.Arithmetic.LectureStructureAndRandomnessTests

open scoped BigOperators
open LectureStructureAndRandomness BostConnesSystem

example : Archetype.finiteFields ≤ Archetype.gaussIdentities :=
  le_trans gauss_branch.1 gauss_branch.2

example : ¬ Archetype.finiteCounting ≤ Archetype.spectralStatistics := by
  decide

example (samples : Finset ℕ+) :
    (∑ index ∈ samples, liouville index * liouville (1 * index.val)) =
      (samples.card : ℤ) := by
  simpa using dilation_correlation samples 1

example (samples : Finset ℕ+) :
    (∑ index ∈ samples, liouville index * liouville (2 * index.val)) =
      -(samples.card : ℤ) :=
  prime_dilation_correlation samples 2 (by decide)

example :
    (∑ index ∈ ({1} : Finset ℕ+), liouville index * liouville (3 * index.val)) =
      -1 := by
  simpa using prime_dilation_correlation ({1} : Finset ℕ+) 3 (by decide)

example (multiplier : ℕ+) :
    (∑ index ∈ (∅ : Finset ℕ+),
      liouville index * liouville (multiplier.val * index.val)) = 0 := by
  simp

example (samples : Finset ℕ+) (shift : ℕ) :
    (∑ index ∈ samples, liouville index * liouville (index.val + shift)) = 0 ↔
      2 * ((samples.filter (fun index =>
        liouville index = liouville (index.val + shift))).card : ℤ) =
          (samples.card : ℤ) :=
  liouville_correlation_zero_iff samples shift

example : legendreSym 13 5 = legendreSym 5 13 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact quadratic_reciprocity_one_mod_four 5 13 (by decide) (by decide)

example (region : CertifiedRegion
    InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge.entireRiemannXi)
    {point : ℂ} (member : point ∈ region.carrier)
    (zero_at :
      InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge.entireRiemannXi point = 0) :
    point.re = 1 / 2 :=
  region.zero_on_critical_line member zero_at

example : ∃ predicate : ℕ → Prop,
    (∀ index ≤ 1000000, predicate index) ∧ ¬ ∀ index, predicate index :=
  finite_checks_do_not_imply_universal 1000000

#print axioms prerequisites_injective
#print axioms gauss_branch
#print axioms correlation_branch
#print axioms symmetry_branch
#print axioms spectral_branch
#print axioms symmetry_and_spectral_realization_incomparable
#print axioms dependency_antisymmetric
#print axioms gauss_duality
#print axioms quadratic_gauss_square
#print axioms quadratic_reciprocity_one_mod_four
#print axioms liouville_completely_multiplicative
#print axioms dilation_correlation
#print axioms prime_dilation_correlation
#print axioms functional_symmetry_pairs_zeros
#print axioms functional_symmetry_does_not_force_critical_zeros
#print axioms finite_checks_do_not_imply_universal

end InfoGeometry.Arithmetic.LectureStructureAndRandomnessTests
