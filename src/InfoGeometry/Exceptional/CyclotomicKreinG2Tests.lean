import InfoGeometry.Exceptional.CyclotomicKreinG2
import InfoGeometry.Lie.G2DoubleStarRootDecomposition

open InfoGeometry.Exceptional
open InfoGeometry.Exceptional.CyclotomicIntegerClock
open InfoGeometry.Exceptional.CyclotomicNeutralBoundary
open InfoGeometry.Exceptional.CyclotomicRotation
open InfoGeometry.Exceptional.CyclotomicKreinG2
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Canonical.TwelveFoldCyclotomicNative
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.G2DoubleStarRootDecomposition

example : Polynomial.cyclotomic 12 ℤ = Polynomial.X ^ 4 - Polynomial.X ^ 2 + 1 :=
  cyclotomic_twelve ℤ

example : (Polynomial.cyclotomic 12 ℤ).natDegree = 4 :=
  cyclotomic_twelve_degree ℤ

example : CyclotomicRotation.rotation.det = 1 ∧
    Matrix.trace CyclotomicRotation.rotation = Real.sqrt 3 ∧
    orderOf CyclotomicRotation.rotation = 12 ∧ CyclotomicRotation.rotation ^ 6 = -1 :=
  ⟨rotation_det, rotation_trace, rotation_order, rotation_half_period⟩

example : Matrix.trace clock = 0 ∧
    Matrix.trace CyclotomicRotation.rotation ^ 2 - 4 < 0 := by
  refine ⟨clock_trace, ?_⟩
  rw [rotation_discriminant]
  norm_num

example :
    ¬ ProofDependency.Archetype.rotationPeriod ≤ ProofDependency.Archetype.ellipticRotation ∧
    ¬ ProofDependency.Archetype.ellipticRotation ≤ ProofDependency.Archetype.rotationPeriod := by
  decide

example : orderOf clock = 12 ∧ clock ^ 6 = -1 ∧ clock ^ 12 = 1 :=
  ⟨clock_order, clock_half_period, clock_period⟩

example : clock ^ 4 ≠ 1 := by
  intro periodic
  have divides := (clock_power_eq_one_iff 4).mp periodic
  norm_num at divides

example : IsKleinFour (Gal(CyclotomicField 12 ℚ / ℚ)) :=
  cyclotomic12_gal_isKleinFour

example :
    shortRootIndices.card = 6 ∧ longRootIndices.card = 6 ∧
    doubleStarIndices.card = 12 :=
  ⟨shortRootIndices_card, longRootIndices_card, doubleStarIndices_card⟩

example :
    Module.finrank ℝ cartanRootSpan = 2 ∧ Module.finrank ℝ rootSpaceSum = 12 :=
  derivation_cartan_rootSpace_two_add_twelve

example :
    canonicalNeutralBilin ((1 : ℝ), LinearMap.id) ((1 : ℝ), LinearMap.id) = 2 ∧
    canonicalNeutralBilin
      (neutralParaInvolution ((1 : ℝ), LinearMap.id))
      (neutralParaInvolution ((1 : ℝ), LinearMap.id)) = -2 := by
  norm_num

example {Root Weight Coweight : Type*} [Finite Root]
    [AddCommGroup Weight] [Module ℝ Weight]
    [AddCommGroup Coweight] [Module ℝ Coweight]
    (pairing : RootPairing Root ℝ Weight Coweight) [pairing.IsG2] :
    Module.finrank ℝ Weight = 2 ∧ Nat.card Root = 12 :=
  g2_rank_and_root_count pairing

example :
    ¬ ProofDependency.Archetype.exactPeriod ≤ ProofDependency.Archetype.rootDecomposition ∧
    ¬ ProofDependency.Archetype.rootDecomposition ≤ ProofDependency.Archetype.exactPeriod := by
  decide

#print axioms cyclotomic_twelve
#print axioms cyclotomic_twelve_degree
#print axioms rotation_entries
#print axioms rotation_trigonometric
#print axioms rotation_trace
#print axioms rotation_det
#print axioms rotation_order
#print axioms rotation_power_eq_one_iff
#print axioms rotation_quartic
#print axioms rotation_half_period
#print axioms rotation_period
#print axioms rotation_discriminant
#print axioms integer_clock_trace_ne_rotation_trace
#print axioms ProofDependency.rotation_dependencies
#print axioms ProofDependency.periodicity_and_ellipticity_incomparable
#print axioms cyclotomic_twelve_factorization
#print axioms pow_six_of_quartic
#print axioms pow_twelve_of_quartic
#print axioms clock_quartic
#print axioms clock_half_period
#print axioms clock_period
#print axioms clock_order
#print axioms clock_power_eq_one_iff
#print axioms clock_annihilates_cyclotomic
#print axioms clock_trace
#print axioms clock_sub_one_isUnit
#print axioms clock_not_unipotent
#print axioms neutral_pairing_contragredient_invariant
#print axioms para_twisted_self_pairing_zero
#print axioms trace_discriminant_trichotomy
#print axioms negative_discriminant_iff
#print axioms zero_discriminant_iff
#print axioms positive_discriminant_iff
#print axioms real_elliptic_not_necessarily_period_twelve
#print axioms square_root_three_discriminant
#print axioms nonidentity_galois_automorphism_order
#print axioms g2_rank_and_root_count
#print axioms g2_six_short_and_six_long
#print axioms galois_automorphisms_not_equivalent_to_g2_roots
#print axioms cyclotomic12_gal_isKleinFour
#print axioms ProofDependency.dependency_branches
#print axioms ProofDependency.arithmetic_and_roots_incomparable
#print axioms ProofDependency.neutral_and_spectral_branches_incomparable
#print axioms ProofDependency.no_cycle
#print axioms shortRootIndices_card
#print axioms longRootIndices_card
#print axioms doubleStarIndices_eq_nonzero_root_indices
#print axioms derivation_cartan_rootSpace_two_add_twelve
