/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.ReflectionZeroCount

namespace InfoGeometry.Arithmetic.SarnakLocalCertificationTests

open SarnakLocalCertification ActualRiemannXiEntireBridge

noncomputable def linearWitness (point : ℂ) : ℂ := point - 1 / 2

instance : RiemannSymmetric linearWitness where
  zero_reflection point := by
    have reflected : linearWitness (critical_reflection point) =
        -star (linearWitness point) := by
      simp only [linearWitness, critical_reflection, map_sub, map_div,
        star_one, star_ofNat]
      rw [star_sub]
      have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by simp
      rw [hhalf]
      ring
    rw [reflected]
    constructor
    · intro zeroAt
      rw [zeroAt, star_zero, neg_zero]
    · intro reflectedZero
      have originalZero := congrArg (fun value : ℂ => -star value) reflectedZero
      simpa using originalZero

def linearRegion : CertifiedRegion linearWitness where
  carrier := Set.univ
  reflectionInvariant := by
    intro point member
    exact Set.mem_univ _
  uniqueZero := by
    intro first firstMember second secondMember
    have firstZero : first - (1 / 2 : ℂ) = 0 := firstMember.2
    have secondZero : second - (1 / 2 : ℂ) = 0 := secondMember.2
    exact (sub_eq_zero.mp firstZero).trans (sub_eq_zero.mp secondZero).symm

theorem linear_witness_global_certificate :
    ∀ point : ℂ, linearWitness point = 0 → point.re = 1 / 2 := by
  apply global_confinement_of_certificates_at_every_height
  intro height
  refine ⟨1, fun _ => linearRegion, ?_⟩
  intro point bounded zeroAt
  exact ⟨0, Set.mem_univ _⟩

example : linearWitness (1 / 2) = 0 := by
  simp [linearWitness]

example : (1 / 2 : ℂ).re = 1 / 2 :=
  linear_witness_global_certificate (1 / 2) (by simp [linearWitness])

example {count : ℕ} (regions : Fin count → CertifiedRegion entireRiemannXi)
    (height : ℝ)
    (coverage : ∀ point : ℂ, |point.im| ≤ height → entireRiemannXi point = 0 →
      ∃ index, point ∈ (regions index).carrier) :
    ∀ point : ℂ, |point.im| ≤ height → entireRiemannXi point = 0 →
      point.re = 1 / 2 :=
  finite_height_certificate regions height coverage

example (region : CertifiedRegion counterexample_f) :
    (0 : ℂ) ∉ region.carrier := by
  letI : RiemannSymmetric counterexample_f := counterexample_is_symmetric
  intro member
  have forced := region.zero_on_critical_line member (by simp [counterexample_f])
  norm_num at forced

/-- This symmetric set has both off-line points and an on-line point. -/
example : ({(0 : ℂ), 1 / 2, 1} : Finset ℂ).card =
    (({(0 : ℂ), 1 / 2, 1} : Finset ℂ).filter fun z => z.re = 1 / 2).card +
      2 * (({(0 : ℂ), 1 / 2, 1} : Finset ℂ).filter fun z => z.re < 1 / 2).card := by
  classical
  apply reflection_card_decomposition
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl <;> norm_num [critical_reflection]

/-- Finite zero counting applies to the already constructed symmetric function. -/
example : ∃ z ∈ ({(1 / 2 : ℂ)} : Finset ℂ),
    linearWitness z = 0 ∧ z.re = 1 / 2 := by
  classical
  apply exists_zero_on_line_of_odd_count
  · intro z hz
    simp only [Finset.mem_singleton] at hz ⊢
    subst z
    norm_num [critical_reflection]
  · simp [linearWitness, Finset.filter_singleton]

#print axioms reflection_card_left_eq_right
#print axioms reflection_card_decomposition
#print axioms reflection_exists_on_line_of_odd_card
#print axioms zero_filter_reflection_closed
#print axioms exists_zero_on_line_of_odd_count

#print axioms reflection_precedes_certification
#print axioms counting_precedes_certification
#print axioms certification_precedes_global
#print axioms reflection_and_counting_are_incomparable
#print axioms critical_reflection_involutive
#print axioms critical_reflection_fixed_iff
#print axioms entireRiemannXi_riemannSymmetric
#print axioms CertifiedRegion.zero_on_critical_line
#print axioms CertifiedRegion.nonzero_off_critical_line
#print axioms covered_zeros_on_critical_line
#print axioms finite_height_certificate
#print axioms global_confinement_of_certificates_at_every_height
#print axioms symmetric_functions_need_not_have_critical_zeros
#print axioms counterexample_is_symmetric
#print axioms zero_reflection_does_not_imply_confinement
#print axioms linear_witness_global_certificate

end InfoGeometry.Arithmetic.SarnakLocalCertificationTests
