/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.RealSplitOctonionAutCandidateConstraint
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Finite coordinate readout of the existing automorphism equations

The readout is only a finite observation of the existing multiplicativity
condition.  It introduces neither a new carrier nor a new automorphism
predicate.
-/

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

noncomputable def candidateMultiplicativityFailure
    (f : SplitOctonionAutCandidate ℝ) : CZ →ₗ[ℝ] CZ →ₗ[ℝ] CZ :=
  LinearMap.mk₂ ℝ (fun X Y => f (zMul X Y) - zMul (f X) (f Y))
    (by
      intro X₁ X₂ Y
      simp only [map_add, zMul_add_left]
      abel)
    (by
      intro r X Y
      simp only [map_smul, zMul_smul_left, smul_sub])
    (by
      intro X Y₁ Y₂
      simp only [map_add, zMul_add_right]
      abel)
    (by
      intro r X Y
      simp only [map_smul, zMul_smul_right, smul_sub])

def automorphismMultiplicativityReadout
    (f : SplitOctonionAutCandidate ℝ) : Fin 8 → Fin 8 → CZ :=
  fun i j => candidateMultiplicativityFailure f
    (circularPeirceBasis i) (circularPeirceBasis j)

abbrev AutomorphismConstraintValues := CZ × (Fin 8 → Fin 8 → CZ)

def automorphismConstraintReadout
    (f : SplitOctonionAutCandidate ℝ) : AutomorphismConstraintValues :=
  (f (1 : CZ) - (1 : CZ), automorphismMultiplicativityReadout f)

theorem continuous_automorphismConstraintReadout :
    Continuous automorphismConstraintReadout := by
  apply Continuous.prodMk
  · exact continuous_candidate_unit_constraint
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simpa [automorphismMultiplicativityReadout,
      candidateMultiplicativityFailure] using
      continuous_candidate_multiplicativity_constraint
        (circularPeirceBasis i) (circularPeirceBasis j)

theorem isClosed_automorphismConstraintReadout_zero :
    IsClosed {f : SplitOctonionAutCandidate ℝ |
      automorphismConstraintReadout f = 0} := by
  exact isClosed_singleton.preimage continuous_automorphismConstraintReadout

theorem automorphismConstraintReadout_zero_iff
    (f : SplitOctonionAutCandidate ℝ) :
    automorphismConstraintReadout f = 0 ↔ IsSplitOctonionAut f := by
  constructor
  · intro h
    have hunit := congrArg Prod.fst h
    have hmul := congrArg Prod.snd h
    have hunit' : f (1 : CZ) - (1 : CZ) = 0 := by
      simpa [automorphismConstraintReadout] using hunit
    have hmul' : automorphismMultiplicativityReadout f = 0 := by
      simpa [automorphismConstraintReadout] using hmul
    have hpres : PreservesZornMul f := by
      intro X Y
      apply sub_eq_zero.mp
      have hzero : candidateMultiplicativityFailure f = 0 := by
        apply LinearMap.ext_basis circularPeirceBasis circularPeirceBasis
        intro i j
        have hij := congrFun (congrFun hmul' i) j
        simpa [automorphismMultiplicativityReadout,
          candidateMultiplicativityFailure] using hij
      have hxy := congrArg
        (fun q : CZ →ₗ[ℝ] CZ →ₗ[ℝ] CZ => q X Y) hzero
      simpa [candidateMultiplicativityFailure] using hxy
    exact ⟨sub_eq_zero.mp hunit', hpres⟩
  · intro h
    apply Prod.ext
    · simpa [automorphismConstraintReadout] using sub_eq_zero.mpr h.1
    · funext i j
      exact sub_eq_zero.mpr (h.2 _ _)

@[simp] theorem automorphismMultiplicativityReadout_apply
    (f : SplitOctonionAutCandidate ℝ) (i j : Fin 8) :
    automorphismMultiplicativityReadout f i j =
      f (zMul (circularPeirceBasis i) (circularPeirceBasis j)) -
        zMul (f (circularPeirceBasis i)) (f (circularPeirceBasis j)) := rfl

theorem automorphismMultiplicativityReadout_eq_zero_of_preservesMul
    (f : SplitOctonionAutCandidate ℝ) (hf : PreservesZornMul f) :
    automorphismMultiplicativityReadout f = 0 := by
  funext i j
  exact sub_eq_zero.mpr (hf _ _)

theorem preservesMul_of_automorphismMultiplicativityReadout_eq_zero
    (f : SplitOctonionAutCandidate ℝ)
    (h : automorphismMultiplicativityReadout f = 0) :
    PreservesZornMul f := by
  intro X Y
  apply sub_eq_zero.mp
  have hzero : candidateMultiplicativityFailure f = 0 := by
    apply LinearMap.ext_basis circularPeirceBasis circularPeirceBasis
    intro i j
    have hij := congrFun (congrFun h i) j
    simpa [automorphismMultiplicativityReadout,
      candidateMultiplicativityFailure] using hij
  have hxy := congrArg
    (fun q : CZ →ₗ[ℝ] CZ →ₗ[ℝ] CZ => q X Y) hzero
  simpa [candidateMultiplicativityFailure] using hxy

theorem automorphism_constraint_readout_zero_iff_isAut
    (f : SplitOctonionAutCandidate ℝ) :
    (f (1 : CZ) - (1 : CZ) = 0 ∧ automorphismMultiplicativityReadout f = 0) ↔
      IsSplitOctonionAut f := by
  constructor
  · rintro ⟨hunit, hmul⟩
    exact ⟨sub_eq_zero.mp hunit,
      preservesMul_of_automorphismMultiplicativityReadout_eq_zero f hmul⟩
  · rintro ⟨hunit, hmul⟩
    exact ⟨sub_eq_zero.mpr hunit,
      automorphismMultiplicativityReadout_eq_zero_of_preservesMul f hmul⟩

theorem automorphism_constraint_readout_zero_of_isAut
    (f : SplitOctonionAutCandidate ℝ) (hf : IsSplitOctonionAut f) :
    f (1 : CZ) - (1 : CZ) = 0 ∧ automorphismMultiplicativityReadout f = 0 := by
  exact ⟨sub_eq_zero.mpr hf.1,
    automorphismMultiplicativityReadout_eq_zero_of_preservesMul f hf.2⟩

theorem automorphismConstraintReadout_one_zero :
    automorphismConstraintReadout (1 : SplitOctonionAutCandidate ℝ) = 0 := by
  apply (automorphismConstraintReadout_zero_iff (1 : SplitOctonionAutCandidate ℝ)).mpr
  exact (splitOctonionAutSubgroup (R := ℝ)).one_mem

end
end InfoGeometry.Canonical
