/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedHodgeOperators

/-!
# The algebraic kernel/range split of the dual-seed adjoint Laplacian

The balanced projection and explicit Green operator identify the kernel of
the ordinary adjoint anticommutator with the whole common commutant. They
construct complementary kernel and range submodules on the unrestricted
ambient algebra. No inner product, norm, finite dimension, or completion is
required. The hypothesis that two is nonzero is explicit.
-/

namespace InfoGeometry.Core.DualSeedPeirce

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.LieJordanGenerators

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Common commutation annihilates both ordered adjoint composites. -/
theorem neg_symmetricGenerator_eq_zero_of_mem_centralizer (d b a : A)
    (ha : a ∈ Subalgebra.centralizer R ({d, b} : Set A)) :
    (-symmetricGenerator (R := R) d b) a = 0 := by
  have hc := (Subalgebra.mem_centralizer_iff R).mp ha
  have hd : LieAlgebra.ad R A d a = 0 := by
    change d * a - a * d = 0
    exact sub_eq_zero.mpr (hc d (Set.mem_insert d {b}))
  have hb : LieAlgebra.ad R A b a = 0 := by
    change b * a - a * b = 0
    exact sub_eq_zero.mpr (hc b (Set.mem_insert_of_mem d (Set.mem_singleton b)))
  change -(-(LieAlgebra.ad R A d (LieAlgebra.ad R A b a) +
    LieAlgebra.ad R A b (LieAlgebra.ad R A d a))) = 0
  rw [neg_neg, hd, hb, map_zero, map_zero, add_zero]

end Ring

section Field

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
variable {d b : A}

namespace IsDualSeedPair

/-- The two adjoint actions remain noncommutative on the full endomorphism algebra. -/
theorem ad_seeds_not_commute (h : IsDualSeedPair d b) (hd : d ≠ 0)
    (h2 : (2 : K) ≠ 0) :
    ¬ Commute (LieAlgebra.ad K A d) (LieAlgebra.ad K A b) := by
  intro hc
  have hz : LieAlgebra.ad K A (phasePolarization d b) = 0 := by
    change LieAlgebra.ad K A ⁅d, b⁆ = 0
    rw [(LieAlgebra.ad K A).map_lie]
    change LieAlgebra.ad K A d * LieAlgebra.ad K A b -
      LieAlgebra.ad K A b * LieAlgebra.ad K A d = 0
    exact sub_eq_zero.mpr hc.eq
  have he := congrArg (fun f : Module.End K A => f d) hz
  change ⁅phasePolarization d b, d⁆ = 0 at he
  rw [h.lie_phase_seed] at he
  have he' : (2 : K) • d = 0 := by
    simpa only [two_smul K, two_nsmul] using he
  exact (smul_ne_zero h2 hd) he'

/-- The Cartan coefficient lies in the eigenvalue-four sector of the Laplacian. -/
theorem neg_symmetricGenerator_phase (h : IsDualSeedPair d b) :
    (-symmetricGenerator (R := K) d b) (phasePolarization d b) =
      (4 : ℕ) • phasePolarization d b := by
  change -(-(d * (b * phasePolarization d b - phasePolarization d b * b) -
      (b * phasePolarization d b - phasePolarization d b * b) * d +
    (b * (d * phasePolarization d b - phasePolarization d b * d) -
      (d * phasePolarization d b - phasePolarization d b * d) * b))) = _
  rw [neg_neg, h.partner_mul_phase, h.phase_mul_partner,
    h.seed_mul_phase, h.phase_mul_seed]
  change _ = (4 : ℕ) • (d * b - b * d)
  rw [show (4 : ℕ) = 2 + 2 by decide, add_nsmul]
  simp only [two_nsmul]
  noncomm_ring

/-- Balancing removes the Cartan component retained by the directional projection. -/
theorem balancedCentralizerProjection_phase (h : IsDualSeedPair d b) :
    balancedCentralizerProjection K d b (phasePolarization d b) = 0 := by
  have hs : centralizerProjection K b d (phasePolarization d b) =
      -(carrierSupport d b) := by
    have hp : phasePolarization d b = -(phasePolarization b d) := by
      change d * b - b * d = -(b * d - d * b)
      abel
    rw [hp, map_neg, h.symm.centralizerProjection_phase]
    change -(b * d + d * b) = -(d * b + b * d)
    rw [add_comm]
  change (1 / 2 : K) •
    (centralizerProjection K d b (phasePolarization d b) +
      centralizerProjection K b d (phasePolarization d b)) = 0
  rw [h.centralizerProjection_phase, hs, add_neg_cancel, smul_zero]

/-- A nonzero seed separates the original directional retraction from the balanced one. -/
theorem centralizerProjection_ne_balanced (h : IsDualSeedPair d b) (hd : d ≠ 0) :
    centralizerProjection K d b ≠ balancedCentralizerProjection K d b := by
  intro he
  have hvalue := congrArg (fun f : Module.End K A => f (phasePolarization d b)) he
  rw [h.centralizerProjection_phase, h.balancedCentralizerProjection_phase] at hvalue
  exact h.support_ne_zero hd hvalue

/-- Averaging the two existing retractions still lands in the full common commutant. -/
theorem balancedCentralizerProjection_mem (h : IsDualSeedPair d b) (a : A) :
    balancedCentralizerProjection K d b a ∈
      Subalgebra.centralizer K ({d, b} : Set A) := by
  change (1 / 2 : K) •
    (centralizerProjection K d b a + centralizerProjection K b d a) ∈ _
  apply Subalgebra.smul_mem
  apply Subalgebra.add_mem
  · exact h.centralizerProjection_mem a
  · simpa only [Set.pair_comm] using h.symm.centralizerProjection_mem (R := K) a

/-- The average fixes each common-commutant element once two can be cancelled. -/
theorem balancedCentralizerProjection_eq_self (h : IsDualSeedPair d b)
    (h2 : (2 : K) ≠ 0) {a : A} (hd : Commute a d) (hb : Commute a b) :
    balancedCentralizerProjection K d b a = a := by
  change (1 / 2 : K) •
    (centralizerProjection K d b a + centralizerProjection K b d a) = a
  rw [h.centralizerProjection_eq_self hd hb, h.symm.centralizerProjection_eq_self hb hd]
  rw [← two_smul K a, smul_smul, div_mul_cancel₀ 1 h2, one_smul]

/-- Fixed points of the balanced projection are exactly the common commutant. -/
theorem balancedCentralizerProjection_eq_self_iff (h : IsDualSeedPair d b)
    (h2 : (2 : K) ≠ 0) (a : A) :
    balancedCentralizerProjection K d b a = a ↔
      a ∈ Subalgebra.centralizer K ({d, b} : Set A) := by
  constructor
  · intro he
    rw [← he]
    exact h.balancedCentralizerProjection_mem a
  · intro ha
    have hc := (Subalgebra.mem_centralizer_iff K).mp ha
    exact h.balancedCentralizerProjection_eq_self h2
      (hc d (Set.mem_insert d {b})).symm
      (hc b (Set.mem_insert_of_mem d (Set.mem_singleton b))).symm

/-- The constructed harmonic projection is idempotent as a native endomorphism. -/
theorem balancedCentralizerProjection_mul_self (h : IsDualSeedPair d b)
    (h2 : (2 : K) ≠ 0) :
    balancedCentralizerProjection K d b * balancedCentralizerProjection K d b =
      balancedCentralizerProjection K d b := by
  ext a
  exact (h.balancedCentralizerProjection_eq_self_iff h2 _).mpr
    (h.balancedCentralizerProjection_mem a)

/-- Every common-commutant element is the image of itself. -/
theorem balancedCentralizerProjection_range (h : IsDualSeedPair d b)
    (h2 : (2 : K) ≠ 0) :
    LinearMap.range (balancedCentralizerProjection K d b) =
      (Subalgebra.centralizer K ({d, b} : Set A)).toSubmodule := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact h.balancedCentralizerProjection_mem x
  · intro ha
    exact ⟨a, (h.balancedCentralizerProjection_eq_self_iff h2 a).mpr ha⟩

/-- The Green identity supplies the nontrivial kernel converse. -/
theorem ker_neg_symmetricGenerator_eq_centralizer (h : IsDualSeedPair d b)
    (h2 : (2 : K) ≠ 0) :
    LinearMap.ker (-symmetricGenerator (R := K) d b) =
      (Subalgebra.centralizer K ({d, b} : Set A)).toSubmodule := by
  ext a
  change (-symmetricGenerator (R := K) d b) a = 0 ↔
    a ∈ Subalgebra.centralizer K ({d, b} : Set A)
  constructor
  · intro ha
    have he := congrArg (fun f : Module.End K A => f a)
      (h.dualSeedGreen_mul_neg_symmetricGenerator h2)
    change dualSeedGreen K d b ((-symmetricGenerator (R := K) d b) a) =
      a - balancedCentralizerProjection K d b a at he
    rw [ha, map_zero] at he
    exact (h.balancedCentralizerProjection_eq_self_iff h2 a).mp
      (sub_eq_zero.mp he.symm).symm
  · exact neg_symmetricGenerator_eq_zero_of_mem_centralizer d b a

/-- The Laplacian annihilates the image of the balanced projection. -/
theorem neg_symmetricGenerator_mul_balancedCentralizerProjection
    (h : IsDualSeedPair d b) :
    (-symmetricGenerator (R := K) d b) * balancedCentralizerProjection K d b = 0 := by
  ext a
  exact neg_symmetricGenerator_eq_zero_of_mem_centralizer d b _
    (h.balancedCentralizerProjection_mem a)

/-- The two Green identities also give annihilation in the opposite order. -/
theorem balancedCentralizerProjection_mul_neg_symmetricGenerator
    (h : IsDualSeedPair d b) (h2 : (2 : K) ≠ 0) :
    balancedCentralizerProjection K d b * (-symmetricGenerator (R := K) d b) = 0 := by
  have hleft : balancedCentralizerProjection K d b =
      1 - (-symmetricGenerator (R := K) d b) * dualSeedGreen K d b := by
    rw [h.neg_symmetricGenerator_mul_dualSeedGreen h2]
    abel
  have hright : balancedCentralizerProjection K d b =
      1 - dualSeedGreen K d b * (-symmetricGenerator (R := K) d b) := by
    rw [h.dualSeedGreen_mul_neg_symmetricGenerator h2]
    abel
  calc
    _ = (1 - (-symmetricGenerator (R := K) d b) * dualSeedGreen K d b) *
        (-symmetricGenerator (R := K) d b) := by rw [← hleft]
    _ = (-symmetricGenerator (R := K) d b) *
        (1 - dualSeedGreen K d b * (-symmetricGenerator (R := K) d b)) := by
      noncomm_ring
    _ = (-symmetricGenerator (R := K) d b) * balancedCentralizerProjection K d b := by
      rw [← hright]
    _ = 0 := h.neg_symmetricGenerator_mul_balancedCentralizerProjection

/-- The explicit Green operator is normalized to zero on the harmonic image. -/
theorem dualSeedGreen_mul_balancedCentralizerProjection (h : IsDualSeedPair d b) :
    dualSeedGreen K d b * balancedCentralizerProjection K d b = 0 := by
  ext a
  have hc := (Subalgebra.mem_centralizer_iff K).mp
    (h.balancedCentralizerProjection_mem (K := K) a)
  exact h.dualSeedGreen_eq_zero_of_commute
    (hc d (Set.mem_insert d {b})).symm
    (hc b (Set.mem_insert_of_mem d (Set.mem_singleton b))).symm

/-- The constructed Green map satisfies the existing Drazin equations at index one. -/
theorem dualSeedGreen_isDrazinInverse (h : IsDualSeedPair d b) (h2 : (2 : K) ≠ 0) :
    InfoGeometry.Singular.Drazin.IsDrazinInverse
      (-symmetricGenerator (R := K) d b) (dualSeedGreen K d b) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_assoc, h.neg_symmetricGenerator_mul_dualSeedGreen h2,
      mul_sub, mul_one, h.dualSeedGreen_mul_balancedCentralizerProjection, sub_zero]
  · rw [h.neg_symmetricGenerator_mul_dualSeedGreen h2,
      h.dualSeedGreen_mul_neg_symmetricGenerator h2]
  · simp only [pow_one, show (1 : ℕ) + 1 = 2 by decide, pow_two]
    rw [mul_assoc, h.neg_symmetricGenerator_mul_dualSeedGreen h2,
      mul_sub, mul_one, h.neg_symmetricGenerator_mul_balancedCentralizerProjection, sub_zero]

/-- The explicit Green map solves the Laplacian equation on the complementary kernel. -/
theorem range_neg_symmetricGenerator_eq_ker_balancedCentralizerProjection
    (h : IsDualSeedPair d b) (h2 : (2 : K) ≠ 0) :
    LinearMap.range (-symmetricGenerator (R := K) d b) =
      LinearMap.ker (balancedCentralizerProjection K d b) := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact congrArg (fun f : Module.End K A => f x)
      (h.balancedCentralizerProjection_mul_neg_symmetricGenerator h2)
  · intro ha
    have he := congrArg (fun f : Module.End K A => f a)
      (h.neg_symmetricGenerator_mul_dualSeedGreen h2)
    change (-symmetricGenerator (R := K) d b) (dualSeedGreen K d b a) =
      a - balancedCentralizerProjection K d b a at he
    rw [LinearMap.mem_ker.mp ha, sub_zero] at he
    exact ⟨dualSeedGreen K d b a, he⟩

/-- A constructive algebraic kernel/range decomposition of every ambient element. -/
theorem balanced_hodge_decomposition (h : IsDualSeedPair d b)
    (h2 : (2 : K) ≠ 0) (a : A) :
    a = balancedCentralizerProjection K d b a +
      (-symmetricGenerator (R := K) d b) (dualSeedGreen K d b a) := by
  have he := congrArg (fun f : Module.End K A => f a)
    (h.neg_symmetricGenerator_mul_dualSeedGreen h2)
  change (-symmetricGenerator (R := K) d b) (dualSeedGreen K d b a) =
    a - balancedCentralizerProjection K d b a at he
  rw [he]
  abel

/-- Native complementary submodules; this is an algebraic direct sum. -/
theorem isCompl_ker_range_neg_symmetricGenerator (h : IsDualSeedPair d b)
    (h2 : (2 : K) ≠ 0) :
    IsCompl (LinearMap.ker (-symmetricGenerator (R := K) d b))
      (LinearMap.range (-symmetricGenerator (R := K) d b)) := by
  rw [h.ker_neg_symmetricGenerator_eq_centralizer h2,
    h.range_neg_symmetricGenerator_eq_ker_balancedCentralizerProjection h2]
  constructor
  · rw [disjoint_iff_inf_le]
    intro a ha
    have he := (h.balancedCentralizerProjection_eq_self_iff h2 a).mpr ha.1
    have hz := LinearMap.mem_ker.mp ha.2
    rw [he] at hz
    simpa only [hz] using (Submodule.zero_mem (⊥ : Submodule K A))
  · rw [codisjoint_iff_le_sup]
    intro a _
    rw [Submodule.mem_sup]
    refine ⟨balancedCentralizerProjection K d b a,
      h.balancedCentralizerProjection_mem a,
      a - balancedCentralizerProjection K d b a, ?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub]
      have he := congrArg (fun f : Module.End K A => f a)
        (h.balancedCentralizerProjection_mul_self h2)
      change balancedCentralizerProjection K d b
        (balancedCentralizerProjection K d b a) =
          balancedCentralizerProjection K d b a at he
      rw [he, sub_self]
    · abel

end IsDualSeedPair
end Field

end InfoGeometry.Core.DualSeedPeirce
