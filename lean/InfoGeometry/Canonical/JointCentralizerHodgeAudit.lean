/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedHodge
import InfoGeometry.Algebra.FiniteMatrixNoncommutativity
import InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses

/-!
# Closed noncommutative witnesses for the algebraic Hodge construction

The existing dense real three-by-three seed acts on the full matrix algebra.
Its native adjoint actions do not commute. Setting only the partner to zero
preserves the two square-zero assumptions but destroys the claimed Laplacian
kernel converse. For the normalized pair the old directional retraction is
distinct from the balanced harmonic projector.
-/

namespace InfoGeometry.Canonical.JointCentralizerHodgeAudit

attribute [local instance 100] LieRing.ofAssociativeRing

open Matrix InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.LieJordanGenerators
open InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses

/-- Closed noncommutativity on the actual adjoint-endomorphism carrier. -/
theorem dense_ad_seeds_not_commute :
    ¬ Commute (LieAlgebra.ad ℝ _ denseSeed) (LieAlgebra.ad ℝ _ denseSeedᴴ) :=
  denseSeed_pair.ad_seeds_not_commute denseSeed_ne_zero (by norm_num)

/-- A square-zero source with zero partner gives a false Laplacian-kernel converse. -/
theorem dense_zero_partner_kernel_counterexample :
    (-symmetricGenerator (R := ℝ) denseSeed 0) denseSeedᴴ = 0 ∧
      denseSeedᴴ ∉ Subalgebra.centralizer ℝ
        ({denseSeed, 0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  constructor
  · simp [symmetricGenerator]
  · intro ha
    apply denseSeed_not_commute
    change denseSeed * denseSeedᴴ = denseSeedᴴ * denseSeed
    exact (Subalgebra.mem_centralizer_iff ℝ).mp ha denseSeed (Set.mem_insert _ _)

/-- The weak source assumptions allow a strictly larger Laplacian kernel. -/
theorem dense_zero_partner_centralizer_lt_kernel :
    (Subalgebra.centralizer ℝ
      ({denseSeed, 0} : Set (Matrix (Fin 3) (Fin 3) ℝ))).toSubmodule <
      LinearMap.ker (-symmetricGenerator (R := ℝ) denseSeed 0) := by
  refine lt_of_le_not_ge ?_ ?_
  · intro a ha
    exact neg_symmetricGenerator_eq_zero_of_mem_centralizer denseSeed 0 a ha
  · intro hle
    exact dense_zero_partner_kernel_counterexample.2
      (hle dense_zero_partner_kernel_counterexample.1)

/-- The directional retraction and harmonic projector disagree on a nonzero Cartan sector. -/
theorem dense_directional_projection_ne_balanced :
    centralizerProjection ℝ denseSeed denseSeedᴴ ≠
      balancedCentralizerProjection ℝ denseSeed denseSeedᴴ :=
  denseSeed_pair.centralizerProjection_ne_balanced denseSeed_ne_zero

/-- The old directional retraction does not annihilate the Laplacian image. -/
theorem dense_directional_projection_laplacian_ne_zero :
    centralizerProjection ℝ denseSeed denseSeedᴴ
      ((-symmetricGenerator (R := ℝ) denseSeed denseSeedᴴ)
        (phasePolarization denseSeed denseSeedᴴ)) ≠ 0 := by
  rw [denseSeed_pair.neg_symmetricGenerator_phase, map_nsmul,
    denseSeed_pair.centralizerProjection_phase]
  have hn : (4 : ℝ) • carrierSupport denseSeed denseSeedᴴ ≠ 0 :=
    smul_ne_zero (by norm_num) (denseSeed_pair.support_ne_zero denseSeed_ne_zero)
  simpa only [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat] using hn

end InfoGeometry.Canonical.JointCentralizerHodgeAudit
