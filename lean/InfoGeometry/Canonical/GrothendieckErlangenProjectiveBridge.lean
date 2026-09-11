import InfoGeometry.Canonical.GrothendieckGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ErlangenOperator2
import InfoGeometry.GromovWittenErlangen.GWCanonicalCountRayBridge
import InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration

/-!
# InfoGeometry.Canonical.GrothendieckErlangenProjectiveBridge

Thin canonical bridge between the existing Grothendieck, Erlangen symmetry,
and Gromov--Witten projective-count owner surfaces.

This file re-exports theorem-backed readouts only. It does not add a new
Grothendieck theory, a new symmetry principle, or a new count normalization
theorem.
 -/

noncomputable section

namespace InfoGeometry.Canonical.GrothendieckErlangenProjectiveBridge

open InfoGeometry.Arithmetic.PrimitiveProjectiveRays
open InfoGeometry.Canonical.ErlangenOperator2
open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeSurprisalOperatorLift
open InfoGeometry.GromovWittenErlangen
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

/-- Canonical `K₀(ℕ) ≃ ℤ` bridge under the existing Grothendieck owner theorem. -/
noncomputable def k0_equiv_int_bridge : Grothendieck ℕ ≃+ ℤ :=
  grothendieckEquivInt

/-- Geometry is invariant tensorial data under a supplied symmetry action. -/
theorem erlangen_geometry_as_symmetry_invariants
    {𝕜 G State Obs : Type*} [Group G]
    (E : ErlangenOperatorDatum 𝕜 G State Obs) :
    ErlangenOperatorDatum.ErlangenOperatorGeometry E :=
  ErlangenOperatorDatum.geometry_as_symmetry_invariants E

/-- GW normalized count shape is invariant under nonzero global rescaling. -/
theorem gw_normalizedShape_scale_counts
    {G T Target Coeff : Type*}
    (C : GWProjectiveCountCalibration G T Target Coeff)
    (β c : ℝ) (hc : c ≠ 0) :
    finiteArithmeticNormalizedRay (fun n => c * C.counts n) C.support β =
      C.normalizedShape β := by
  simpa using
    GWProjectiveCountCalibration.normalizedShape_scale_counts (C := C) β c hc

/-- GW normalized count shape depends only on the positive projective ray. -/
theorem gw_normalizedShape_eq_of_samePositiveRay
    {G T Target Coeff : Type*}
    (C : GWProjectiveCountCalibration G T Target Coeff)
    {counts' : CountProfile} {β : ℝ}
    (hray : SamePositiveRay C.counts counts')
    (hZ : finiteArithmeticPartition C.counts C.support β ≠ 0)
    (n : ℕ) :
    finiteArithmeticNormalizedRay counts' C.support β n =
      C.normalizedShape β n := by
  simpa using
    GWProjectiveCountCalibration.normalizedShape_eq_of_samePositiveRay
      (C := C) (hray := hray) (hZ := hZ) n

/-- The selected finite gauge normalizes active weights to sum to one. -/
theorem gw_normalizedShape_sum_eq_one
    {G T Target Coeff : Type*}
    (C : GWProjectiveCountCalibration G T Target Coeff)
    (β : ℝ)
    (hZ : C.finitePartition β ≠ 0) :
    Finset.sum C.support (fun n => C.normalizedShape β n) = 1 :=
  GWProjectiveCountCalibration.normalizedShape_sum_eq_one (C := C) β hZ

/-- Finite unnormalized weights factor through the normalized projective shape. -/
theorem gw_finiteArithmeticWeight_eq_partition_mul_normalizedShape
    {G T Target Coeff : Type*}
    (C : GWProjectiveCountCalibration G T Target Coeff)
    (β : ℝ)
    (hZ : C.finitePartition β ≠ 0)
    (n : ℕ) :
    finiteArithmeticWeight C.counts β n =
      C.finitePartition β * C.normalizedShape β n :=
  GWProjectiveCountCalibration.finiteArithmeticWeight_eq_partition_mul_normalizedShape
    (C := C) β hZ n

/-- Density diagonals are the normalized count masses. -/
theorem gw_stateDensityMatrix_diag
    {n : ℕ} [Nonempty (Fin n)]
    {G T Target Coeff : Type*}
    (B : GWCanonicalCountRayBridge n G T Target Coeff)
    (i : Fin n) :
    B.stateDensityMatrix i i =
      B.counts i / countMass B.counts B.counts_pos :=
  B.stateDensityMatrix_diag i

/-- Entropy of the probability gauge is the expectation of the surprisal operator. -/
theorem gw_entropy_eq_diagonalExpectation_stateSurprisalOperator
    {n : ℕ} [Nonempty (Fin n)]
    {G T Target Coeff : Type*}
    (B : GWCanonicalCountRayBridge n G T Target Coeff) :
    InfoGeometry.entropy B.stateFinProb =
      diagonalExpectation B.stateFinProb B.stateSurprisalOperator :=
  B.entropy_eq_diagonalExpectation_stateSurprisalOperator

/-- The projective count Hamiltonian is the relative modular potential. -/
theorem gw_projectiveHamiltonianProfile_eq_relativeModularPotential
    {n : ℕ} [Nonempty (Fin n)]
    {G T Target Coeff : Type*}
    (B : GWCanonicalCountRayBridge n G T Target Coeff)
    (i : Fin n) :
    B.projectiveHamiltonianProfile i =
      relativeModularPotential (α := Fin n) B.stateRay B.referenceRay i :=
  B.projectiveHamiltonianProfile_eq_relativeModularPotential i

/-- The projective count density is the exponential of minus the Hamiltonian. -/
theorem gw_projectiveDelta_eq_exp_neg_projectiveHamiltonianProfile
    {n : ℕ} [Nonempty (Fin n)]
    {G T Target Coeff : Type*}
    (B : GWCanonicalCountRayBridge n G T Target Coeff)
    (i : Fin n) :
    B.projectiveDelta i =
      Real.exp (-(B.projectiveHamiltonianProfile i)) :=
  B.projectiveDelta_eq_exp_neg_projectiveHamiltonianProfile i

/-- Self-relative projective count density is one. -/
theorem gw_projectiveDelta_self
    {n : ℕ} [Nonempty (Fin n)]
    {G T Target Coeff : Type*}
    (B : GWCanonicalCountRayBridge n G T Target Coeff)
    (i : Fin n) :
    projectiveCountDelta B.counts B.counts B.counts_pos B.counts_pos i = 1 :=
  B.projectiveDelta_self i

/-- Self-relative projective count Hamiltonian vanishes. -/
theorem gw_projectiveHamiltonianProfile_self
    {n : ℕ} [Nonempty (Fin n)]
    {G T Target Coeff : Type*}
    (B : GWCanonicalCountRayBridge n G T Target Coeff)
    (i : Fin n) :
    projectiveCountHamiltonianProfile
        B.counts B.counts B.counts_pos B.counts_pos i = 0 :=
  B.projectiveHamiltonianProfile_self i

end InfoGeometry.Canonical.GrothendieckErlangenProjectiveBridge
