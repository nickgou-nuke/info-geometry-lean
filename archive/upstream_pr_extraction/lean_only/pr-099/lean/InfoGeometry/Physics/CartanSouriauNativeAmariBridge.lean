import Mathlib.Tactic
import InfoGeometry.Canonical.AmariSouriauThermodynamicGauge
import InfoGeometry.Canonical.MassieuFisherClassical
import InfoGeometry.Physics.ParaKahlerAmariSouriauSynthesis

/-!
# Native Cartan Souriau ensemble as dually-flat information geometry

This owner does not introduce a second statistical model.  It packages the
existing finite Cartan Souriau Gibbs ensemble into the repository-owned
`DuallyFlatLogPartition` / `LogPartitionPotentialBridge` interface.

The data are the already proved native objects:

* `realGibbsKernel` and `realGibbsWeight`;
* `realGibbsPartition`;
* `souriauMassieu = log realGibbsPartition`;
* `souriauChargeMean`;
* `chargeCovariance` / the finite Fisher matrix.

The theorem layer records that the coordinate derivatives of the same Massieu
potential give the mean moment and covariance, and that the resulting Fisher
quadratic form is positive semidefinite.
-/

noncomputable section

namespace InfoGeometry.Physics.CartanSouriauNativeAmariBridge

open scoped BigOperators
open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Canonical.AmariSouriauThermodynamicGauge
open InfoGeometry.Canonical.MassieuFisherClassical
open InfoGeometry.Physics.ParaKahlerAmariSouriauSynthesis

abbrev Parameter := Fin 2 → ℝ

variable {State : Type*} [Fintype State] [Nonempty State]

/-- Native affine difference on the rank-two Cartan temperature parameter. -/
def parameterDiff (beta' beta : Parameter) : Parameter :=
  beta' - beta

/-- Standard rank-two primal/dual pairing. -/
def parameterPair (eta dBeta : Parameter) : ℝ :=
  ∑ i : Fin 2, eta i * dBeta i

/-- The Souriau expectation coordinate.  The sign is fixed by the native
Gibbs convention `exp (- <beta,J>)`, for which `d log Z / d beta_i = -<J_i>`. -/
noncomputable def souriauDualCoord
    (D : CartanSouriauDatum State) (beta : Parameter) : Parameter :=
  fun i => -souriauChargeMean D beta i

/-- The full finite Souriau-Fisher covariance bilinear form. -/
noncomputable def souriauFisherBilinear
    (D : CartanSouriauDatum State) (beta : Parameter)
    (u v : Parameter) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    u i * chargeCovariance D beta i j * v j

/-- The existing finite Cartan Souriau ensemble, packaged as the native
rank-two dually-flat log-partition datum. -/
noncomputable def cartanSouriauDuallyFlat
    (D : CartanSouriauDatum State) :
    DuallyFlatLogPartition Parameter Parameter where
  Ψ := souriauMassieu D
  gradΨ := souriauDualCoord D
  hessianMetric := souriauFisherBilinear D
  diff := parameterDiff
  pair := parameterPair
  diff_self := by
    intro beta
    simp [parameterDiff]
  pair_zero_right := by
    intro eta
    simp [parameterPair]

/-- The positive Gibbs partition function is the partition-function owner of
exactly the same dually-flat datum. -/
noncomputable def cartanSouriauLogPartitionBridge
    (D : CartanSouriauDatum State) :
    LogPartitionPotentialBridge Parameter Parameter where
  info := cartanSouriauDuallyFlat D
  Q := realGibbsPartition D
  positiveQ := realGibbsPartition_pos D
  log_partition_eq := by
    intro beta
    rfl

/-- Direct instance of the already existing Amari-Souriau synthesis packet. -/
noncomputable def cartanSouriauDuallyFlatAmariSystem
    (D : CartanSouriauDatum State) :
    DuallyFlatAmariSystem Parameter Parameter where
  logBridge := cartanSouriauLogPartitionBridge D

@[simp] theorem cartanSouriau_potential_eq_massieu
    (D : CartanSouriauDatum State) (beta : Parameter) :
    (cartanSouriauDuallyFlatAmariSystem D).potential beta =
      souriauMassieu D beta := by
  rfl

@[simp] theorem cartanSouriau_partition_eq_gibbsPartition
    (D : CartanSouriauDatum State) (beta : Parameter) :
    (cartanSouriauLogPartitionBridge D).Q beta =
      realGibbsPartition D beta := by
  rfl

/-- The Amari potential is literally the Souriau Massieu `log Z`. -/
theorem cartanSouriau_potential_eq_log_gibbsPartition
    (D : CartanSouriauDatum State) (beta : Parameter) :
    (cartanSouriauDuallyFlatAmariSystem D).potential beta =
      Real.log (realGibbsPartition D beta) := by
  exact (cartanSouriauDuallyFlatAmariSystem D).potential_eq_log_Q beta

@[simp] theorem cartanSouriau_dualCoord_apply
    (D : CartanSouriauDatum State) (beta : Parameter) (i : Fin 2) :
    (cartanSouriauDuallyFlat D).dualCoord beta i =
      -souriauChargeMean D beta i := by
  rfl

/-- First Massieu derivative = the native Souriau expectation coordinate. -/
theorem cartanSouriau_gradient_eq_dualCoord
    (D : CartanSouriauDatum State) (beta : Parameter) (i : Fin 2) :
    deriv (fun t =>
      (cartanSouriauDuallyFlat D).Ψ (InfoGeometry.Lie.betaSlice beta i t))
      (beta i) =
      (cartanSouriauDuallyFlat D).dualCoord beta i := by
  simpa [cartanSouriauDuallyFlat, souriauDualCoord] using
    souriauMassieu_gradient_eq_neg_meanCharge D beta i

/-- Basis readback of the full Souriau-Fisher bilinear form. -/
theorem souriauFisherBilinear_basis
    (D : CartanSouriauDatum State) (beta : Parameter) (i j : Fin 2) :
    souriauFisherBilinear D beta (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) =
      chargeCovariance D beta i j := by
  fin_cases i <;> fin_cases j <;>
    simp [souriauFisherBilinear, Fin.sum_univ_two, Pi.single_apply]

/-- Second coordinate derivative of the same Massieu potential is the
corresponding diagonal Souriau-Fisher covariance entry. -/
theorem cartanSouriau_hessian_diag_eq_fisher
    (D : CartanSouriauDatum State) (beta : Parameter) (i : Fin 2) :
    deriv (fun t => deriv
      (fun t' => (cartanSouriauDuallyFlat D).Ψ
        (InfoGeometry.Lie.betaSlice beta i t')) t) (beta i) =
      (cartanSouriauDuallyFlat D).fisherMetric beta
        (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
  calc
    deriv (fun t => deriv
      (fun t' => (cartanSouriauDuallyFlat D).Ψ
        (InfoGeometry.Lie.betaSlice beta i t')) t) (beta i)
        = souriauChargeVariance D beta i := by
            simpa [cartanSouriauDuallyFlat] using
              souriauMassieu_secondDeriv_eq_chargeVariance D beta i
    _ = chargeCovariance D beta i i :=
      (chargeCovariance_diag_eq_chargeVariance D beta i).symm
    _ = (cartanSouriauDuallyFlat D).fisherMetric beta
        (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
          symm
          exact souriauFisherBilinear_basis D beta i i

/-- The full covariance metric is positive semidefinite, not merely on the
coordinate axes. -/
theorem cartanSouriau_fisher_nonneg
    (D : CartanSouriauDatum State) (beta v : Parameter) :
    0 ≤ (cartanSouriauDuallyFlat D).fisherMetric beta v v := by
  simpa [cartanSouriauDuallyFlat, souriauFisherBilinear] using
    fisher_pos_semidef D beta v

/-- The Bregman divergence is generated by this same Souriau Massieu potential
and vanishes on the diagonal. -/
theorem cartanSouriau_bregman_self
    (D : CartanSouriauDatum State) (beta : Parameter) :
    (cartanSouriauDuallyFlat D).bregman beta beta = 0 := by
  exact (cartanSouriauDuallyFlat D).bregman_self beta

/-- Compact native packet: one Gibbs/Massieu object simultaneously provides
log partition, expectation coordinate, Fisher-Hessian diagonal readback, and
PSD information metric. -/
theorem cartanSouriau_native_information_geometry_packet
    (D : CartanSouriauDatum State) (beta : Parameter) (i : Fin 2) :
    ((cartanSouriauDuallyFlatAmariSystem D).potential beta =
        Real.log (realGibbsPartition D beta)) ∧
    (deriv (fun t =>
        (cartanSouriauDuallyFlat D).Ψ (InfoGeometry.Lie.betaSlice beta i t))
        (beta i) =
      (cartanSouriauDuallyFlat D).dualCoord beta i) ∧
    (deriv (fun t => deriv
        (fun t' => (cartanSouriauDuallyFlat D).Ψ
          (InfoGeometry.Lie.betaSlice beta i t')) t) (beta i) =
      (cartanSouriauDuallyFlat D).fisherMetric beta
        (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ))) ∧
    (0 ≤ (cartanSouriauDuallyFlat D).fisherMetric beta
      (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ))) := by
  refine ⟨cartanSouriau_potential_eq_log_gibbsPartition D beta,
    cartanSouriau_gradient_eq_dualCoord D beta i,
    cartanSouriau_hessian_diag_eq_fisher D beta i, ?_⟩
  exact cartanSouriau_fisher_nonneg D beta (Pi.single i (1 : ℝ))

end InfoGeometry.Physics.CartanSouriauNativeAmariBridge
