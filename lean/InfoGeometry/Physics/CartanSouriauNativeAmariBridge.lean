import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric
import InfoGeometry.Canonical.MassieuFisherClassical
import InfoGeometry.Canonical.AmariSouriauThermodynamicGauge
import InfoGeometry.Physics.ParaKahlerAmariSouriauSynthesis

/-!
# Native Amari packaging of the finite Cartan--Souriau family

This file packages the existing finite Gibbs/Massieu owners as a
`DuallyFlatAmariSystem`.  It introduces no second statistical model: the
potential is the existing Souriau Massieu function and the metric is the
existing covariance readout.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Physics.CartanSouriauNativeAmariBridge

open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Canonical
open InfoGeometry.Canonical.MassieuFisherClassical
open InfoGeometry.Physics.ParaKahlerAmariSouriauSynthesis
open InfoGeometry.Canonical.AmariSouriauThermodynamicGauge

variable {State : Type*} [Fintype State] [Nonempty State]
  (D : CartanSouriauDatum State)

abbrev Parameter := InfoGeometry.Algebra.FiniteSpin.Vec2R

def parameterDiff (β γ : Parameter) : Parameter := γ - β

def parameterPair (u v : Parameter) : ℝ := ∑ i : Fin 2, u i * v i

def souriauDualCoord (β : Parameter) : Parameter :=
  fun i => -souriauChargeMean D β i

def souriauFisherBilinear (β u v : Parameter) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    u i * chargeCovariance D β i j * v j

def cartanSouriauDuallyFlat :
    DuallyFlatLogPartition Parameter Parameter where
  Ψ := souriauMassieu D
  gradΨ := souriauDualCoord D
  hessianMetric := souriauFisherBilinear D
  diff := parameterDiff
  pair := parameterPair
  diff_self := by intro β; simp [parameterDiff]
  pair_zero_right := by intro u; simp [parameterPair]

def cartanSouriauLogPartitionBridge :
    LogPartitionPotentialBridge Parameter Parameter where
  info := cartanSouriauDuallyFlat D
  Q := realGibbsPartition D
  positiveQ := realGibbsPartition_pos D
  log_partition_eq := by
    intro β
    rfl

def cartanSouriauDuallyFlatAmariSystem :
    DuallyFlatAmariSystem Parameter Parameter where
  logBridge := cartanSouriauLogPartitionBridge D

theorem cartanSouriau_potential_eq_log_gibbsPartition (β : Parameter) :
    (cartanSouriauDuallyFlatAmariSystem D).potential β =
      Real.log (realGibbsPartition D β) := by
  exact (cartanSouriauLogPartitionBridge D).log_partition_eq β

theorem cartanSouriau_gradient_eq_dualCoord (β : Parameter) :
    (cartanSouriauDuallyFlatAmariSystem D).expectationCoord β =
      souriauDualCoord D β := by
  rfl

theorem souriauFisherBilinear_basis (β : Parameter) (i : Fin 2) :
    souriauFisherBilinear D β (Pi.single i 1) (Pi.single i 1) =
      chargeCovariance D β i i := by
  classical
  fin_cases i <;>
    simp [souriauFisherBilinear, Pi.single_apply, Fin.sum_univ_two]

theorem cartanSouriau_hessian_diag_eq_fisher (β : Parameter) (i : Fin 2) :
    deriv (fun t => deriv
      (fun t' => souriauMassieu D (InfoGeometry.Lie.betaSlice β i t')) t)
      (β i) =
      souriauFisherBilinear D β (Pi.single i 1) (Pi.single i 1) := by
  rw [souriauFisherBilinear_basis]
  change deriv (fun t => deriv
      (fun t' => souriauMassieu D (InfoGeometry.Lie.betaSlice β i t')) t)
      (β i) = fisherSouriauMatrix D β i i
  exact fisherSouriauMatrix_eq_massieuHessian D β i

theorem cartanSouriau_fisher_nonneg (β v : Parameter) :
    0 ≤ souriauFisherBilinear D β v v := by
  exact fisher_pos_semidef D β v

theorem cartanSouriau_native_information_geometry_packet (β v : Parameter) :
    ((cartanSouriauDuallyFlatAmariSystem D).potential β =
        Real.log (realGibbsPartition D β)) ∧
      ((cartanSouriauDuallyFlatAmariSystem D).expectationCoord β =
        souriauDualCoord D β) ∧
      (0 ≤ souriauFisherBilinear D β v v) := by
  exact ⟨cartanSouriau_potential_eq_log_gibbsPartition D β,
    cartanSouriau_gradient_eq_dualCoord D β,
    cartanSouriau_fisher_nonneg D β v⟩

end InfoGeometry.Physics.CartanSouriauNativeAmariBridge
