import Mathlib
import InfoGeometry.Inference.PoissonUnbalancedSinkhornCouplingTopological

/-!
# TopCat surface for the continuous unbalanced transport objective

The inference owner already supplies continuous row/column GKL penalties and
the full parameterized transport objective.  This file exposes those native
continuous maps as `TopCat` morphisms and adds no optimizer or convergence
claim.
-/

namespace InfoGeometry.Topology.UnbalancedTransportObjectiveTopCat

noncomputable section

open InfoGeometry.Inference

variable {Row Col : Type}
  [Fintype Row] [Nonempty Row] [Fintype Col] [Nonempty Col]

def rowPenaltyTopCatHom
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    TopCat.of (PositiveRowProfile Row) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := unbalancedRowPenaltyContinuousMap T
      continuous_toFun :=
        (unbalancedRowPenaltyContinuousMap T).continuous }

@[simp] theorem rowPenaltyTopCatHom_apply
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (target : PositiveRowProfile Row) :
    rowPenaltyTopCatHom T target =
      unbalancedRowPenaltyContinuousMap T target :=
  rfl

def colPenaltyTopCatHom
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    TopCat.of (PositiveColProfile Col) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := unbalancedColPenaltyContinuousMap T
      continuous_toFun :=
        (unbalancedColPenaltyContinuousMap T).continuous }

@[simp] theorem colPenaltyTopCatHom_apply
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (target : PositiveColProfile Col) :
    colPenaltyTopCatHom T target =
      unbalancedColPenaltyContinuousMap T target :=
  rfl

theorem rowPenaltyTopCatHom_target_nonnegative
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    0 ≤ rowPenaltyTopCatHom T
      ⟨T.targetRowMass, T.target_row_mass_pos⟩ := by
  rw [rowPenaltyTopCatHom_apply,
    unbalancedRowPenaltyContinuousMap_target_eq]
  exact unbalancedRowPenalty_nonneg T

theorem colPenaltyTopCatHom_target_nonnegative
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    0 ≤ colPenaltyTopCatHom T
      ⟨T.targetColMass, T.target_col_mass_pos⟩ := by
  rw [colPenaltyTopCatHom_apply,
    unbalancedColPenaltyContinuousMap_target_eq]
  exact unbalancedColPenalty_nonneg T

def fullObjectiveTopCatHom
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ) :
    TopCat.of (FullObjectiveParameterSpace Row Col) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fullUnbalancedTransportObjectiveProfilesContinuousMap
        T cost reference
      continuous_toFun :=
        (fullUnbalancedTransportObjectiveProfilesContinuousMap
          T cost reference).continuous }

@[simp] theorem fullObjectiveTopCatHom_apply
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ)
    (p : FullObjectiveParameterSpace Row Col) :
    fullObjectiveTopCatHom T cost reference p =
      fullUnbalancedTransportObjectiveProfilesContinuousMap
        T cost reference p :=
  rfl

end
end InfoGeometry.Topology.UnbalancedTransportObjectiveTopCat
