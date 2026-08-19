import Mathlib.Tactic
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Clifford.JordanWignerBridge
import InfoGeometry.Clifford.JordanWignerCAR
import InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit
import InfoGeometry.Canonical.Cl11IndexedJordanWignerCrossSiteLimit
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Clifford.SupergradedCliffordColimit
import InfoGeometry.TraceFormula.OperatorialISColimitFramework
import InfoGeometry.Canonical.InfiniteCARColimit
import InfoGeometry.TraceFormula.PrimonColimitGNSRepresentation
import InfoGeometry.Physics.ChiralSUSYBlockFactorization
import InfoGeometry.Physics.FiniteLeftRightRelativeAction
import InfoGeometry.Canonical.CliffordCARGeneratorTopological
import InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNet

/-!
# GNS CAR Colimit

This file records the direct-limit representatives of the finite Jordan-Wigner
generators and the stagewise CAR readback they inherit from the matrix tower.

It does **not** assert a completed CAR representation on the direct limit, and
it does **not** construct a star/GNS action.  The honest claim here is only:

* the direct-limit representatives are well-defined;
* their squares and same-stage anticommutator are read off from the finite
  matrix theorems;
* the one-step stage embeddings preserve the chosen representatives.
-/

noncomputable section

namespace InfoGeometry.Canonical.GNSCARColimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.SupergradedCliffordColimit
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Canonical.InfiniteCARColimit
open InfoGeometry.TraceFormula.PrimonColimitGNSRepresentation
open InfoGeometry.Physics
open InfoGeometry.Physics.FiniteLeftRightRelativeAction
open InfoGeometry.Canonical.CliffordCARGeneratorTopological
open InfoGeometry.Canonical.Cl11CompatibleRealAlgebraicStateNet
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState

/-! The finite normalized state owner supplies the positivity and symmetry
    data for the direct-limit trace carried by `Cl11TensorTowerLimit`. -/

def cliffordColimitState :
    RealAlgebraicState InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit where
  toLinearMap := limitTrace
  normalized := by
    rw [DirectLimit.one_def 0]
    change limitTrace (ofStage 0 (1 : ClStage 0)) = 1
    rw [limitTrace_stage]
    exact
      (normalizedTraceState 0).normalized
  positive := by
    intro X
    induction X using DirectLimit.induction with
    | _ n A =>
        rw [limit_star_mk, DirectLimit.mul_def]
        change 0 ≤ InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n
          (star A * A)
        exact
          (normalizedTraceState_positive n A)
  symmetric := by
    intro X Y
    induction X, Y using DirectLimit.induction₂ with
    | _ n A B =>
        rw [limit_star_mk, DirectLimit.mul_def, limit_star_mk,
          DirectLimit.mul_def]
        change InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n
            (star B * A) =
          InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n
            (star A * B)
        exact
          (normalizedTraceState n).symmetric A B

@[simp] theorem cliffordColimitState_one :
    cliffordColimitState.toLinearMap
        (1 : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) = 1 := by
  change InfoGeometry.Clifford.Cl11TensorTowerLimit.limitTrace (1 :
    InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) = 1
  exact InfoGeometry.Clifford.Cl11TensorTowerLimit.limitTrace_one

@[simp] theorem cliffordColimitState_stage
    (n : ℕ) (A : ClStage n) :
    cliffordColimitState.toLinearMap (ofStage n A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n A := by
  rfl

theorem tauInfinity_eq_cliffordColimitState (X :
    InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (cliffordBitWordColimitEquiv X) =
      cliffordColimitState.toLinearMap X := by
  induction X using DirectLimit.induction with
  | _ n A =>
      change
        InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
            (cliffordBitWordColimitEquiv (ofStage n A)) =
          cliffordColimitState.toLinearMap (ofStage n A)
      rw [cliffordBitWordColimitEquiv_ofStage,
        InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity_stage,
        cliffordColimitState_stage, normalizedTrace_clStageEquiv]

/-- The chiral matrix trace has the same scalar-state readout in both carrier
presentations: transport the chiral block and then evaluate `tauInfinity`, or
take its scalar trace first and evaluate the Clifford colimit state. -/
theorem cliffordColimitState_chiralTrace_eq_tauInfinity
    (X : ChiralCarrier) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (Matrix.trace
          (chiralCarrierEquiv X)) =
      cliffordColimitState.toLinearMap (Matrix.trace X) := by
  calc
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (Matrix.trace
          (InfoGeometry.Clifford.SupergradedCliffordColimit.chiralCarrierEquiv X)) =
        InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
          (cliffordBitWordColimitEquiv (Matrix.trace X)) := by
            exact (tauInfinity_chiralCarrierEquiv_trace X).symm
    _ = cliffordColimitState.toLinearMap (Matrix.trace X) :=
      tauInfinity_eq_cliffordColimitState (Matrix.trace X)

/-- The existing Clifford colimit state evaluates the parity-inserted chiral
matrix trace identically in the Clifford and BitWord carrier presentations. -/
theorem cliffordColimitState_chiralSupertrace_eq_tauInfinity
    (X : ChiralCarrier) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (Matrix.trace (chiralParity * chiralCarrierEquiv X)) =
      cliffordColimitState.toLinearMap
        (Matrix.trace (chiralParity * X)) := by
  calc
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (Matrix.trace (chiralParity * chiralCarrierEquiv X)) =
        InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
          (cliffordBitWordColimitEquiv
            (Matrix.trace (chiralParity * X))) := by
            exact congrArg
              InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
              (chiralCarrierEquiv_supertrace X).symm
    _ = cliffordColimitState.toLinearMap
        (Matrix.trace (chiralParity * X)) :=
      tauInfinity_eq_cliffordColimitState (Matrix.trace (chiralParity * X))

/-- Odd chiral supercharges have zero readout in the descended colimit state. -/
theorem cliffordColimitState_chiralSupertrace_qPlus_zero (a : Carrier) :
    cliffordColimitState.toLinearMap
        (Matrix.trace (chiralParity * chiralQPlus a)) = 0 := by
  rw [chiral_supertrace_qPlus_zero]
  exact map_zero cliffordColimitState.toLinearMap

theorem cliffordColimitState_chiralSupertrace_qMinus_zero (b : Carrier) :
    cliffordColimitState.toLinearMap
        (Matrix.trace (chiralParity * chiralQMinus b)) = 0 := by
  rw [chiral_supertrace_qMinus_zero]
  exact map_zero cliffordColimitState.toLinearMap

/-- The colimit-state odd Dirac readout vanishes by chiral cancellation. -/
theorem cliffordColimitState_chiralSupertrace_dirac_zero (a b : Carrier) :
    cliffordColimitState.toLinearMap
        (Matrix.trace (chiralParity * chiralDirac a b)) = 0 := by
  rw [chiral_supertrace_dirac_zero]
  exact map_zero cliffordColimitState.toLinearMap

/-! The descended Clifford state annihilates algebraic commutators.  This is
the finite cyclicity theorem transported through the real-linear colimit
trace, rather than an additional tracial-state axiom. -/
theorem cliffordColimitState_commutator_zero
    (X Y : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) :
    cliffordColimitState.toLinearMap (X * Y - Y * X) = 0 := by
  change limitTrace (X * Y - Y * X) = 0
  exact limitTrace_commutator_zero X Y

/-- The descended state annihilates the parity supertrace of the SUSY
Hamiltonian because that supertrace is an algebraic commutator. -/
theorem cliffordColimitState_chiralSupertrace_hamiltonian_zero
    (a b : Carrier) :
    cliffordColimitState.toLinearMap
        (Matrix.trace (chiralParity * chiralSUSYHamiltonian a b)) = 0 := by
  rw [chiral_supertrace_hamiltonian_eq_commutator]
  exact cliffordColimitState_commutator_zero a b

/-- The same commutator vanishing read in the BitWord/Cantor presentation of
the unified carrier. -/
theorem tauInfinity_commutator_zero_clifford
    (X Y : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (cliffordBitWordColimitEquiv (X * Y - Y * X)) = 0 := by
  rw [tauInfinity_eq_cliffordColimitState]
  exact cliffordColimitState_commutator_zero X Y

theorem cliffordColimitState_relativeAction_zero
    (X Y : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) :
    cliffordColimitState.toLinearMap
        (InfoGeometry.Physics.FiniteLeftRightRelativeAction.relativeAction
          (R := ℝ) X Y) = 0 := by
  change cliffordColimitState.toLinearMap (X * Y - Y * X) = 0
  exact cliffordColimitState_commutator_zero X Y

theorem tauInfinity_relativeAction_zero_clifford
    (X Y : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (cliffordBitWordColimitEquiv
          (InfoGeometry.Physics.FiniteLeftRightRelativeAction.relativeAction
            (R := ℝ) X Y)) = 0 := by
  change InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
      (cliffordBitWordColimitEquiv (X * Y - Y * X)) = 0
  exact tauInfinity_commutator_zero_clifford X Y

/-- The real-linear Clifford colimit state reads the finite relative modular
operator on the same stage representative used by the operatorial IS owner.
This is the finite-carrier Tomita readout; no logarithm or completion is
introduced here. -/
theorem cliffordColimitState_tomitaRelativeDelta_stage_identity
    (n : ℕ) (a b :
      (InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n)ˣ) :
    cliffordColimitState.toLinearMap
        (ofStage n
          ((clStageEquiv n).symm
            (InfoGeometry.TraceFormula.OperatorialISColimitFramework.tomitaRelativeDelta
              (R := ℝ) a b (1 : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n)))) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.normalizedTrace n
        (a.val * b.inv) := by
  change limitTrace
      (ofStage n
        ((clStageEquiv n).symm
          (InfoGeometry.TraceFormula.OperatorialISColimitFramework.tomitaRelativeDelta
            (R := ℝ) a b (1 : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n)))) = _
  rw [limitTrace_stage]
  rw [← normalizedTrace_clStageEquiv]
  have hDelta :
      InfoGeometry.TraceFormula.OperatorialISColimitFramework.tomitaRelativeDelta
          (R := ℝ) a b (1 : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n) =
        a.val * b.inv := by
    simp [InfoGeometry.TraceFormula.OperatorialISColimitFramework.tomitaRelativeDelta_apply]
  rw [hDelta]
  exact congrArg
    (InfoGeometry.Algebra.PrimonColimitAlgebra.normalizedTrace n)
    ((clStageEquiv n).apply_symm_apply (a.val * b.inv))

/-- The normalized finite Itakura--Saito readout, including its determinant
potential, is evaluated by the same Clifford colimit state as the Tomita
relative-modular ratio. -/
theorem cliffordColimitState_normalized_finiteIS_modular_readout
    (n : ℕ) (a b :
      (InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n)ˣ) :
    (1 / (2 ^ n : ℝ)) *
        InfoGeometry.TraceFormula.OperatorialISColimitFramework.finiteIS
          n a.val b.val =
      cliffordColimitState.toLinearMap
          (ofStage n
            ((clStageEquiv n).symm
              (InfoGeometry.TraceFormula.OperatorialISColimitFramework.tomitaRelativeDelta
                (R := ℝ) a b
                (1 : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n)))) +
        (1 / (2 ^ n : ℝ)) *
          InfoGeometry.TraceFormula.ItakuraSaito.mongeAmperePotential n
            (a.val * b.inv) - 1 := by
  rw [InfoGeometry.TraceFormula.OperatorialISColimitFramework.normalized_finiteIS_modular_readout]
  rw [← cliffordBitWordColimitEquiv_ofStage_symm]
  rw [tauInfinity_eq_cliffordColimitState]

/-- The creation operator for mode `k` in the direct-limit algebra. -/
def limit_u (k : ℕ) : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit :=
  ofStage (k + 1) (jw_u_new k)

/-- The annihilation operator for mode `k` in the direct-limit algebra. -/
def limit_v (k : ℕ) : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit :=
  ofStage (k + 1) (jw_v_new k)

/-! The odd Jordan--Wigner generators have zero vacuum readout already at
the finite carrier.  The colimit statements below are therefore transported
trace identities, not an additional supertrace or parity axiom. -/

theorem normalizedTrace_jw_u_new_zero (k : ℕ) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace (k + 1)
        (jw_u_new k) = 0 := by
  unfold InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace jw_u_new
  rw [Matrix.trace_kronecker]
  have hbase : Matrix.trace a_dagger_base = 0 := by
    simp [a_dagger_base, Matrix.trace, Matrix.diag]
  rw [hbase, mul_zero]
  simp

theorem normalizedTrace_jw_v_new_zero (k : ℕ) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace (k + 1)
        (jw_v_new k) = 0 := by
  unfold InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace jw_v_new
  rw [Matrix.trace_kronecker]
  have hbase : Matrix.trace a_base = 0 := by
    simp [a_base, Matrix.trace, Matrix.diag]
  rw [hbase, mul_zero]
  simp

theorem cliffordColimitState_limit_u_zero (k : ℕ) :
    cliffordColimitState.toLinearMap (limit_u k) = 0 := by
  unfold limit_u
  rw [cliffordColimitState_stage]
  exact normalizedTrace_jw_u_new_zero k

theorem cliffordColimitState_limit_v_zero (k : ℕ) :
    cliffordColimitState.toLinearMap (limit_v k) = 0 := by
  unfold limit_v
  rw [cliffordColimitState_stage]
  exact normalizedTrace_jw_v_new_zero k

theorem tauInfinity_clifford_limit_u_zero (k : ℕ) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (cliffordBitWordColimitEquiv (limit_u k)) = 0 := by
  rw [tauInfinity_eq_cliffordColimitState]
  exact cliffordColimitState_limit_u_zero k

theorem tauInfinity_clifford_limit_v_zero (k : ℕ) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (cliffordBitWordColimitEquiv (limit_v k)) = 0 := by
  rw [tauInfinity_eq_cliffordColimitState]
  exact cliffordColimitState_limit_v_zero k

/-! The introduced-stage and indexed direct-limit representatives coincide. -/

@[simp] theorem cliffordBitWordColimitEquiv_limit_u (k : ℕ) :
    cliffordBitWordColimitEquiv (limit_u k) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
        (clStageEquiv (k + 1) (jw_u_new k)) := by
  exact cliffordBitWordColimitEquiv_ofStage (k + 1) (jw_u_new k)

@[simp] theorem cliffordBitWordColimitEquiv_limit_v (k : ℕ) :
    cliffordBitWordColimitEquiv (limit_v k) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
        (clStageEquiv (k + 1) (jw_v_new k)) := by
  exact cliffordBitWordColimitEquiv_ofStage (k + 1) (jw_v_new k)

@[simp] theorem limit_u_eq_uImage (k : ℕ) :
    limit_u k = uImage (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) := by
  unfold limit_u uImage u jw_u_new jwCreation jwStringWithBase
  simp [a_dagger_base,
    InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase]

@[simp] theorem limit_v_eq_vImage (k : ℕ) :
    limit_v k = vImage (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) := by
  unfold limit_v vImage v jw_v_new jwAnnihilation
  rw [jwStringWithBase_last]
  simp [a_base, InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase]

/-- The direct-limit creation representative squares to zero. -/
@[simp] theorem limit_u_sq_zero (k : ℕ) : limit_u k * limit_u k = 0 := by
  unfold limit_u
  rw [← ofStage_mul, jw_u_new_sq, ofStage_zero]

/-- The direct-limit annihilation representative squares to zero. -/
@[simp] theorem limit_v_sq_zero (k : ℕ) : limit_v k * limit_v k = 0 := by
  unfold limit_v
  rw [← ofStage_mul, jw_v_new_sq, ofStage_zero]

/-- The same-stage direct-limit mixed CAR relation is the identity. -/
@[simp] theorem limit_uv_anticomm (k : ℕ) :
    limit_u k * limit_v k + limit_v k * limit_u k = 1 := by
  unfold limit_u limit_v
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add, jw_uv_anticomm_new, ofStage_one]

/-! Any two fixed-site representatives can be moved to one common finite
stage.  This is the direct-limit step needed to turn the finite cross-site
CAR laws into the countable CAR relations. -/

theorem uImage_castLE (m n : ℕ) (h : m ≤ n) (k : Fin m) :
    uImage (Fin.castLE h k) = uImage k := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n h ih =>
      have hk : Fin.castLE (Nat.le_succ_of_le h) k =
          (Fin.castLE h k).castSucc := by
        rfl
      rw [hk]
      calc
        uImage ((Fin.castLE h k).castSucc) =
            uImage (Fin.castLE h k) := by
          simpa [uImage] using
            (uImage_castSucc n (Fin.castLE h k))
        _ = uImage k := ih

theorem vImage_castLE (m n : ℕ) (h : m ≤ n) (k : Fin m) :
    vImage (Fin.castLE h k) = vImage k := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n h ih =>
      have hk : Fin.castLE (Nat.le_succ_of_le h) k =
          (Fin.castLE h k).castSucc := by
        rfl
      rw [hk]
      calc
        vImage ((Fin.castLE h k).castSucc) =
            vImage (Fin.castLE h k) := by
          simpa [vImage] using
            (vImage_castSucc n (Fin.castLE h k))
        _ = vImage k := ih

theorem limit_u_cross_site_anticommute {i j : ℕ} (hij : i ≠ j) :
    limit_u i * limit_u j + limit_u j * limit_u i = 0 := by
  let N := max (i + 1) (j + 1)
  have hi : i + 1 ≤ N := le_max_left _ _
  have hj : j + 1 ≤ N := le_max_right _ _
  let ii : Fin N := Fin.castLE hi ⟨i, Nat.lt_succ_self i⟩
  let jj : Fin N := Fin.castLE hj ⟨j, Nat.lt_succ_self j⟩
  have hij' : ii ≠ jj := by
    intro h
    apply hij
    simpa [ii, jj] using congrArg Fin.val h
  rw [limit_u_eq_uImage i, limit_u_eq_uImage j]
  rw [← uImage_castLE (i + 1) N hi ⟨i, Nat.lt_succ_self i⟩,
    ← uImage_castLE (j + 1) N hj ⟨j, Nat.lt_succ_self j⟩]
  exact InfoGeometry.Canonical.Cl11IndexedJordanWignerCrossSiteLimit.uImage_cross_site_anticommute
    N ii jj hij'

theorem limit_v_cross_site_anticommute {i j : ℕ} (hij : i ≠ j) :
    limit_v i * limit_v j + limit_v j * limit_v i = 0 := by
  let N := max (i + 1) (j + 1)
  have hi : i + 1 ≤ N := le_max_left _ _
  have hj : j + 1 ≤ N := le_max_right _ _
  let ii : Fin N := Fin.castLE hi ⟨i, Nat.lt_succ_self i⟩
  let jj : Fin N := Fin.castLE hj ⟨j, Nat.lt_succ_self j⟩
  have hij' : ii ≠ jj := by
    intro h
    apply hij
    simpa [ii, jj] using congrArg Fin.val h
  rw [limit_v_eq_vImage i, limit_v_eq_vImage j]
  rw [← vImage_castLE (i + 1) N hi ⟨i, Nat.lt_succ_self i⟩,
    ← vImage_castLE (j + 1) N hj ⟨j, Nat.lt_succ_self j⟩]
  exact InfoGeometry.Canonical.Cl11IndexedJordanWignerCrossSiteLimit.vImage_cross_site_anticommute
    N ii jj hij'

theorem limit_u_v_cross_site_anticommute {i j : ℕ} (hij : i ≠ j) :
    limit_u i * limit_v j + limit_v j * limit_u i = 0 := by
  let N := max (i + 1) (j + 1)
  have hi : i + 1 ≤ N := le_max_left _ _
  have hj : j + 1 ≤ N := le_max_right _ _
  let ii : Fin N := Fin.castLE hi ⟨i, Nat.lt_succ_self i⟩
  let jj : Fin N := Fin.castLE hj ⟨j, Nat.lt_succ_self j⟩
  have hij' : ii ≠ jj := by
    intro h
    apply hij
    simpa [ii, jj] using congrArg Fin.val h
  rw [limit_u_eq_uImage i, limit_v_eq_vImage j]
  rw [← uImage_castLE (i + 1) N hi ⟨i, Nat.lt_succ_self i⟩,
    ← vImage_castLE (j + 1) N hj ⟨j, Nat.lt_succ_self j⟩]
  exact InfoGeometry.Canonical.Cl11IndexedJordanWignerCrossSiteLimit.uImage_vImage_cross_site_anticommute
    N ii jj hij'

theorem limit_v_u_cross_site_anticommute {i j : ℕ} (hij : i ≠ j) :
    limit_v i * limit_u j + limit_u j * limit_v i = 0 := by
  let N := max (i + 1) (j + 1)
  have hi : i + 1 ≤ N := le_max_left _ _
  have hj : j + 1 ≤ N := le_max_right _ _
  let ii : Fin N := Fin.castLE hi ⟨i, Nat.lt_succ_self i⟩
  let jj : Fin N := Fin.castLE hj ⟨j, Nat.lt_succ_self j⟩
  have hij' : ii ≠ jj := by
    intro h
    apply hij
    simpa [ii, jj] using congrArg Fin.val h
  rw [limit_v_eq_vImage i, limit_u_eq_uImage j]
  rw [← vImage_castLE (i + 1) N hi ⟨i, Nat.lt_succ_self i⟩,
    ← uImage_castLE (j + 1) N hj ⟨j, Nat.lt_succ_self j⟩]
  exact InfoGeometry.Canonical.Cl11IndexedJordanWignerCrossSiteLimit.vImage_uImage_cross_site_anticommute
    N ii jj hij'

/-- The direct-limit Jordan--Wigner representatives satisfy the full
countable algebraic CAR relations. -/
def limitCAR :
    CARAlgebra InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit where
  u := limit_u
  v := limit_v
  anticomm_uv := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [anticommutator, if_pos rfl]
      exact limit_uv_anticomm i
    · change limit_u i * limit_v j + limit_v j * limit_u i =
          if i = j then 1 else 0
      rw [if_neg hij]
      exact limit_u_v_cross_site_anticommute hij
  anticomm_uu := by
    intro i j
    by_cases hij : i = j
    · subst j
      change limit_u i * limit_u i + limit_u i * limit_u i = 0
      rw [limit_u_sq_zero]
      simp
    · change limit_u i * limit_u j + limit_u j * limit_u i = 0
      exact limit_u_cross_site_anticommute hij
  anticomm_vv := by
    intro i j
    by_cases hij : i = j
    · subst j
      change limit_v i * limit_v i + limit_v i * limit_v i = 0
      rw [limit_v_sq_zero]
      simp
    · change limit_v i * limit_v j + limit_v j * limit_v i = 0
      exact limit_v_cross_site_anticommute hij

/-! The CAR relations are now read by the native normalized trace after
transport through the established Clifford/BitWord colimit equivalence. -/

theorem tauInfinity_cliffordCAR_anticommutator_u_v (i j : ℕ) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (cliffordBitWordColimitEquiv
          (anticommutator (limitCAR.u i) (limitCAR.v j))) =
      if i = j then 1 else 0 := by
  rw [limitCAR.anticomm_uv]
  split_ifs with hij
  · simp only [if_pos hij, map_one]
    exact InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity_one
  · simp only [if_neg hij, map_zero, LinearMap.map_zero]

/-! The finite CAR matrices act on the finite carrier by the existing left-action
representation, and the same identity is transported to the algebraic colimit. -/

theorem finiteCAR_leftAction_anticommutator (k : ℕ) (x : UHFStage (k + 1)) :
    finiteLeftAction (k + 1) (clStageEquiv (k + 1) (jw_u_new k))
        (finiteLeftAction (k + 1) (clStageEquiv (k + 1) (jw_v_new k)) x) +
      finiteLeftAction (k + 1) (clStageEquiv (k + 1) (jw_v_new k))
        (finiteLeftAction (k + 1) (clStageEquiv (k + 1) (jw_u_new k)) x) = x := by
  let u : UHFStage (k + 1) := clStageEquiv (k + 1) (jw_u_new k)
  let v : UHFStage (k + 1) := clStageEquiv (k + 1) (jw_v_new k)
  have huv : u * v + v * u = 1 := by
    simpa [u, v] using
      congrArg (clStageEquiv (k + 1)) (jw_uv_anticomm_new k)
  change finiteLeftAction (k + 1) u (finiteLeftAction (k + 1) v x) +
      finiteLeftAction (k + 1) v (finiteLeftAction (k + 1) u x) = x
  change u * (v * x) + v * (u * x) = x
  rw [← mul_assoc, ← mul_assoc, ← add_mul, huv, one_mul]

theorem colimitCAR_leftAction_anticommutator (k : ℕ) (x : UHFStage (k + 1)) :
    colimitLeftAction
        (toColimit (k + 1) (clStageEquiv (k + 1) (jw_u_new k)))
        (colimitLeftAction
          (toColimit (k + 1) (clStageEquiv (k + 1) (jw_v_new k)))
          (toColimit (k + 1) x)) +
      colimitLeftAction
        (toColimit (k + 1) (clStageEquiv (k + 1) (jw_v_new k)))
        (colimitLeftAction
          (toColimit (k + 1) (clStageEquiv (k + 1) (jw_u_new k)))
          (toColimit (k + 1) x)) =
      toColimit (k + 1) x := by
  rw [colimitLeftAction_stage, colimitLeftAction_stage,
    colimitLeftAction_stage, colimitLeftAction_stage]
  simpa [finiteLeftAction_apply, map_add, map_mul] using
    congrArg (toColimit (k + 1)) (finiteCAR_leftAction_anticommutator k x)

/-! The chiral block algebra is applied directly to the finite CAR
generators.  These are carrier theorems, not new supercharge definitions. -/

theorem finiteCAR_chiral_supercharge_packet (k : ℕ) :
    chiralQPlus (clStageEquiv (k + 1) (jw_u_new k)) *
        chiralQPlus (clStageEquiv (k + 1) (jw_u_new k)) = 0 ∧
      chiralQMinus (clStageEquiv (k + 1) (jw_v_new k)) *
        chiralQMinus (clStageEquiv (k + 1) (jw_v_new k)) = 0 ∧
      chiralDirac (clStageEquiv (k + 1) (jw_u_new k))
          (clStageEquiv (k + 1) (jw_v_new k)) *
        chiralDirac (clStageEquiv (k + 1) (jw_u_new k))
          (clStageEquiv (k + 1) (jw_v_new k)) =
        chiralSUSYHamiltonian (clStageEquiv (k + 1) (jw_u_new k))
          (clStageEquiv (k + 1) (jw_v_new k)) := by
  exact ⟨chiralQPlus_sq _, chiralQMinus_sq _, chiralDirac_sq_eq_susyHamiltonian _ _⟩

theorem colimitCAR_chiral_supercharge_packet (k : ℕ) :
    chiralQPlus
          (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
            (clStageEquiv (k + 1) (jw_u_new k))) *
        chiralQPlus
          (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
            (clStageEquiv (k + 1) (jw_u_new k))) = 0 ∧
      chiralQMinus
          (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
            (clStageEquiv (k + 1) (jw_v_new k))) *
        chiralQMinus
          (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
            (clStageEquiv (k + 1) (jw_v_new k))) = 0 ∧
      chiralDirac
          (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
            (clStageEquiv (k + 1) (jw_u_new k)))
          (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
            (clStageEquiv (k + 1) (jw_v_new k))) *
        chiralDirac
          (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
            (clStageEquiv (k + 1) (jw_u_new k)))
          (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
            (clStageEquiv (k + 1) (jw_v_new k))) =
        chiralSUSYHamiltonian
          (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
            (clStageEquiv (k + 1) (jw_u_new k)))
          (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (k + 1)
            (clStageEquiv (k + 1) (jw_v_new k))) := by
  exact ⟨chiralQPlus_sq _, chiralQMinus_sq _, chiralDirac_sq_eq_susyHamiltonian _ _⟩

/-! The finite relative left-right generator is the commutator derivation on
the stage carrier, and the normalized colimit trace annihilates its readout. -/

theorem tauInfinity_finite_relativeAction_zero
    (n : ℕ) (a x : UHFStage n) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
          (relativeAction (R := ℝ) a x)) = 0 := by
  rw [relativeAction_apply]
  change InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
      (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
        (a * x - x * a)) = 0
  rw [map_sub (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n)]
  simpa only [map_sub, map_mul] using
    (InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity_commutator_zero
      (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n a)
      (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n x))

theorem tauInfinity_clifford_relativeAction_zero
    (n : ℕ) (a x : ClStage n) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (cliffordBitWordColimitEquiv
          (ofStage n (relativeAction (R := ℝ) a x))) = 0 := by
  rw [cliffordBitWordColimitEquiv_ofStage]
  change InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
      (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
        (clStageEquiv n (a * x - x * a))) = 0
  have hrel : clStageEquiv n (a * x - x * a) =
      clStageEquiv n a * clStageEquiv n x -
        clStageEquiv n x * clStageEquiv n a := by
    simpa only [map_sub, map_mul]
  rw [hrel]
  simpa only [map_sub, map_mul] using
    (InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity_commutator_zero
      (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n (clStageEquiv n a))
      (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n (clStageEquiv n x)))

/-- The colimit trace and the compatible finite algebraic state net agree on
    every Clifford-stage representative.  This is a finite-to-colimit
    readout theorem; it does not assert a completed star-algebraic carrier. -/
theorem tauInfinity_clifford_stage_eq_state_net
    (n : ℕ) (A : ClStage n) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (cliffordBitWordColimitEquiv (ofStage n A)) =
      cl11CompatibleRealAlgebraicStateNet.state n A := by
  rw [cliffordBitWordColimitEquiv_ofStage]
  rw [InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity_stage]
  rw [normalizedTrace_clStageEquiv]
  exact (state_eq_normalizedTrace n A).symm

/-! The direct-limit CAR representatives coincide with the existing canonical
algebraic/topological generator representatives. -/

theorem limit_u_eq_algebraicCreationElement (k : ℕ) :
    limit_u k =
      algebraicCreationElement (k + 1)
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) := by
  rw [limit_u_eq_uImage]
  rfl

theorem limit_v_eq_algebraicAnnihilationElement (k : ℕ) :
    limit_v k =
      algebraicAnnihilationElement (k + 1)
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) := by
  rw [limit_v_eq_vImage]
  rfl

theorem limit_u_leftAction_eq_algebraicCreationActionAtMode (k : ℕ) :
    LinearMap.mulLeft ℝ (limit_u k) =
      algebraicCreationActionAtMode k := by
  unfold algebraicCreationActionAtMode algebraicCreationAction
  rw [limit_u_eq_algebraicCreationElement]

theorem limit_v_leftAction_eq_algebraicAnnihilationActionAtMode (k : ℕ) :
    LinearMap.mulLeft ℝ (limit_v k) =
      algebraicAnnihilationActionAtMode k := by
  unfold algebraicAnnihilationActionAtMode algebraicAnnihilationAction
  rw [limit_v_eq_algebraicAnnihilationElement]

/-- The one-step stage embedding carries the creation representative forward. -/
theorem limit_u_stage_embed (k : ℕ) :
    ofStage (k + 2) (matStageEmbed (k + 1) (jw_u_new k)) = limit_u k := by
  simpa [limit_u, stageEmbed_apply] using
    (ofStage_apply_bond (n := k + 1) (A := jw_u_new k))

/-- The one-step stage embedding carries the annihilation representative forward. -/
theorem limit_v_stage_embed (k : ℕ) :
    ofStage (k + 2) (matStageEmbed (k + 1) (jw_v_new k)) = limit_v k := by
  simpa [limit_v, stageEmbed_apply] using
    (ofStage_apply_bond (n := k + 1) (A := jw_v_new k))

/-- Stagewise CAR packet for the direct-limit representatives. -/
theorem limit_stagewise_car_packet (k : ℕ) :
    limit_u k * limit_u k = 0 ∧
    limit_v k * limit_v k = 0 ∧
    limit_u k * limit_v k + limit_v k * limit_u k = 1 := by
  refine ⟨limit_u_sq_zero k, ?_, limit_uv_anticomm k⟩
  exact limit_v_sq_zero k

end InfoGeometry.Canonical.GNSCARColimit
