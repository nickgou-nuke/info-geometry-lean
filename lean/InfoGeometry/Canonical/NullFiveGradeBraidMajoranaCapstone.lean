import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Clifford.ConformalLieAlgebra55
import InfoGeometry.Twistor.NullProjective
import InfoGeometry.Physics.B3PresentedGroup
import InfoGeometry.Physics.YangBaxterQSwap
import InfoGeometry.Physics.YangBaxterZornBridge
import InfoGeometry.OperatorAlgebra.AndreevLedger

/-!
# Finite null, five-grade, braid, and Majorana capstone

This file only packages constructions which already have concrete owners.
The null sector is the linear span of the five explicit Witt null vectors in
`Clifford55`; the projective map is the ordinary Mathlib projectivization.
The five-grade statement is the concrete `adD` eigenspace reversal in
`ConformalLieAlgebra55`, while the braid and Majorana packets are re-used
without asserting an analytic or continuum completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.NullFiveGradeBraidMajoranaCapstone

open BigOperators
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Twistor
open InfoGeometry.Physics
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Physics.YangBaxterQSwap
open InfoGeometry.OperatorAlgebra.AndreevLedger

abbrev NullCoefficient := InfoGeometry.Algebra.FiniteSpin.Vec5R

/-! ## The five-dimensional null annihilator fibre -/

def nullAnnihilatorMap : NullCoefficient →ₗ[ℝ] V55 where
  toFun c := ∑ i : Fin 5, c i • n_pair i
  map_add' c d := by
    classical
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    classical
    simp [Pi.smul_apply, Finset.smul_sum, smul_smul]

@[simp] theorem nullAnnihilatorMap_apply (c : NullCoefficient) :
    nullAnnihilatorMap c = ∑ i : Fin 5, c i • n_pair i := rfl

theorem nullAnnihilatorMap_single (i : Fin 5) :
    nullAnnihilatorMap (Pi.single i 1) = n_pair i := by
  classical
  simp [nullAnnihilatorMap]

@[simp] theorem nullAnnihilator_basis_null (i : Fin 5) :
    Q55 (n_pair i) = 0 := n_pair_null i

theorem nullAnnihilatorMap_injective :
    Function.Injective nullAnnihilatorMap := by
  intro c d h
  funext i
  have hi := congrArg (fun v : V55 => v.2 i) h
  classical
  have hc : (nullAnnihilatorMap c).2 i = c i := by
    dsimp [nullAnnihilatorMap, n_pair, e_pos, f_neg]
    simp only [zero_add, add_zero]
    change (∑ x : Fin 5, c x •
      (fun j => if j = x then (1 : ℝ) else 0)) i = c i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      simp [Pi.smul_apply, hbi.symm]
    · simp
  have hd : (nullAnnihilatorMap d).2 i = d i := by
    dsimp [nullAnnihilatorMap, n_pair, e_pos, f_neg]
    simp only [zero_add, add_zero]
    change (∑ x : Fin 5, d x •
      (fun j => if j = x then (1 : ℝ) else 0)) i = d i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      simp [Pi.smul_apply, hbi.symm]
    · simp
  change (nullAnnihilatorMap c).2 i = (nullAnnihilatorMap d).2 i at hi
  rw [hc, hd] at hi
  exact hi

theorem nullAnnihilatorMap_ker :
    LinearMap.ker nullAnnihilatorMap = ⊥ :=
  (LinearMap.ker_eq_bot).2 nullAnnihilatorMap_injective

theorem nullAnnihilatorMap_range_finrank :
    Module.finrank ℝ (LinearMap.range nullAnnihilatorMap) = 5 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker nullAnnihilatorMap
  rw [nullAnnihilatorMap_ker] at hdim
  simpa [Module.finrank_pi_fintype] using hdim

def nullAnnihilatorFibreEquiv :
    NullCoefficient ≃ₗ[ℝ] LinearMap.range nullAnnihilatorMap :=
  LinearEquiv.ofInjective nullAnnihilatorMap nullAnnihilatorMap_injective

@[simp] theorem nullAnnihilatorFibreEquiv_apply (c : NullCoefficient) :
    nullAnnihilatorFibreEquiv c =
      ⟨nullAnnihilatorMap c, LinearMap.mem_range_self _ c⟩ := rfl

/-! ## Null representative → projective null point → Clifford nilpotent -/

def nullProjectivePoint (i : Fin 5) : TwistorSpace Q55 :=
  twistorMk Q55 (n_pair i) (by
    intro h
    have hi := congrArg (fun v : V55 => v.1 i) h
    simp [n_pair, e_pos, f_neg] at hi) (n_pair_null i)

def nullCliffordRepresentative (i : Fin 5) : Cl55 :=
  ι55 (n_pair i)

@[simp] theorem nullProjectivePoint_isNull (i : Fin 5) :
    IsNull Q55 (nullProjectivePoint i) :=
  (nullProjectivePoint i).property

@[simp] theorem nullCliffordRepresentative_sq (i : Fin 5) :
    nullCliffordRepresentative i * nullCliffordRepresentative i = 0 :=
  n_pair_sq_zero i

theorem null_projective_clifford_readout (i : Fin 5) :
    nullCliffordRepresentative i = ι55 (n_pair i) := rfl

/-! ## Concrete five-grade bracket and reversal -/

def conformalBracket (x y : InfoGeometry.Clifford.ClNN.Alg 5) :
    InfoGeometry.Clifford.ClNN.Alg 5 := x * y - y * x

theorem theta_preserves_conformalBracket
    (x y : InfoGeometry.Clifford.ClNN.Alg 5) :
    thetaOp (conformalBracket x y) =
      conformalBracket (thetaOp x) (thetaOp y) := by
  calc
    thetaOp (conformalBracket x y) =
        thetaOp (x * y) - thetaOp (y * x) := by
          dsimp [conformalBracket, thetaOp]
          noncomm_ring
    _ = thetaOp x * thetaOp y - thetaOp y * thetaOp x := by
          rw [theta_mul, theta_mul]
    _ = conformalBracket (thetaOp x) (thetaOp y) := rfl

theorem theta_reverses_conformal_grade
    (g : InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade)
    (x : InfoGeometry.Clifford.ClNN.Alg 5) (hx : x ∈ gradeSpace g) :
    thetaOp x ∈ gradeSpace
      (InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade.swap g) :=
  theta_maps g x hx

theorem theta_is_involutive_on_conformalBracket
    (x y : InfoGeometry.Clifford.ClNN.Alg 5) :
    thetaOp (thetaOp (conformalBracket x y)) = conformalBracket x y := by
  simp [theta_inv]

/-! ## Braid/Yang--Baxter packet -/

theorem qSwap_yang_baxter (q : ℂ) :
    C12 q * C23 q * C12 q = C23 q * C12 q * C23 q :=
  yang_baxter_relation q

theorem zorn_left_multiplication_braid :
    InfoGeometry.Physics.YangBaxterZornBridge.LeftMulR 0 *
        InfoGeometry.Physics.YangBaxterZornBridge.LeftMulR 1 *
        InfoGeometry.Physics.YangBaxterZornBridge.LeftMulR 0 =
      InfoGeometry.Physics.YangBaxterZornBridge.LeftMulR 1 *
        InfoGeometry.Physics.YangBaxterZornBridge.LeftMulR 0 *
        InfoGeometry.Physics.YangBaxterZornBridge.LeftMulR 1 := by
  exact InfoGeometry.Physics.YangBaxterZornBridge.leftMulR_B3_braid

theorem presented_braid_generators_readout :
    B3PresentedGroup.phi (PresentedGroup.of B3PresentedGroup.B3Gen.sig0) =
        B3PresentedGroup.s0_unit ∧
    B3PresentedGroup.phi (PresentedGroup.of B3PresentedGroup.B3Gen.sig1) =
        B3PresentedGroup.s1_unit := by
  exact ⟨B3PresentedGroup.phi_sig0, B3PresentedGroup.phi_sig1⟩

/-! ## Explicit real particle-hole/Majorana packet -/

abbrev MajoranaCarrier := ℝ × ℝ

def majoranaTheta : MajoranaCarrier →ₗ[ℝ] MajoranaCarrier where
  toFun x := (x.2, x.1)
  map_add' x y := by cases x; cases y; rfl
  map_smul' a x := by cases x; rfl

theorem majoranaTheta_involutive (x : MajoranaCarrier) :
    majoranaTheta (majoranaTheta x) = x := by
  cases x
  rfl

def majoranaLedger : Ledger MajoranaCarrier where
  theta := majoranaTheta
  theta_involutive := majoranaTheta_involutive
  delta := 1
  delta_pos := by norm_num

def majoranaPair : AndreevPair majoranaLedger where
  electron := (1, 0)
  hole := (0, 1)
  electron_to_hole := by rfl

def majoranaBdGLedger : BdGHamiltonianLedger MajoranaCarrier where
  toLedger := majoranaLedger
  H := 0
  particle_hole_anticommutes := by
    intro v
    simp

def majoranaZeroMode : MajoranaZeroMode majoranaBdGLedger where
  mode := majoranaPair.evenMajorana
  zero_energy := by
    change (0 : MajoranaCarrier) = 0
    rfl
  fixed := by
    simpa using majoranaPair.evenMajorana_fixed

@[simp] theorem majoranaZeroMode_fixed :
    majoranaBdGLedger.theta majoranaZeroMode.mode = majoranaZeroMode.mode :=
  majoranaZeroMode.fixed

theorem majoranaZeroMode_nonzero :
    majoranaZeroMode.mode ≠ 0 := by
  intro h
  have hfirst := congrArg Prod.fst h
  norm_num [majoranaZeroMode, majoranaPair, AndreevPair.evenMajorana] at hfirst

/-! ## A typed five-grade ↔ boundary zero-mode bridge -/

abbrev ConcreteGrade :=
  InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade

def concreteGradeInversion :
    InfoGeometry.Canonical.ConformalFiveGradeInversion.FiveGradedConformalInversion
      ConcreteGrade where
  theta := InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade.swap
  grade := id
  theta_involutive := by
    intro g
    simp
  grade_swap := by
    intro g
    rfl

def gradeBoundaryMap : ConcreteGrade → MajoranaCarrier
  | .negTwo => (1, 0)
  | .negOne => (1, 0)
  | .zero => (1, 1)
  | .posOne => (0, 1)
  | .posTwo => (0, 1)

structure TypedFiveGradeBoundaryBridge
    {L : Type*}
    (G : InfoGeometry.Canonical.ConformalFiveGradeInversion.FiveGradedConformalInversion
      L)
    (B : BdGHamiltonianLedger MajoranaCarrier) where
  map : L → MajoranaCarrier
  zeroMode : MajoranaZeroMode B
  theta_equivariant : ∀ g, map (G.theta g) = B.theta (map g)
  center_to_zeroMode : ∀ g,
    G.grade g = InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade.zero →
      map g = zeroMode.mode

def concreteGradeBoundaryBridge :
    TypedFiveGradeBoundaryBridge concreteGradeInversion majoranaBdGLedger where
  map := gradeBoundaryMap
  zeroMode := majoranaZeroMode
  theta_equivariant := by
    intro g
    cases g <;> rfl
  center_to_zeroMode := by
    intro g hg
    cases g with
    | negTwo => cases hg
    | negOne => cases hg
    | zero =>
        norm_num [gradeBoundaryMap, majoranaZeroMode, majoranaPair,
          AndreevPair.evenMajorana]
    | posOne => cases hg
    | posTwo => cases hg

theorem concreteGradeBoundaryBridge_equivariant (g : ConcreteGrade) :
    concreteGradeBoundaryBridge.map (concreteGradeInversion.theta g) =
      majoranaBdGLedger.theta (concreteGradeBoundaryBridge.map g) :=
  concreteGradeBoundaryBridge.theta_equivariant g

theorem concreteGradeBoundaryBridge_center_readout (g : ConcreteGrade)
    (hg : concreteGradeInversion.grade g =
      InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade.zero) :
    concreteGradeBoundaryBridge.map g = majoranaZeroMode.mode :=
  concreteGradeBoundaryBridge.center_to_zeroMode g hg

theorem concreteGradeBoundaryBridge_center_fixed (g : ConcreteGrade)
    (hg : concreteGradeInversion.grade g =
      InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade.zero) :
    majoranaBdGLedger.theta (concreteGradeBoundaryBridge.map g) =
      concreteGradeBoundaryBridge.map g := by
  rw [concreteGradeBoundaryBridge_center_readout g hg]
  exact majoranaZeroMode_fixed

def homogeneousEvenBoundaryMap
    (x : InfoGeometry.Clifford.ConformalLieAlgebra55.HomogeneousElementEven) :
    MajoranaCarrier :=
  gradeBoundaryMap x.1

def homogeneousEvenBoundaryBridge :
    TypedFiveGradeBoundaryBridge
      InfoGeometry.Clifford.ConformalLieAlgebra55.instanceFiveGraded
      majoranaBdGLedger where
  map := homogeneousEvenBoundaryMap
  zeroMode := majoranaZeroMode
  theta_equivariant := by
    intro x
    rcases x with ⟨g, y⟩
    cases g <;> rfl
  center_to_zeroMode := by
    intro x hx
    rcases x with ⟨g, y⟩
    cases g with
    | negTwo => cases hx
    | negOne => cases hx
    | zero =>
        norm_num [homogeneousEvenBoundaryMap, gradeBoundaryMap,
          majoranaZeroMode, majoranaPair, AndreevPair.evenMajorana]
    | posOne => cases hx
    | posTwo => cases hx

theorem homogeneousEvenBoundaryBridge_equivariant
    (x : InfoGeometry.Clifford.ConformalLieAlgebra55.HomogeneousElementEven) :
    homogeneousEvenBoundaryBridge.map
        (InfoGeometry.Clifford.ConformalLieAlgebra55.homogeneousThetaEven x) =
      majoranaBdGLedger.theta (homogeneousEvenBoundaryBridge.map x) :=
  homogeneousEvenBoundaryBridge.theta_equivariant x

theorem homogeneousEvenBoundaryBridge_center_readout
    (x : InfoGeometry.Clifford.ConformalLieAlgebra55.HomogeneousElementEven)
    (hx : InfoGeometry.Clifford.ConformalLieAlgebra55.homogeneousGradeEven x =
      InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade.zero) :
    homogeneousEvenBoundaryBridge.map x = majoranaZeroMode.mode :=
  homogeneousEvenBoundaryBridge.center_to_zeroMode x hx

end InfoGeometry.Canonical.NullFiveGradeBraidMajoranaCapstone
