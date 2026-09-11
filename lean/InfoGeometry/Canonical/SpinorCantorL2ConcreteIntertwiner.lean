import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.Canonical.SpinorCantorL2HilbertIntertwinerBridge

/-!
# Concrete finite Spinor-to-Cantor Hilbert intertwiner

The binary Cantor Cuntz representation already supplies two orthonormal branch
vectors.  This owner packages them as a genuine linear isometry from the
two-dimensional spinor carrier into the Cantor `L²` space.

This is only the carrier map.  It does not assert a Spin action, a Yang--Baxter
transport, or a braid representation on the target.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpinorCantorL2ConcreteIntertwiner

open Complex
open ContinuousLinearMap
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.Canonical.SpinorCantorL2HilbertIntertwinerBridge

abbrev SpinorSpace := SpinorCantorL2HilbertIntertwinerBridge.SpinorSpace

def branchVector (b : Bool) : L2Boundary :=
  (match b with
  | false => vLeft
  | true => vRight) vacuumL2

def spinorToCantor : SpinorSpace →ₗ[ℂ] L2Boundary :=
  (EuclideanSpace.projₗ 0).smulRight (branchVector false) +
    (EuclideanSpace.projₗ 1).smulRight (branchVector true)

theorem branchVector_inner (b c : Bool) :
    inner ℂ (branchVector b) (branchVector c) = if b = c then 1 else 0 := by
  cases b <;> cases c
  · calc
      inner ℂ (branchVector false) (branchVector false) =
          inner ℂ vacuumL2 ((star vLeft) (vLeft vacuumL2)) := by
            exact (ContinuousLinearMap.adjoint_inner_right vLeft
              vacuumL2 (vLeft vacuumL2)).symm
      _ = inner ℂ vacuumL2 vacuumL2 := by
        rw [show (star vLeft) (vLeft vacuumL2) = vacuumL2 by
          exact ContinuousLinearMap.ext_iff.mp vLeft_adjoint_comp_vLeft vacuumL2]
      _ = 1 := vacuumL2_inner_self
  · calc
      inner ℂ (branchVector false) (branchVector true) =
          inner ℂ vacuumL2 ((star vLeft) (vRight vacuumL2)) := by
            exact (ContinuousLinearMap.adjoint_inner_right vLeft
              vacuumL2 (vRight vacuumL2)).symm
      _ = 0 := by
        rw [show (star vLeft) (vRight vacuumL2) = 0 by
          exact ContinuousLinearMap.ext_iff.mp vLeft_adjoint_comp_vRight vacuumL2]
        simp
  · calc
      inner ℂ (branchVector true) (branchVector false) =
          inner ℂ vacuumL2 ((star vRight) (vLeft vacuumL2)) := by
            exact (ContinuousLinearMap.adjoint_inner_right vRight
              vacuumL2 (vLeft vacuumL2)).symm
      _ = 0 := by
        rw [show (star vRight) (vLeft vacuumL2) = 0 by
          exact ContinuousLinearMap.ext_iff.mp vRight_adjoint_comp_vLeft vacuumL2]
        simp
  · calc
      inner ℂ (branchVector true) (branchVector true) =
          inner ℂ vacuumL2 ((star vRight) (vRight vacuumL2)) := by
            exact (ContinuousLinearMap.adjoint_inner_right vRight
              vacuumL2 (vRight vacuumL2)).symm
      _ = inner ℂ vacuumL2 vacuumL2 := by
        rw [show (star vRight) (vRight vacuumL2) = vacuumL2 by
          exact ContinuousLinearMap.ext_iff.mp vRight_adjoint_comp_vRight vacuumL2]
      _ = 1 := vacuumL2_inner_self

theorem spinorToCantor_inner (x y : SpinorSpace) :
    inner ℂ (spinorToCantor x) (spinorToCantor y) = inner ℂ x y := by
  change inner ℂ
      (x.ofLp 0 • branchVector false + x.ofLp 1 • branchVector true)
      (y.ofLp 0 • branchVector false + y.ofLp 1 • branchVector true) = _
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right]
  simp only [branchVector_inner]
  simp
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]

theorem spinorToCantor_norm (x : SpinorSpace) :
    ‖spinorToCantor x‖ = ‖x‖ := by
  have h := spinorToCantor_inner x x
  have hreal := congrArg Complex.re h
  have hleft :
      ‖spinorToCantor x‖ ^ 2 =
        (inner ℂ (spinorToCantor x) (spinorToCantor x)).re :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (spinorToCantor x)
  have hright :
      ‖x‖ ^ 2 = (inner ℂ x x).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x
  have hsquares : ‖spinorToCantor x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [hleft, hright]
    exact hreal
  have hnonneg₁ : 0 ≤ ‖spinorToCantor x‖ := norm_nonneg _
  have hnonneg₂ : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith [hsquares]

theorem spinorToCantor_isometry : Isometry spinorToCantor := by
  intro x y
  simpa [edist_dist, dist_eq_norm, map_sub] using
    congrArg ENNReal.ofReal (spinorToCantor_norm (x - y))

end InfoGeometry.Canonical.SpinorCantorL2ConcreteIntertwiner
