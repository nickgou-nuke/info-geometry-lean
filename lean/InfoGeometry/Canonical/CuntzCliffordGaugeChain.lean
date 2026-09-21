import InfoGeometry.Algebra.RegularBimoduleWeylObstruction
import InfoGeometry.Clifford.CuntzSplitClifford22
import InfoGeometry.Geometry.AssociativeGaugeConnection

/-!
# A concrete finite action on the repaired Clifford carrier

Mathematical dependency order:
regular bimodule -> Cuntz matrix units -> real Clifford representation ->
linear fundamental symmetry -> specified connection -> curvature -> cyclic action.

The trace is chosen on the finite real matrix carrier. It is not extended to
the full Cuntz algebra. The value 64 below comes from the normalization of these
four explicit matrices; it is not a prediction of a physical time or energy.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzCliffordGaugeChain

open InfoGeometry.Clifford.CuntzSplitClifford22
open InfoGeometry.Geometry.AssociativeGaugeConnection

/-- Ordinary real trace after viewing the two-by-two blocks as a four-by-four matrix. -/
def blockTrace : Block →ₗ[ℝ] ℝ where
  toFun T := T 0 0 0 0 + T 0 0 1 1 + T 1 1 0 0 + T 1 1 1 1
  map_add' T U := by simp; ring
  map_smul' r T := by simp; ring

theorem blockTrace_cyclic (T U : Block) : blockTrace (T * U) = blockTrace (U * T) := by
  simp [blockTrace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

def gammaCurvature (i j : Fin 4) : Block :=
  curvature (0 : Module.End ℝ Block) 0 (gamma i) (gamma j)

@[simp] theorem gammaCurvature_eq (i j : Fin 4) :
    gammaCurvature i j = gamma i * gamma j - gamma j * gamma i := by
  simp [gammaCurvature, curvature]

set_option maxHeartbeats 2000000 in
/-- Exact value of the finite curvature-square action for the chosen normalization. -/
theorem gammaAction_eq : cyclicAction blockTrace gammaCurvature = 64 := by
  norm_num [cyclicAction, gammaCurvature_eq, blockTrace,
    Fin.sum_univ_four, gamma0, gamma1, gamma2, gamma3,
    u, v, w, InfoGeometry.Clifford.Cl11Matrix.J1,
    InfoGeometry.Clifford.Cl11Matrix.Eplus, InfoGeometry.Clifford.Cl11Matrix.Eminus,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem gammaAction_gauge_invariant (g : Blockˣ) :
    cyclicAction blockTrace (fun i j : Fin 4 =>
      curvature (0 : Module.End ℝ Block) 0
        (gaugePotential (0 : Module.End ℝ Block) (gamma i) g)
        (gaugePotential (0 : Module.End ℝ Block) (gamma j) g)) = 64 := by
  have hzero : IsLeibniz (0 : Module.End ℝ Block) := by
    intro x y
    simp
  have h := connectionAction_gauge_invariant blockTrace blockTrace_cyclic
    (fun _ : Fin 4 => (0 : Module.End ℝ Block)) (fun _ => hzero)
    (by intros; simp) gamma g
  exact h.trans gammaAction_eq

/-- A zero connection is flat independently of the choice of Clifford frame. -/
theorem zero_connection_curvature :
    curvature (0 : Module.End ℝ Block) 0 0 0 = 0 := by
  simp [curvature]

/-- Clifford commutators can be nonzero on that same carrier. -/
theorem gamma_commutator_ne_zero : gamma0 * gamma2 - gamma2 * gamma0 ≠ 0 := by
  intro h
  have hentry := congrArg (fun T : Block => T 0 0 0 1) h
  norm_num [gamma0, gamma2, u, InfoGeometry.Clifford.Cl11Matrix.J1,
    Matrix.mul_apply, Fin.sum_univ_two] at hentry

end InfoGeometry.Canonical.CuntzCliffordGaugeChain
