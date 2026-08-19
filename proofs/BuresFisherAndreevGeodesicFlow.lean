import InfoGeometry.External.Auto.BuresInformationGeodesicFlow
import proofs.TopologicalAndreevPump

/-!
# Bures/Fisher geodesic flow after the Andreev pump

This module is the finite metric/dynamics layer following the nonlinear
Andreev-pump tile:

* Bures geometry is represented by a three-coordinate local chart;
* geodesics are represented by affine finite-chart segments;
* Fisher dynamics is represented by the exact quadratic gradient and one
  Newton/Fisher step to the center;
* modular flow is kept as the zero-time fixed-point theorem;
* the Andreev gain/loss condition is reused from `TopologicalAndreevPump`.

The continuum Bures metric, global geodesic uniqueness, dissipative PDE/Onsager
semigroups, and physical supercurrent/BEC realizations remain outside this finite owner.
-/

noncomputable section

namespace BuresFisherAndreevGeodesicFlow

/-- Finite local Bures chart point. -/
@[ext]
structure BuresPoint where
  x : ℝ
  y : ℝ
  z : ℝ

instance : Zero BuresPoint where
  zero := { x := 0, y := 0, z := 0 }

instance : Add BuresPoint where
  add p q := { x := p.x + q.x, y := p.y + q.y, z := p.z + q.z }

instance : Neg BuresPoint where
  neg p := { x := -p.x, y := -p.y, z := -p.z }

instance : Sub BuresPoint where
  sub p q := { x := p.x - q.x, y := p.y - q.y, z := p.z - q.z }

instance : SMul ℝ BuresPoint where
  smul c p := { x := c * p.x, y := c * p.y, z := c * p.z }

instance : AddCommGroup BuresPoint where
  add_assoc a b c := by ext <;> exact add_assoc _ _ _
  zero_add a := by ext <;> exact zero_add _
  add_zero a := by ext <;> exact add_zero _
  nsmul := nsmulRec
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  neg_add_cancel a := by ext <;> exact neg_add_cancel _
  zsmul := zsmulRec
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl
  add_comm a b := by ext <;> exact add_comm _ _

instance : Module ℝ BuresPoint where
  one_smul a := by ext <;> exact one_mul _
  mul_smul a b c := by ext <;> exact mul_assoc _ _ _
  smul_zero a := by ext <;> exact mul_zero _
  smul_add a b c := by ext <;> exact mul_add _ _ _
  add_smul a b c := by ext <;> exact add_mul _ _ _
  zero_smul a := by ext <;> exact zero_mul _

/-- Squared Bures-chart distance shadow. -/
def buresDistanceP (p q : BuresPoint) : ℝ :=
  BuresInformationGeodesicFlow.buresDistance p.x p.y p.z q.x q.y q.z

/-- Affine finite-chart geodesic segment. -/
def geodesicPoint (t : ℝ) (p q : BuresPoint) : BuresPoint :=
  (1 - t) • p + t • q

@[simp] theorem geodesicPoint_zero (p q : BuresPoint) :
    geodesicPoint 0 p q = p := by
  simp [geodesicPoint]

@[simp] theorem geodesicPoint_one (p q : BuresPoint) :
    geodesicPoint 1 p q = q := by
  simp [geodesicPoint]

@[simp] theorem buresDistanceP_self (p : BuresPoint) :
    buresDistanceP p p = 0 := by
  simp [buresDistanceP, BuresInformationGeodesicFlow.buresDistance]

/-- The finite Bures distance shadow is symmetric. -/
theorem buresDistanceP_symm (p q : BuresPoint) :
    buresDistanceP p q = buresDistanceP q p := by
  unfold buresDistanceP BuresInformationGeodesicFlow.buresDistance
  ring

/-- The finite Bures distance shadow is nonnegative. -/
theorem buresDistanceP_nonneg (p q : BuresPoint) :
    0 ≤ buresDistanceP p q := by
  unfold buresDistanceP BuresInformationGeodesicFlow.buresDistance
  have hx : 0 ≤ (p.x - q.x) ^ 2 := sq_nonneg (p.x - q.x)
  have hy : 0 ≤ (p.y - q.y) ^ 2 := sq_nonneg (p.y - q.y)
  have hz : 0 ≤ (p.z - q.z) ^ 2 := sq_nonneg (p.z - q.z)
  nlinarith

/-- One explicit point at the Bures/Fisher center. -/
def buresCenter : BuresPoint := 0

@[simp] theorem buresCenter_x : buresCenter.x = 0 := rfl
@[simp] theorem buresCenter_y : buresCenter.y = 0 := rfl
@[simp] theorem buresCenter_z : buresCenter.z = 0 := rfl

@[simp] theorem buresCenter_zero_distance :
    buresDistanceP buresCenter buresCenter = 0 := by
  simp [buresCenter]

theorem geodesicPoint_buresCenter (t : ℝ) :
    geodesicPoint t buresCenter buresCenter = buresCenter := by
  simp [geodesicPoint, buresCenter]

theorem buresDistanceP_to_buresCenter (p : BuresPoint) :
    buresDistanceP p buresCenter = p.x^2 + p.y^2 + p.z^2 := by
  unfold buresDistanceP BuresInformationGeodesicFlow.buresDistance
  change (p.x - 0)^2 + (p.y - 0)^2 + (p.z - 0)^2 = _
  ring

/-- Fisher-gradient Euler step in the quadratic chart. -/
def fisherEulerStep (I η θ : ℝ) : ℝ :=
  θ - η * deriv (fisherQuadratic I) θ

/-- In the quadratic Fisher chart, the inverse-curvature step lands exactly at
center. -/
theorem fisherEulerStep_inverse_curvature (I θ : ℝ) (hI : I ≠ 0) :
    fisherEulerStep I I⁻¹ θ = 0 := by
  unfold fisherEulerStep
  rw [fisher_gradient]
  field_simp [hI]
  ring

/-- The Fisher gradient is exactly `Iθ`. -/
theorem fisher_gradient_eq (I θ : ℝ) :
    deriv (fisherQuadratic I) θ = I * θ :=
  fisher_gradient


/-- Capstone: finite Bures/Fisher dynamics connects to the already-formalized
Andreev nonlinear gain tile; analytic dynamics and physical supercurrents remain
interfaces. -/
theorem bures_fisher_andreev_geodesic_flow_synthesis
    (p q : BuresPoint) (I θ gain loss K : ℝ) (A : ℂ)
    (hIpos : 0 < I) :
    buresDistanceP p p = 0 ∧
    buresDistanceP p q = buresDistanceP q p ∧
    0 ≤ buresDistanceP p q ∧
    geodesicPoint 0 p q = p ∧
    geodesicPoint 1 p q = q ∧
    buresDistanceP buresCenter buresCenter = 0 ∧
    deriv (fisherQuadratic I) θ = I * θ ∧
    fisherEulerStep I I⁻¹ θ = 0 ∧
    (∀ E, θ * E ≤ fisherQuadratic I θ + dualFisherQuadratic I E) ∧
    (∀ E, deriv (fun x : ℝ => deriv (fisherQuadratic I) x) θ *
      deriv (fun x : ℝ => deriv (dualFisherQuadratic I) x) E = 1) ∧
    modularFlow K 0 A = A ∧
    (0 < TopologicalAndreevPump.gainMinusLoss gain loss ↔ loss < gain) ∧
    TopologicalAndreevPump.generationPhases.length = 3 ∧
    TopologicalAndreevPump.phaseLocked TopologicalAndreevPump.GenerationPhase.p2 = true ∧
    TopologicalAndreevPump.phaseLocked TopologicalAndreevPump.GenerationPhase.p3 = true ∧
    TopologicalAndreevPump.phaseLocked TopologicalAndreevPump.GenerationPhase.p5 = true ∧
    StimulatedScatteringAmplituhedron.fourWaveMixingCount = 4 := by
  exact ⟨buresDistanceP_self p,
    buresDistanceP_symm p q,
    buresDistanceP_nonneg p q,
    geodesicPoint_zero p q,
    geodesicPoint_one p q,
    buresCenter_zero_distance,
    fisher_gradient_eq I θ,
    fisherEulerStep_inverse_curvature I θ (ne_of_gt hIpos),
    fun E => BuresInformationGeodesicFlow.fisher_legendre_geodesic_cost I θ E hIpos,
    fun E => BuresInformationGeodesicFlow.fisher_curvature_inverse I θ E (ne_of_gt hIpos),
    BuresInformationGeodesicFlow.modularFlow_zero_time K A,
    TopologicalAndreevPump.gain_overcomes_loss_iff_positive_margin gain loss,
    TopologicalAndreevPump.generation_phase_count,
    TopologicalAndreevPump.all_generation_phases_locked.1,
    TopologicalAndreevPump.all_generation_phases_locked.2.1,
    TopologicalAndreevPump.all_generation_phases_locked.2.2,
    StimulatedScatteringAmplituhedron.four_wave_mixing_count_eq_four⟩

#check bures_fisher_andreev_geodesic_flow_synthesis

end BuresFisherAndreevGeodesicFlow

end noncomputable section
