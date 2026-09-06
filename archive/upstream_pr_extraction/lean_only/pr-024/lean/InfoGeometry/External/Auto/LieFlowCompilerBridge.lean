import Mathlib
import InfoGeometry.External.Auto.LieFlowMatching
import InfoGeometry.External.Auto.TrifactorGeometry
import InfoGeometry.External.Auto.DeterminantSupergrading

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.LieFlowCompiler

open InfoGeometry.Canonical.LieFlowMatching

/--
Operational reading of Conditional Flow Matching as a KMS/thermodynamic compiler.

`Γ` below is the discrete-to-continuous bridge datum:
- boundary sample `x1`
- group perturbation `g`
- flow time `t`
- power schedule `γ`
-/
structure KMSCompiler (G X V : Type*) [Group G] [MulAction G X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  chart : LieFlowChart G V
  x1 : X
  g : G
  t : ℝ
  gamma : ℝ

namespace KMSCompiler

variable {G X V : Type*}
variable [Group G] [MulAction G X]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Step 5: x0 = g • x1. -/
def boundaryToBulk (C : KMSCompiler G X V) : X :=
  C.g • C.x1

/-- Step 6: A = log(g⁻¹). -/
def logGenerator (C : KMSCompiler G X V) : V :=
  algebraSpeed C.chart C.g

/-- Step 7: xt = exp(tA) • x0. -/
def trajectoryPoint (C : KMSCompiler G X V) (τ : ℝ) : X :=
  geodesicPoint C.chart C.x1 C.g τ

/-- Step 7 endpoints (discrete boundary = t=1, bulk seed = t=0). -/
lemma trajectory_start (C : KMSCompiler G X V) :
    trajectoryPoint C 0 = boundaryToBulk C := by
  simpa [trajectoryPoint, boundaryToBulk] using
    (geodesicPoint_zero (L := C.chart) C.x1 C.g)

lemma trajectory_end (C : KMSCompiler G X V) :
    trajectoryPoint C 1 = C.x1 := by
  simpa [trajectoryPoint] using (geodesicPoint_one (L := C.chart) C.x1 C.g)

/-- Step 8 pointwise loss at this compiler state. -/
def localLoss (C : KMSCompiler G X V) (v : X → ℝ → V) : ℝ :=
  sampleLoss C.chart v C.x1 C.g C.t

/-- Step 8 scheduled loss: t -> t^γ. -/
def localScheduledLoss (C : KMSCompiler G X V) (v : X → ℝ → V) : ℝ :=
  scheduledSampleLoss C.chart v C.x1 C.g C.gamma C.t

/-- If velocity field memorizes the exact Lie-algebra speed, loss is zero. -/
theorem localLoss_eq_zero_if_exact (C : KMSCompiler G X V)
    (v : X → ℝ → V)
    (h : ∀ x t, v x t = logGenerator C) :
    localLoss C v = 0 := by
  simpa [localLoss, logGenerator, sampleLoss_eq_zero_if_perfect] using
    (sampleLoss_eq_zero_if_perfect (L := C.chart) v C.x1 C.g C.t h)

/-- Scheduled loss is also zero under exact matching. -/
theorem scheduledLoss_eq_zero_if_exact (C : KMSCompiler G X V)
    (v : X → ℝ → V)
    (h : ∀ x t, v x t = logGenerator C) :
    localScheduledLoss C v = 0 := by
  simpa [localScheduledLoss, logGenerator] using
    (scheduledSampleLoss_eq_zero_if_perfect (L := C.chart) v C.x1 C.g C.gamma C.t h)

/-- For a finite batch, the empirical estimator vanishes in equilibrium. -/
theorem batchLoss_eq_zero_if_exact (C : KMSCompiler G X V)
    (v : X → ℝ → V) (ts : Finset ℝ)
    (h : ∀ x t, v x t = logGenerator C) :
    batchLoss C.chart v C.x1 C.g ts = 0 := by
  simpa [batchLoss] using
    (batchLoss_eq_zero_if_perfect (L := C.chart) v C.x1 C.g ts
      (by simpa [logGenerator] using h))

/-- Surjectivity witness: exp has a right inverse by `hExpLog`; this is the
    computational form of the theorem that reconstruction chart sees every bulk point. -/
theorem exp_surjective (C : KMSCompiler G X V) : Function.Surjective C.chart.exp := by
  intro g
  exact ⟨C.chart.log g, C.chart.hExpLog g⟩

/-- power-time correction is exactly the correction used for late-time topological focus. -/
theorem gamma_correction_focus (C : KMSCompiler G X V) (ht0 : 0 ≤ C.t)
    (ht1 : C.t ≤ 1) (hγ : 1 < C.gamma) :
    powerTime C.gamma C.t ≤ C.t := by
  exact powerScheduleCompression C.t C.gamma ht0 ht1 hγ

end KMSCompiler

/--
A minimal “physics-to-math” diagnostic packet used as a compiler report:
- exact Lie-cubic gate states (`OP^3 = OP`)
- determinant supergrading as Weyl/sign sector homomorphism
- V4-compatible parity grading in two-sheeted sector.
-/

theorem compiler_diagnostic_packet
    {q : ℝ} (hq : q ^ 3 = q) :
    (q = -1 ∨ q = 0 ∨ q = 1) ∧
    (TrifactorGeometry.trifactorProjectorPlus q) ^ 2 = TrifactorGeometry.trifactorProjectorPlus q ∧
    (TrifactorGeometry.trifactorProjectorMinus q) ^ 2 = TrifactorGeometry.trifactorProjectorMinus q := by
  constructor
  · exact TrifactorGeometry.cubic_real_roots hq
  · exact ⟨TrifactorGeometry.trifactor_projector_idempotent_plus hq,
      TrifactorGeometry.trifactor_projector_idempotent_minus hq⟩

/-- Weyl-scale homogeneity in doubled real sheets is encoded by determinant sign. -/
theorem compiler_scale_grade_multiplicative (A B : M2R) :
    superGrade (A * B) = superGrade A * superGrade B :=
  superGrade_mul A B

/-- Canonical parity signs already proved in this project:
`modular_j` and `chiralParity` are odd, `K = J ε` is even. -/
theorem compiler_parity_table :
    superGrade modular_j = (-1 : SignType) ∧
      superGrade chiralParity = (-1 : SignType) ∧
      superGrade emergentK = (1 : SignType) :=
  superGrade_table

end InfoGeometry.Canonical.LieFlowCompiler
