import Mathlib.Tactic

/-!
# Thermodynamic Gauge

Finite algebraic interface for a nonequilibrium transition word.

This file intentionally records only conservative, kernel-safe equalities for
finite ring-level data. It does not prove analytic Wilson-loop, positivity,
de Rham-period, or zeta identities.
-/

namespace InfoGeometry.Topology.ThermodynamicGauge

/-- Nonequilibrium causal flow over a directed causal network. -/
structure CausalNonequilibriumFlow (Op : Type*) [Ring Op] where
  Q : Op
  d_ln_Q : Op
  P_forward : Op
  P_backward : Op

variable {Op : Type*} [Ring Op]

/-- Thermodynamic gauge connection. -/
def thermodynamic_gauge_connection (flow : CausalNonequilibriumFlow Op) : Op :=
  flow.P_forward * flow.d_ln_Q * flow.P_backward

/-- Entropy production commutator. -/
def entropy_production (flow : CausalNonequilibriumFlow Op) : Op :=
  flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward

/-- Entropy production is definitionally the transition commutator. -/
theorem entropy_production_eq_commutator (flow : CausalNonequilibriumFlow Op) :
    entropy_production flow =
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward := by
  rfl

/-- A supplied commutator comparison identifies entropy production with `d_ln_Q`. -/
theorem de_rham_potential_equals_entropy_production_of_commutator
    (flow : CausalNonequilibriumFlow Op)
    (hcomm :
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward =
        flow.d_ln_Q) :
    entropy_production flow = flow.d_ln_Q := by
  rw [entropy_production_eq_commutator, hcomm]

/-- Detailed balance is exactly vanishing commutator defect. -/
theorem entropy_production_eq_zero_iff_detailed_balance (flow : CausalNonequilibriumFlow Op) :
    entropy_production flow = 0 ↔
      flow.P_forward * flow.P_backward = flow.P_backward * flow.P_forward := by
  simp [entropy_production, sub_eq_zero]

/--
Operator-valued variation of the negative logarithmic generator
`K_Q = -log Q`.

Since the flow stores `d_ln_Q`, its surprisal/log-generator variation is
`dK_Q = -d_ln_Q`.  No trace or scalar expectation is taken here.
-/
def logGeneratorVariation (flow : CausalNonequilibriumFlow Op) : Op :=
  -flow.d_ln_Q

/--
Under the commutator comparison, operator-valued entropy production is the
negative variation of the surprisal/log generator:
`[P_forward, P_backward] = d log Q = -dK_Q`.
-/
theorem entropy_production_eq_neg_logGeneratorVariation
    (flow : CausalNonequilibriumFlow Op)
    (hcomm :
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward =
        flow.d_ln_Q) :
    entropy_production flow = -logGeneratorVariation flow := by
  rw [de_rham_potential_equals_entropy_production_of_commutator flow hcomm]
  simp [logGeneratorVariation]

/--
A nonzero operator-valued logarithmic-generator variation rules out detailed
balance.  This is a ring-level consequence of the commutator identity and does
not scalarize entropy production.
-/
theorem nonzero_logGeneratorVariation_implies_not_detailedBalance
    (flow : CausalNonequilibriumFlow Op)
    (hcomm :
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward =
        flow.d_ln_Q)
    (hne : logGeneratorVariation flow ≠ 0) :
    ¬ flow.P_forward * flow.P_backward =
        flow.P_backward * flow.P_forward := by
  intro hdb
  have hzero : entropy_production flow = 0 :=
    (entropy_production_eq_zero_iff_detailed_balance flow).2 hdb
  have hvariation : logGeneratorVariation flow = 0 := by
    rw [entropy_production_eq_neg_logGeneratorVariation flow hcomm] at hzero
    simpa using congrArg Neg.neg hzero
  exact hne hvariation

/-- Scalar reciprocity invariance of the gauge word. -/
theorem gauge_field_covariance
    [Algebra ℝ Op]
    (flow : CausalNonequilibriumFlow Op)
    (lam : ℝ) (hlam : lam ≠ 0) :
    (lam • flow.P_forward) * flow.d_ln_Q * ((1 / lam) • flow.P_backward) =
      thermodynamic_gauge_connection flow := by
  have h2 :
      ((lam • (flow.P_forward * flow.d_ln_Q)) * ((1 / lam) • flow.P_backward)) =
        (1 / lam) • ((lam • (flow.P_forward * flow.d_ln_Q)) * flow.P_backward) := by
    simp
  have h3 :
      (lam • (flow.P_forward * flow.d_ln_Q)) * flow.P_backward =
        lam • (flow.P_forward * flow.d_ln_Q * flow.P_backward) := by
    simp [mul_assoc]
  calc
    (lam • flow.P_forward) * flow.d_ln_Q * ((1 / lam) • flow.P_backward)
        = ((lam • (flow.P_forward * flow.d_ln_Q)) * ((1 / lam) • flow.P_backward)) := by
          rw [smul_mul_assoc]
    _ = (1 / lam) • ((lam • (flow.P_forward * flow.d_ln_Q)) * flow.P_backward) := h2
    _ = (1 / lam) • (lam • (flow.P_forward * flow.d_ln_Q * flow.P_backward)) := by
          rw [h3]
    _ = ((1 / lam) * lam) • (flow.P_forward * flow.d_ln_Q * flow.P_backward) := by
          rw [smul_smul]
    _ = thermodynamic_gauge_connection flow := by
          rw [one_div_mul_cancel hlam, one_smul, thermodynamic_gauge_connection]

/-- Finite Wilson holonomy readout over the thermodynamic gauge word. -/
def wilson_loop_holonomy (flow : CausalNonequilibriumFlow Op) : Op :=
  thermodynamic_gauge_connection flow

/-- Non-abelian curvature defect of the thermodynamic connection against the entropy current. -/
def thermodynamic_curvature (flow : CausalNonequilibriumFlow Op) : Op :=
  thermodynamic_gauge_connection flow * entropy_production flow -
    entropy_production flow * thermodynamic_gauge_connection flow

/-- Holonomy of a finite non-abelian Wilson word. The order of the list is the path order. -/
def nonabelian_wilson_word (path : List Op) : Op :=
  path.foldl (fun acc step => acc * step) 1

/-- Path-ordered finite holonomy of a discrete connection word: finite ordered product
    of infinitesimal factors `(1 + A)`.

    This is a conservative discretization of a Wilson-loop-like transport; it avoids
    analytic path-ordering/integration machinery and remains kernel-safe at the
    ring level.
-/
def finite_wilson_loop (path : List Op) : Op :=
  path.foldl (fun acc step => acc * (1 + step)) 1

/-- The empty non-abelian Wilson word has unit holonomy. -/
theorem nonabelian_wilson_word_nil :
    nonabelian_wilson_word ([] : List Op) = 1 := by
  rfl

/-- The empty finite Wilson loop has unit transport. -/
theorem finite_wilson_loop_nil :
    finite_wilson_loop ([] : List Op) = 1 := by
  rfl

/-- Appending one path-ordered step multiplies non-abelian Wilson word on the right. -/
theorem nonabelian_wilson_word_append_singleton (path : List Op) (step : Op) :
    nonabelian_wilson_word (path ++ [step]) = nonabelian_wilson_word path * step := by
  simp [nonabelian_wilson_word]

/-- Appending one step multiplies finite Wilson loop on the right by `(1 + step)`. -/
theorem finite_wilson_loop_append_singleton (path : List Op) (step : Op) :
    finite_wilson_loop (path ++ [step]) = finite_wilson_loop path * (1 + step) := by
  simp [finite_wilson_loop]

/-- The one-step non-abelian Wilson word recovers that step. -/
theorem nonabelian_wilson_word_singleton (step : Op) :
    nonabelian_wilson_word [step] = step := by
  simp [nonabelian_wilson_word]

/-- The one-step finite Wilson loop is `(1 + step)`. -/
theorem finite_wilson_loop_singleton (step : Op) :
    finite_wilson_loop [step] = 1 + step := by
  simp [finite_wilson_loop]

/-- Read back a supplied finite Wilson-word trace premise. -/
theorem wilson_word_trace_computes_zeta_of_trace_eval
    [Algebra ℝ Op]
    (path : List Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (partitionZeta : ℝ)
    (htrace : trace (nonabelian_wilson_word path) = partitionZeta) :
    trace (nonabelian_wilson_word path) = partitionZeta :=
  htrace

/-- Read back a supplied finite non-abelian Wilson-loop trace premise. -/
theorem finite_wilson_loop_trace_computes_zeta_of_trace_eval
    [Algebra ℝ Op]
    (path : List Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (partitionZeta : ℝ)
    (htrace : trace (finite_wilson_loop path) = partitionZeta) :
    trace (finite_wilson_loop path) = partitionZeta :=
  htrace

/-- Read back a supplied finite curvature trace premise. -/
theorem curvature_trace_computes_zeta_of_trace_eval
    [Algebra ℝ Op]
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (partitionZeta : ℝ)
    (htrace : trace (thermodynamic_curvature flow) = partitionZeta) :
    trace (thermodynamic_curvature flow) = partitionZeta :=
  htrace

/-- Trace-readout schema for a supplied partition comparison hypothesis. -/
theorem wilson_loop_computes_zeta_of_trace_eval
    [Algebra ℝ Op]
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (partitionZeta : ℝ)
    (htrace : trace (wilson_loop_holonomy flow) = partitionZeta) :
    trace (wilson_loop_holonomy flow) = partitionZeta :=
  htrace

end InfoGeometry.Topology.ThermodynamicGauge
