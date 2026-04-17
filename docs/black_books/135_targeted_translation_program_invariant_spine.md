# Chapter 135: Targeted Translation Program Along the Invariant Spine

> "Exploration may be Jungian. Closure must be Pauli."

At this stage, the requirement is not "more theorems" in the abstract. The requirement is a targeted translation program that expands the Rosetta layer along the same invariant spine already fixed:

```text
Delta -> log Delta -> modular flow -> projector geometry -> Cl(1,1) action -> anomaly
```

This chapter records a prioritized theorem program: the minimal set needed to close the operator/geometry/thermodynamics stack.

## Priority 1: Modular Core (Must Be Completed)

These are non-negotiable.

### 1. Modular Flow = Lorentz Boost (full theorem)

The partial lane already exists in `UnruhKMS.lean`. Complete the channel action:

```lean
theorem modular_flow_scales_uPlus
  exp(tK) • uPlus = Real.exp t * uPlus

theorem modular_flow_scales_uMinus
  exp(tK) • uMinus = Real.exp (-t) * uMinus
```

This is the Lorentz representation theorem on polarized channels.

### 2. Modular Hamiltonian = Cartan Generator

Formalize the grading-respecting commutator action:

```lean
theorem K_is_Cartan :
  forall A, commutator K A respects_grading_decomposition
```

### 3. Functional Calculus Compatibility (Critical)

Seal the `Delta -> K` passage:

```lean
theorem log_defined_on_Preg :
  spectrum (Preg Delta) ⊆ positive_real_axis
```

and

```lean
noncomputable def K := -log (Preg Delta)
```

## Priority 2: Projector/Anomaly Geometry

This is the unique repo contribution.

### 4. Spectral vs. Metric Support Mismatch

With `chi := [P_D, P_L]`, formalize behavior:

```lean
theorem anomaly_vanishes_iff_alignment :
  chi = 0 ↔ spectral_support = metric_support
```

### 5. Anomaly as Curvature/Obstruction

```lean
theorem anomaly_as_obstruction :
  chi ≠ 0 -> no_simultaneous_diagonalization
```

### 6. Transport Invariance of Projectors

```lean
theorem Preg_transport_invariant :
  T * Preg * T⁻¹ = Preg
```

for the allowed flow class.

## Priority 3: Information Geometry Layer

### 7. Relative Entropy as Modular Expectation

Replace trace-rooted form with state-functional modular form:

```lean
noncomputable def relativeEntropy (phi psi) :=
  phi (K_psi_over_phi)

theorem entropy_nonnegative :
  relativeEntropy phi psi >= 0
```

### 8. KMS Condition (Correct Form)

Use the flow-first statement, then transliterate to doubled/Krein real form:

```lean
theorem KMS_condition :
  omega (A * alpha_t B) = omega (alpha_(t_plus_i_beta) B * A)
```

### 9. Unruh Effect Completion

```lean
theorem wedge_restriction_is_KMS :
  restricted_state_satisfies_KMS_wrt_boost
```

## Priority 4: Cl(1,1) Algebra Completion

### 10. Ladder Algebra

Promote as canonical lane theorem:

```lean
theorem commutator_uPlus_uMinus_in_gZero :
  commutator uPlus uMinus ∈ gZero
```

### 11. Full Decomposition Isomorphism

```lean
theorem End_decomposes :
  End(H) ≃ gPlus ⊕ gZero ⊕ gMinus
```

### 12. Exponential Map Closure

```lean
theorem exp_closure :
  exp (a*K + b*eps) generates_full_action
```

## Priority 5: Spectroscopy/Measurement Theory

### 13. Measurement Relativity

```lean
theorem measurement_is_relative :
  readout depends_on chosen_reference_state_and_gauge
```

### 14. Spectral Response Decomposition

```lean
theorem response_split :
  A = symmetric_response + antisymmetric_response
```

### 15. Channel Decomposition Theorem

Map channels to interpretation lanes:

- `gPlus / gMinus / gZero`
- `phase / entropy / neutral`

## Priority 6: Path/Optimization Layer

### 16. Path Action Functional

```lean
noncomputable def PathAction :=
  sum (modular_term + anomaly_term + transport_term)
```

### 17. Gibbs Weight

```lean
noncomputable def pathWeight := Real.exp (-PathAction)
```

### 18. Least Action Theorem

```lean
theorem flat_path_maximizes_weight :
  flat_path -> maximal_weight
```

## Priority 7: Deep Structural Theorems (Long-Term)

### 19. Modular Flow = Geometric Flow

```lean
theorem modular_flow_is_geometric_transform :
  flow acts_as_geometric_transformation
```

### 20. Phase = Internal Axis

```lean
theorem phase_internal_axis :
  i_shadow ≈ J_comp_eps
```

### 21. Noncommutative -> Scalar Shadow

```lean
theorem operator_to_scalar_shadow :
  operator_dynamics -> scalar_action
```

## Master Build Pipeline

```text
Cl(1,1) algebra
-> projector decomposition
-> modular operator Delta
-> logarithmic generator K
-> modular flow
-> anomaly curvature
-> entropy / information
-> path action
-> optimization / inference
```

## Most Important Immediate Next 3 Steps

1. Finish `uPlus / uMinus` algebra as canonical lane.
2. Prove modular flow acts diagonally on these channels.
3. Seal the `log (Delta | Preg)` theorem.

These three unlock the corridor.

## Final Insight

This is not theorem accumulation. It is closure construction: one algebra, many bases.

- geometry
- thermodynamics
- quantum structure
- computation

are treated as the same object in different representations.
