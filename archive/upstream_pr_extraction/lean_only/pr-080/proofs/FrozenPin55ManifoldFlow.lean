import proofs.SU2ValencePairVQE

/-!
# Frozen `O(5,5)` / `Pin(5,5)` manifold-flow

The CUAI equivariant-manifold-flow code learns invariant densities on a
manifold by using symmetry-compatible vector fields.  For our finite
Hamiltonian layer, the Lean formulation is:

* embed the active nuclear/valence coordinates into a 10-dimensional
  `O(5,5)` carrier;
* freeze protected coordinates by removing their generator rows/columns;
* learn only the active parameters.

The executable script checks the numerical `O(5,5)` invariant
`xᵀ η x` under `exp(tA)` for projected `o(5,5)` generators.
-/

namespace FrozenPin55ManifoldFlow

/-- The vector representation dimension of `O(5,5)`. -/
def o55CarrierDimension : ℕ := 5 + 5

/-- Lie algebra dimension of `O(5,5)`: `10*9/2 = 45`. -/
def o55LieAlgebraDimension : ℕ :=
  o55CarrierDimension * (o55CarrierDimension - 1) / 2

/-- Four frozen coordinates leaves six active coordinates in the toy model. -/
def defaultFrozenCoordinates : ℕ := 4

def defaultActiveCoordinates : ℕ :=
  o55CarrierDimension - defaultFrozenCoordinates

@[simp] theorem o55_carrier_dimension_eq :
    o55CarrierDimension = 10 := by
  norm_num [o55CarrierDimension]

@[simp] theorem o55_lie_algebra_dimension_eq :
    o55LieAlgebraDimension = 45 := by
  norm_num [o55LieAlgebraDimension, o55CarrierDimension]

@[simp] theorem default_active_coordinates_eq :
    defaultActiveCoordinates = 6 := by
  norm_num [defaultActiveCoordinates, o55CarrierDimension,
    defaultFrozenCoordinates]

/-- Number of antisymmetric active-pair parameters after freezing four
coordinates: `6*5/2 = 15`. -/
def defaultActivePairParameters : ℕ :=
  defaultActiveCoordinates * (defaultActiveCoordinates - 1) / 2

@[simp] theorem default_active_pair_parameters_eq :
    defaultActivePairParameters = 15 := by
  norm_num [defaultActivePairParameters, defaultActiveCoordinates,
    o55CarrierDimension, defaultFrozenCoordinates]

/-- Decoupled bookkeeping: frozen energy plus active flow energy. -/
def frozenDecoupledEnergy (frozen active : ℝ) : ℝ :=
  frozen + active

theorem frozenDecoupledEnergy_comm (frozen active : ℝ) :
    frozenDecoupledEnergy frozen active =
      frozenDecoupledEnergy active frozen := by
  unfold frozenDecoupledEnergy
  ring

/-- Capstone: finite `O(5,5)` bookkeeping and the four-block spin-2 VQE
parameter count. -/
theorem frozen_pin55_manifold_flow_synthesis
    (frozen active : ℝ) :
    o55CarrierDimension = 10 ∧
    o55LieAlgebraDimension = 45 ∧
    defaultActiveCoordinates = 6 ∧
    defaultActivePairParameters = 15 ∧
    frozenDecoupledEnergy frozen active =
      frozenDecoupledEnergy active frozen ∧
    SU2ValencePairVQE.spin2VQEParamCount 4 = 4 := by
  have hCarrier : o55CarrierDimension = 10 := o55_carrier_dimension_eq
  have hLie : o55LieAlgebraDimension = 45 := o55_lie_algebra_dimension_eq
  have hActive : defaultActiveCoordinates = 6 :=
    default_active_coordinates_eq
  have hPairs : defaultActivePairParameters = 15 :=
    default_active_pair_parameters_eq
  have hEnergy :
      frozenDecoupledEnergy frozen active =
        frozenDecoupledEnergy active frozen :=
    frozenDecoupledEnergy_comm frozen active
  have hVQE : SU2ValencePairVQE.spin2VQEParamCount 4 = 4 :=
    SU2ValencePairVQE.spin2_vqe_params_four_blocks
  refine And.intro ?_ ?_
  · rw [hCarrier]
  · refine And.intro ?_ ?_
    · rw [hLie]
    · refine And.intro ?_ ?_
      · rw [hActive]
      · refine And.intro ?_ ?_
        · rw [hPairs]
        · refine And.intro ?_ ?_
          · rw [hEnergy]
          · rw [hVQE]

end FrozenPin55ManifoldFlow
