import InfoGeometry.Algebra.NonCommutativeIsometry
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DeformedIdeleAction
import InfoGeometry.Canonical.PrimonCoulombGas
import InfoGeometry.Canonical.VandermondeExclusionBridge

/-!
# InfoGeometry.Canonical.DeformedIdeleDysonBridge

Minimal honest bridge from branch nonunitarity / noncommutativity to finite scalar-node
noncollision for the Dyson/Vandermonde lane.

This file does not claim that branch nonunitarity alone constructs a scalar spectrum.
Instead, it records the exact extra bridge datum needed: a node readout together with an
explicit theorem that range-projection defect forces injectivity of that readout.

#### BUCKET 1: CLOSED FINITE THEOREMS
Given explicit bridge data, range defect implies a nonzero branch commutator,
injective scalar nodes, pairwise noncollision, Vandermonde determinant
nonvanishing, and the finite Dyson/Vandermonde identity.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The bridge depends on an isometric branch operator, a finite scalar readout
`nodes : Fin N → ℝ`, and the named premise
`range_defect_forces_injective_nodes`.

#### BUCKET 3: OPEN CLOSURE DEBT
No theorem here derives the scalar readout from operator algebra alone.  No
theorem asserts Witten's unorientable parity anomaly, GUE asymptotics, KMS/BEC
physics, C*-completion, zeta-zero statistics, or RH consequences.
-/

namespace InfoGeometry.Canonical.DeformedIdeleDysonBridge

section RealBridge

variable {A : Type*} [Ring A] [StarRing A]
variable {N : ℕ}

/--
Explicit bridge data from a nonunitary branch operator to a finite scalar readout.

The key field is `range_defect_forces_injective_nodes`: this is the missing theorem-carrying
bridge from operator-side nonunitarity to scalar-side noncollision.
-/
@[rep_depth thermo]
structure BranchDefectToDysonNodes where
  branch : A
  branch_isometry : star branch * branch = 1
  nodes : Fin N → ℝ
  range_defect_forces_injective_nodes :
    InfoGeometry.Algebra.NonCommutativity.rangeProjection branch ≠ (1 : A) →
      Function.Injective nodes

namespace BranchDefectToDysonNodes

variable (B : BranchDefectToDysonNodes (A := A) (N := N))

/-- Operator-side noncommutativity readout from the explicit range-defect hypothesis. -/
@[rep_depth thermo]
theorem branch_commutator_ne_zero
    (hRange : InfoGeometry.Algebra.NonCommutativity.rangeProjection B.branch ≠ (1 : A)) :
    B.branch * star B.branch - star B.branch * B.branch ≠ 0 := by
  exact InfoGeometry.Algebra.NonCommutativity.isometry_branch_commutator_ne_zero
    B.branch B.branch_isometry hRange

/-- Scalar node injectivity extracted from the bridge hypothesis. -/
@[rep_depth thermo]
theorem nodes_injective_of_range_defect
    (hRange : InfoGeometry.Algebra.NonCommutativity.rangeProjection B.branch ≠ (1 : A)) :
    Function.Injective B.nodes :=
  B.range_defect_forces_injective_nodes hRange

/-- Ordered-pair noncollision extracted from the injective node readout. -/
@[rep_depth thermo]
theorem nodes_noncollision_of_range_defect
    (hRange : InfoGeometry.Algebra.NonCommutativity.rangeProjection B.branch ≠ (1 : A)) :
    ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, B.nodes j ≠ B.nodes i := by
  intro i j hj hEq
  have hinj : Function.Injective B.nodes := B.nodes_injective_of_range_defect hRange
  have hij_eq : j = i := hinj hEq
  have hlt : i < j := Finset.mem_Ioi.mp hj
  rw [hij_eq] at hlt
  exact lt_irrefl i hlt

/--
Finite Dyson/Vandermonde bridge driven by the explicit branch-to-node noncollision theorem.
-/
@[rep_depth thermo]
theorem dyson_to_vandermonde_of_range_defect
    (V : ℝ → ℝ)
    (hRange : InfoGeometry.Algebra.NonCommutativity.rangeProjection B.branch ≠ (1 : A)) :
    InfoGeometry.Canonical.PrimonCoulombGas.dyson_hamiltonian B.nodes V =
      InfoGeometry.Canonical.PrimonCoulombGas.external_potential_energy B.nodes V -
        Real.log ((InfoGeometry.Canonical.PrimonCoulombGas.vandermonde_product_abs B.nodes) ^ 2) := by
  exact InfoGeometry.Canonical.PrimonCoulombGas.dyson_to_vandermonde_bridge
    B.nodes V (B.nodes_noncollision_of_range_defect hRange)

/--
Combined honest packet: the branch commutator is nonzero, and the finite Dyson readout lands on
a proved finite Vandermonde exclusion identity.
-/
@[rep_depth thermo]
theorem commutator_nonzero_and_dyson_bridge
    (V : ℝ → ℝ)
    (hRange : InfoGeometry.Algebra.NonCommutativity.rangeProjection B.branch ≠ (1 : A)) :
    (B.branch * star B.branch - star B.branch * B.branch ≠ 0) ∧
      (InfoGeometry.Canonical.PrimonCoulombGas.dyson_hamiltonian B.nodes V =
        InfoGeometry.Canonical.PrimonCoulombGas.external_potential_energy B.nodes V -
          Real.log ((InfoGeometry.Canonical.PrimonCoulombGas.vandermonde_product_abs B.nodes) ^ 2)) := by
  exact ⟨B.branch_commutator_ne_zero hRange, B.dyson_to_vandermonde_of_range_defect V hRange⟩

/--
Vandermonde determinant nonvanishing on the scalar readout, routed through the explicit
noncollision bridge and the existing owner theorem.
-/
@[rep_depth thermo]
theorem vandermonde_determinant_ne_zero_of_range_defect
    (hRange : InfoGeometry.Algebra.NonCommutativity.rangeProjection B.branch ≠ (1 : A)) :
    InfoGeometry.Canonical.VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant
      (B.nodes : Fin N → ℝ) ≠ 0 := by
  let W : Fin N → ℝ :=
    B.nodes
  have hinj : Function.Injective W := B.nodes_injective_of_range_defect hRange
  exact
    InfoGeometry.Canonical.VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant_ne_zero_iff_injective W |>.mpr hinj

end BranchDefectToDysonNodes

end RealBridge

end InfoGeometry.Canonical.DeformedIdeleDysonBridge
