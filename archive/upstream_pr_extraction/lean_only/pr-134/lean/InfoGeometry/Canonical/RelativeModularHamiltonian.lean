import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Meta.Architecture

open scoped BigOperators

/-!
# Relative Modular Surprisal

Finite operator-owner lift with `Δ` primary and `𝒦 := -log Δ` as the derived
relative surprisal operator on the diagonal commuting lane.

This file sits between:
- `RelativeModularOperator`, which owns the finite relative modular operator
  `Δ(q,q₀)`,
- `RelativeSurprisalOperatorLift`, which packages first-quantized readouts and
  downstream compatibility surfaces.

Methodological contract:
- operator ownership is carried by `Δ`,
- `𝒦` is derived from `Δ` by logarithmic readout on the diagonal (finite
  commuting spectral lane),
- physical Hamiltonian readouts remain specialized shadows of the operator
  surprisal owner.
-/

namespace InfoGeometry.Canonical.RelativeModularHamiltonian

open InfoGeometry.Canonical.PositiveRayCore
open RelativePotentialCore
open RelativeModularOperator
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

section Finite

variable {n : ℕ} [Nonempty (Fin n)]

/-
Diagonal logarithmic functional-calculus readout on a finite operator:
`𝒦(Δ) := diag(-log Δᵢᵢ)`.

The historical declaration below retains the old Hamiltonian name for
compatibility; the canonical surprisal aliases are defined at the end of the
owner.
-/
noncomputable def modularHamiltonianFromDiagonal (Δ : FinMat n) : FinMat n :=
  diagMatrix (fun i => -Real.log (Δ i i))

omit [Nonempty (Fin n)] in
@[simp] theorem modularHamiltonianFromDiagonal_diag
    (Δ : FinMat n) (i : Fin n) :
    modularHamiltonianFromDiagonal (n := n) Δ i i = -Real.log (Δ i i) := by
  simp [modularHamiltonianFromDiagonal, diagMatrix]

omit [Nonempty (Fin n)] in
@[simp] theorem modularHamiltonianFromDiagonal_offdiag
    (Δ : FinMat n) {i j : Fin n} (hij : i ≠ j) :
    modularHamiltonianFromDiagonal (n := n) Δ i j = 0 := by
  simp [modularHamiltonianFromDiagonal, diagMatrix, hij]

/-/ Relative modular Hamiltonian operator induced by the canonical finite `Δ(q,q₀)`. -/
@[rep_depth operator]
noncomputable def relativeModularHamiltonianOperator
    (q q0 : PositiveRay (Fin n)) : FinMat n :=
  modularHamiltonianFromDiagonal (n := n)
    (relativeModularOperator (n := n) q q0)

theorem relativeModularHamiltonianOperator_diag
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeModularHamiltonianOperator (n := n) q q0 i i
      = relativeModularPotential (α := Fin n) q q0 i := by
  rw [relativeModularHamiltonianOperator, modularHamiltonianFromDiagonal_diag]
  exact (relativeModularPotential_eq_neg_log_relativeModularOperator_diag (n := n) q q0 i).symm

theorem relativeModularHamiltonianOperator_offdiag
    (q q0 : PositiveRay (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    relativeModularHamiltonianOperator (n := n) q q0 i j = 0 := by
  rw [relativeModularHamiltonianOperator]
  exact modularHamiltonianFromDiagonal_offdiag (n := n)
    (Δ := relativeModularOperator (n := n) q q0) (hij := hij)

/-- Operator-level `K = -log Δ` in the finite commuting diagonal lane. -/
@[rep_depth operator]
theorem relativeModularHamiltonianOperator_eq_diag_relativeModularPotential
    (q q0 : PositiveRay (Fin n)) :
    relativeModularHamiltonianOperator (n := n) q q0
      = diagMatrix (fun i => relativeModularPotential (α := Fin n) q q0 i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [relativeModularHamiltonianOperator_diag]
    rw [diagMatrix, Matrix.diagonal_apply_eq]
  · rw [relativeModularHamiltonianOperator_offdiag (hij := hij)]
    rw [diagMatrix, Matrix.diagonal_apply_ne _ hij]

/--
Commuting cocycle lift in the finite diagonal lane:
`K(q,q₁) = K(q,q₀) + K(q₀,q₁)`.
-/
@[rep_depth operator]
theorem relativeModularHamiltonianOperator_cocycle
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeModularHamiltonianOperator (n := n) q q1
      = relativeModularHamiltonianOperator (n := n) q q0
          + relativeModularHamiltonianOperator (n := n) q0 q1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.add_apply, relativeModularHamiltonianOperator_diag,
      relativeModularHamiltonianOperator_diag, relativeModularHamiltonianOperator_diag]
    exact relativeModularPotential_cocycle (q := q) (q0 := q0) (q1 := q1) i
  · rw [relativeModularHamiltonianOperator_offdiag (hij := hij)]
    rw [Matrix.add_apply, relativeModularHamiltonianOperator_offdiag (hij := hij),
      relativeModularHamiltonianOperator_offdiag (hij := hij)]
    ring

/-!
## Canonical surprisal terminology

The finite positive deformation is `Δ`; its additive logarithmic coordinate is
therefore an operator surprisal.  The older `Hamiltonian` names remain the
compatibility API for existing imports.
-/

noncomputable abbrev relativeSurprisalFromDiagonal {n : ℕ}
    (Δ : FinMat n) : FinMat n :=
  modularHamiltonianFromDiagonal Δ

noncomputable abbrev relativeSurprisalOperator {n : ℕ} [Nonempty (Fin n)]
    (q q0 : PositiveRay (Fin n)) : FinMat n :=
  relativeModularHamiltonianOperator q q0

theorem relativeSurprisalOperator_diag
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeSurprisalOperator (n := n) q q0 i i =
      relativeModularPotential (α := Fin n) q q0 i :=
  relativeModularHamiltonianOperator_diag (n := n) q q0 i

theorem relativeSurprisalOperator_cocycle
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeSurprisalOperator (n := n) q q1 =
      relativeSurprisalOperator (n := n) q q0 +
        relativeSurprisalOperator (n := n) q0 q1 :=
  relativeModularHamiltonianOperator_cocycle (n := n) q q0 q1

/--
The finite operator-level volume identity:
the negative logarithm of the determinant shadow is the trace of the
relative surprisal operator `𝒦 = -log Δ`.

This is stated over the canonical finite `Δ` owner; it is not a separate
fixed-size matrix model.
-/
@[rep_depth operator, capstone]
theorem neg_log_relativeModularVolumeShadow_eq_trace_relativeSurprisalOperator
    (q q0 : PositiveRay (Fin n)) :
    -Real.log (relativeModularVolumeShadow (n := n) q q0) =
      Matrix.trace (relativeSurprisalOperator (n := n) q q0) := by
  change relativeModularVolumePotential (n := n) q q0 =
    Matrix.trace (relativeSurprisalOperator (n := n) q q0)
  rw [relativeModularVolumePotential_eq_sum_relativeModularPotential]
  rw [Matrix.trace]
  refine Finset.sum_congr rfl ?_
  intro i hi
  change relativeModularPotential (α := Fin n) q q0 i =
    relativeSurprisalOperator (n := n) q q0 i i
  rw [relativeSurprisalOperator_diag]

/-- Scalar shadow: diagonal-average readout of the operator owner `K(q,q₀)`. -/
@[rep_depth operator]
noncomputable def relativeModularHamiltonianExpectation
    (q q0 : PositiveRay (Fin n)) : ℝ :=
  (n : ℝ)⁻¹ * diagonalMass (relativeModularHamiltonianOperator (n := n) q q0)

/-- Compatibility with the established finite owner readout. -/
@[rep_depth thermo, capstone]
theorem relativeModularHamiltonianExpectation_eq_readout
    (q q0 : PositiveRay (Fin n)) :
    relativeModularHamiltonianExpectation (n := n) q q0
      = relativeModularHamiltonianReadout (n := n) q q0 := by
  unfold relativeModularHamiltonianExpectation relativeModularHamiltonianReadout
  unfold diagonalMass relativeModularHamiltonianOperator
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [modularHamiltonianFromDiagonal_diag]

/--
Operator-shadow relation: the expectation of `K` equals the normalized
log-volume Hamiltonian readout.
-/
@[rep_depth thermo, capstone]
theorem relativeModularHamiltonianExpectation_eq_inv_card_mul_relativeModularVolumePotential
    (q q0 : PositiveRay (Fin n)) :
    relativeModularHamiltonianExpectation (n := n) q q0
      = (n : ℝ)⁻¹ * relativeModularVolumePotential (n := n) q q0 := by
  rw [relativeModularHamiltonianExpectation_eq_readout]
  exact relativeModularHamiltonianReadout_eq_inv_card_mul_relativeModularVolumePotential
    (n := n) q q0

@[simp, rep_depth thermo, capstone]
theorem relativeModularHamiltonianExpectation_self
    (q : PositiveRay (Fin n)) :
    relativeModularHamiltonianExpectation (n := n) q q = 0 := by
  rw [relativeModularHamiltonianExpectation_eq_readout]
  exact relativeModularHamiltonianReadout_self (n := n) q

/-- Canonical name for the diagonal-average surprisal readout. -/
noncomputable abbrev relativeSurprisalExpectation {n : ℕ} [Nonempty (Fin n)]
    (q q0 : PositiveRay (Fin n)) : ℝ :=
  relativeModularHamiltonianExpectation q q0

theorem relativeSurprisalExpectation_eq_readout
    (q q0 : PositiveRay (Fin n)) :
    relativeSurprisalExpectation (n := n) q q0 =
      relativeModularHamiltonianReadout (n := n) q q0 :=
  relativeModularHamiltonianExpectation_eq_readout (n := n) q q0

end Finite

end InfoGeometry.Canonical.RelativeModularHamiltonian
