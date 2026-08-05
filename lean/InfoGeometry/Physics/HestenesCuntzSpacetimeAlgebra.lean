import InfoGeometry.Physics.LorentzChiralCuntzBridge

/-!
# Hestenes-style spacetime algebra over the Cuntz-deformed operator layer

This file packages the finite algebraic ingredients for a Hestenes/geometric
algebra of physics spine without claiming the full analytic/geometric theory:

* complexified four-vectors are Pauli-soldered to `2×2` operator matrices;
* dual coordinate readouts recover the four-vector components;
* the determinant of the paravector operator is the Minkowski quadratic;
* `SL(2,ℂ)` acts on the chiral algebra and solders to vectors;
* the complexified Poincaré semidirect action has its group law;
* Fierz completeness and the Cuntz-deformed odd--odd bracket are reused.

The Hestenes/STA content here is the finite Pauli/paravector Clifford spine:
the spatial Pauli generators square to `1` and anticommute, while spacetime
norms are represented by the determinant of the soldered paravector.
-/

noncomputable section

namespace InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra

open Matrix
open ChiralPoincareSouriauBridge
open LorentzChiralCuntzBridge

/-- Local polarization pairing from the quadratic form. -/
def hestenesPair (P Q : FourMomentum) : ℂ :=
  (1 / 2 : ℂ) *
    (minkowskiSq (addFourMomentum P Q) - minkowskiSq P - minkowskiSq Q)

/-- Explicit coordinate formula for the polarized Hestenes/Minkowski pairing. -/
theorem hestenesPair_apply (P Q : FourMomentum) :
    hestenesPair P Q = P.E * Q.E - P.px * Q.px - P.py * Q.py - P.pz * Q.pz := by
  cases P
  cases Q
  simp [hestenesPair, addFourMomentum, minkowskiSq]
  ring

/-- The coordinate duals recover the components of a soldered paravector. -/
theorem coordinate_duals_recover (P : FourMomentum) :
    recoverE (pauliMomentum P) = P.E ∧
    recoverPx (pauliMomentum P) = P.px ∧
    recoverPy (pauliMomentum P) = P.py ∧
    recoverPz (pauliMomentum P) = P.pz := by
  simp

/-- Re-soldering the coordinate readouts of an operator recovers that operator. -/
theorem coordinate_operator_roundtrip (X : M2C) :
    pauliMomentum (fourMomentumOfMatrix X) = X := by
  exact pauliMomentum_fourMomentumOfMatrix X

/-- Re-soldering recovered coordinates of a soldered vector is identity. -/
theorem vector_coordinate_roundtrip (P : FourMomentum) :
    fourMomentumOfMatrix (pauliMomentum P) = P := by
  apply fourMomentum_ext_of_pauliMomentum_eq
  exact coordinate_operator_roundtrip (pauliMomentum P)

/-- The Hestenes paravector determinant is the Minkowski quadratic. -/
theorem hestenes_metric_from_determinant (P : FourMomentum) :
    (pauliMomentum P).det = minkowskiSq P := by
  exact det_pauliMomentum P

/-- Lorentz covariance of the finite Hestenes norm. -/
theorem hestenes_lorentz_covariance (g : SL2C) (P : FourMomentum) :
    minkowskiSq (spinLorentzAction g P) = minkowskiSq P := by
  exact spinLorentzAction_preserves_minkowskiSq g P

/-- Poincaré action obeys the semidirect-product group law. -/
theorem hestenes_poincare_group_law
    (G H : ChiralPoincareElement) (P : FourMomentum) :
    chiralPoincareAct (chiralPoincareComp G H) P =
      chiralPoincareAct G (chiralPoincareAct H P) := by
  exact chiralPoincareAct_comp G H P

/-- Fierz completeness supplies the finite soldering completeness relation. -/
theorem hestenes_fierz_completeness : chiralFierzStatement := by
  exact FierzIdentities.chiral_fierz_identity

/-! ## Pauli/Clifford finite spatial spine -/

/-- Matrix anticommutator. -/
def antiM (A B : M2C) : M2C := A * B + B * A

theorem pauli_sigma1_sq : σ1 * σ1 = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ1, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli_sigma2_sq : σ2 * σ2 = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [σ2, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem pauli_sigma3_sq : σ3 * σ3 = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ3, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli_sigma1_anti_sigma2 : antiM σ1 σ2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antiM, σ1, σ2]

theorem pauli_sigma1_anti_sigma3 : antiM σ1 σ3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antiM, σ1, σ3]

theorem pauli_sigma2_anti_sigma3 : antiM σ2 σ3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antiM, σ2, σ3]

/-- Spatial Pauli generators realize the finite Clifford anticommutation spine. -/
theorem hestenes_pauli_clifford_spatial_spine :
    σ1 * σ1 = (1 : M2C) ∧
    σ2 * σ2 = (1 : M2C) ∧
    σ3 * σ3 = (1 : M2C) ∧
    antiM σ1 σ2 = 0 ∧
    antiM σ1 σ3 = 0 ∧
    antiM σ2 σ3 = 0 := by
  constructor
  · exact pauli_sigma1_sq
  constructor
  · exact pauli_sigma2_sq
  constructor
  · exact pauli_sigma3_sq
  constructor
  · exact pauli_sigma1_anti_sigma2
  constructor
  · exact pauli_sigma1_anti_sigma3
  · exact pauli_sigma2_anti_sigma3

/-! ## Cuntz-deformed operator layer -/

/-- The Cuntz-deformed odd--odd bracket is the affine Lie/Jordan split. -/
theorem hestenes_cuntz_deformed_super_poincare (β : ℂ) (x y : M2C) :
    SupergradedCuntzBdG.affineSuperBracket β SupergradedCuntzBdG.Z2Parity.odd
        SupergradedCuntzBdG.Z2Parity.odd x y =
      (1 - β) • SupergradedCuntzBdG.lieBracket x y +
        β • SupergradedCuntzBdG.jordanProduct x y := by
  exact CuntzDeformedSuperPoincare.cuntzDeformed_odd_odd_lie_jordan_split β x y

/-- Lorentz transport of the Cuntz-deformed operator super-Poincaré relation. -/
theorem hestenes_cuntz_lorentz_transport
    (g : SL2C) (S : CuntzDeformedSuperPoincare.ChiralOperatorPresentation) :
    CuntzDeformedSuperPoincare.transportedRelation
      (spinMatrix g) (spinMatrix g⁻¹) S := by
  exact sl2c_transportedRelation_holds g S

/-- Consolidated finite Hestenes/Cuntz spacetime algebra package. -/
theorem hestenes_cuntz_spacetime_synthesis
    (g : SL2C) (G H : ChiralPoincareElement) (P Q : FourMomentum)
    (S : CuntzDeformedSuperPoincare.ChiralOperatorPresentation)
    (β : ℂ) (x y : M2C) :
    recoverE (pauliMomentum P) = P.E ∧
    recoverPx (pauliMomentum P) = P.px ∧
    recoverPy (pauliMomentum P) = P.py ∧
    recoverPz (pauliMomentum P) = P.pz ∧
    (pauliMomentum P).det = minkowskiSq P ∧
    hestenesPair P Q = P.E * Q.E - P.px * Q.px - P.py * Q.py - P.pz * Q.pz ∧
    minkowskiSq (spinLorentzAction g P) = minkowskiSq P ∧
    chiralPoincareAct (chiralPoincareComp G H) P =
      chiralPoincareAct G (chiralPoincareAct H P) ∧
    chiralFierzStatement ∧
    σ1 * σ1 = (1 : M2C) ∧
    σ2 * σ2 = (1 : M2C) ∧
    σ3 * σ3 = (1 : M2C) ∧
    antiM σ1 σ2 = 0 ∧
    antiM σ1 σ3 = 0 ∧
    antiM σ2 σ3 = 0 ∧
    CuntzDeformedSuperPoincare.transportedRelation
      (spinMatrix g) (spinMatrix g⁻¹) S ∧
    SupergradedCuntzBdG.affineSuperBracket β SupergradedCuntzBdG.Z2Parity.odd
        SupergradedCuntzBdG.Z2Parity.odd x y =
      (1 - β) • SupergradedCuntzBdG.lieBracket x y +
        β • SupergradedCuntzBdG.jordanProduct x y := by
  constructor
  · exact (coordinate_duals_recover P).1
  constructor
  · exact (coordinate_duals_recover P).2.1
  constructor
  · exact (coordinate_duals_recover P).2.2.1
  constructor
  · exact (coordinate_duals_recover P).2.2.2
  constructor
  · exact hestenes_metric_from_determinant P
  constructor
  · exact hestenesPair_apply P Q
  constructor
  · exact hestenes_lorentz_covariance g P
  constructor
  · exact hestenes_poincare_group_law G H P
  constructor
  · exact hestenes_fierz_completeness
  constructor
  · exact pauli_sigma1_sq
  constructor
  · exact pauli_sigma2_sq
  constructor
  · exact pauli_sigma3_sq
  constructor
  · exact pauli_sigma1_anti_sigma2
  constructor
  · exact pauli_sigma1_anti_sigma3
  constructor
  · exact pauli_sigma2_anti_sigma3
  constructor
  · exact hestenes_cuntz_lorentz_transport g S
  · exact hestenes_cuntz_deformed_super_poincare β x y

end InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra

end noncomputable section
