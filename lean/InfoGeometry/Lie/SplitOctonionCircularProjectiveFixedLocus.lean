import InfoGeometry.Lie.SplitOctonionCircularProjectiveReciprocalFlow
import InfoGeometry.Twistor.ProjectiveNullPolarIncidence

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitOctonionCircularProjectiveFixedLocus

open InfoGeometry.Lie.SplitOctonionCircularProjectiveNullBoundary
open InfoGeometry.Lie.SplitOctonionCircularProjectiveReciprocalFlow
open InfoGeometry.Lie.SplitOctonionCircularReciprocalWittBridge
open InfoGeometry.Lie.SplitOctonionCircularQuadraticCoherence
open InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
open InfoGeometry.Twistor
open InfoGeometry.Twistor.ProjectiveNullPolarIncidence

abbrev Coord := Fin 8 → ℝ
abbrev CircularNullBoundary := TwistorSpace circularPeirceQuadratic

def zeroWeightSubmodule : Submodule ℝ Coord :=
  Submodule.span ℝ {Pi.single 0 1, Pi.single 4 1}

def positiveWeightSubmodule : Submodule ℝ Coord :=
  Submodule.span ℝ {Pi.single 1 1, Pi.single 2 1, Pi.single 3 1}

def negativeWeightSubmodule : Submodule ℝ Coord :=
  Submodule.span ℝ {Pi.single 5 1, Pi.single 6 1, Pi.single 7 1}

theorem hyperbolicFlow_on_zeroWeight (t : ℝ) (x : Coord) (hx : x ∈ zeroWeightSubmodule) :
    hyperbolicFlowCoordinate t x = x := by
  refine Submodule.span_induction (p := fun y _ => hyperbolicFlowCoordinate t y = y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl | rfl <;> ext i <;> fin_cases i <;>
      simp [hyperbolicFlowCoordinate, hyperbolicScale, axialWeight, Pi.smul_apply]
  · simpa [hyperbolicFlowCoordinate, hyperbolicScale]
  · intro y z _ _ hy hz
    rw [map_add, hy, hz]
  · intro a y _ hy
    simpa [map_smul, hy]

theorem hyperbolicFlow_on_positiveWeight (t : ℝ) (x : Coord) (hx : x ∈ positiveWeightSubmodule) :
    hyperbolicFlowCoordinate t x = Real.exp t • x := by
  refine Submodule.span_induction (p := fun y _ => hyperbolicFlowCoordinate t y = Real.exp t • y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl | rfl | rfl <;>
      rw [hyperbolicFlowCoordinate_basis_action] <;>
      simp [axialWeight, smul_eq_mul]
  · simpa [hyperbolicFlowCoordinate, hyperbolicScale]
  · intro y z _ _ hy hz
    rw [map_add, hy, hz, smul_add]
  · intro a y _ hy
    rw [map_smul, hy, smul_smul]
    ring

theorem hyperbolicFlow_on_negativeWeight (t : ℝ) (x : Coord) (hx : x ∈ negativeWeightSubmodule) :
    hyperbolicFlowCoordinate t x = Real.exp (-t) • x := by
  refine Submodule.span_induction (p := fun y _ => hyperbolicFlowCoordinate t y = Real.exp (-t) • y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl | rfl | rfl <;>
      rw [hyperbolicFlowCoordinate_basis_action] <;>
      simp [axialWeight, smul_eq_mul]
  · simpa [hyperbolicFlowCoordinate, hyperbolicScale]
  · intro y z _ _ hy hz
    rw [map_add, hy, hz, smul_add]
  · intro a y _ hy
    rw [map_smul, hy, smul_smul]
    ring

theorem positiveWeight_totallyNull (x : Coord) (hx : x ∈ positiveWeightSubmodule) :
    circularPeirceQuadratic x = 0 := by
  rw [circularPeirceQuadratic_formula]
  have h0 : x 0 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 0 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  have h4 : x 4 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 4 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  have h5 : x 5 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 5 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  have h6 : x 6 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 6 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  have h7 : x 7 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 7 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  simp [h0, h4, h5, h6, h7]

theorem negativeWeight_totallyNull (x : Coord) (hx : x ∈ negativeWeightSubmodule) :
    circularPeirceQuadratic x = 0 := by
  rw [circularPeirceQuadratic_formula]
  have h0 : x 0 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 0 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  have h1 : x 1 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 1 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  have h2 : x 2 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 2 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  have h3 : x 3 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 3 = 0)
      (fun y hy => by rcases hy with rfl | rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  simp [h0, h1, h2, h3]

theorem projective_positiveWeight_fixed (t : ℝ) (x : Coord) (hx_ne : x ≠ 0)
    (hx : x ∈ positiveWeightSubmodule) :
    circularNullBoundaryFlow t (twistorMk circularPeirceQuadratic x hx_ne (positiveWeight_totallyNull x hx)) =
      twistorMk circularPeirceQuadratic x hx_ne (positiveWeight_totallyNull x hx) := by
  rw [circularNullBoundaryFlow_mk_axialFlow]
  apply Subtype.ext
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨Units.mk0 (Real.exp t) (Real.exp_ne_zero t), ?_⟩
  rw [axialFlowCoordinate_eq_hyperbolicFlowCoordinate,
    hyperbolicFlow_on_positiveWeight t x hx]
  simp [Units.smul_def]

theorem projective_negativeWeight_fixed (t : ℝ) (x : Coord) (hx_ne : x ≠ 0)
    (hx : x ∈ negativeWeightSubmodule) :
    circularNullBoundaryFlow t (twistorMk circularPeirceQuadratic x hx_ne (negativeWeight_totallyNull x hx)) =
      twistorMk circularPeirceQuadratic x hx_ne (negativeWeight_totallyNull x hx) := by
  rw [circularNullBoundaryFlow_mk_axialFlow]
  apply Subtype.ext
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨Units.mk0 (Real.exp (-t)) (Real.exp_ne_zero (-t)), ?_⟩
  rw [axialFlowCoordinate_eq_hyperbolicFlowCoordinate,
    hyperbolicFlow_on_negativeWeight t x hx]
  simp [Units.smul_def]

theorem zeroWeight_null_iff (x : Coord) (hx : x ∈ zeroWeightSubmodule) :
    circularPeirceQuadratic x = 0 ↔ (x 0 = 0 ∨ x 4 = 0) := by
  rw [circularPeirceQuadratic_formula]
  have h1 : x 1 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 1 = 0)
      (fun y hy => by rcases hy with rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  have h2 : x 2 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 2 = 0)
      (fun y hy => by rcases hy with rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  have h3 : x 3 = 0 := by
    exact Submodule.span_induction (p := fun y _ => y 3 = 0)
      (fun y hy => by rcases hy with rfl | rfl <;> simp)
      (by simp) (fun y z _ _ hy hz => by simp [hy, hz])
      (fun a y _ hy => by simp [hy]) hx
  simp [h1, h2, h3]

theorem circularNullBoundaryFlow_fixed_iff_of_ne_zero (t : ℝ) (ht : t ≠ 0)
    (p : CircularNullBoundary) :
    circularNullBoundaryFlow t p = p ↔
      (p.1.rep ∈ positiveWeightSubmodule ∨
       p.1.rep ∈ negativeWeightSubmodule ∨
       (p.1.rep ∈ zeroWeightSubmodule ∧ (p.1.rep 0 = 0 ∨ p.1.rep 4 = 0))) := by
  sorry

theorem circularNullBoundaryFlow_preserves_incidence (t : ℝ) (p q : CircularNullBoundary) :
    NullPolarIncident SplitOctonionEllCircularQuadraticCoordinates.circularPeirceQuadratic (circularNullBoundaryFlow t p) (circularNullBoundaryFlow t q) ↔
      NullPolarIncident SplitOctonionEllCircularQuadraticCoordinates.circularPeirceQuadratic p q := by
  exact InfoGeometry.Twistor.ProjectiveNullIsometryIncidence.nullIsometryEquiv_preserves_incidence
    (circularFlowQuadraticIsometry t) p q

end InfoGeometry.Lie.SplitOctonionCircularProjectiveFixedLocus
