import InfoGeometry.Lie.SplitOctonionCircularProjectiveReciprocalFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

abbrev Coord := InfoGeometry.Algebra.FiniteSpin.Vec8R
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
    rcases hy with rfl | rfl
    · rw [hyperbolicFlowCoordinate_basis_action]
      have h : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 0 = 0 := rfl
      rw [h, mul_zero, Real.exp_zero, one_smul]
    · rw [hyperbolicFlowCoordinate_basis_action]
      have h : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 4 = 0 := rfl
      rw [h, mul_zero, Real.exp_zero, one_smul]
  · exact map_zero _
  · intro y z _ _ hy hz
    rw [map_add, hy, hz]
  · intro a y _ hy
    rw [map_smul, hy]

theorem hyperbolicFlow_on_positiveWeight (t : ℝ) (x : Coord) (hx : x ∈ positiveWeightSubmodule) :
    hyperbolicFlowCoordinate t x = Real.exp t • x := by
  refine Submodule.span_induction (p := fun y _ => hyperbolicFlowCoordinate t y = Real.exp t • y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl | rfl | rfl
    · rw [hyperbolicFlowCoordinate_basis_action]
      have h : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 1 = 1 := rfl
      rw [h, mul_one]
    · rw [hyperbolicFlowCoordinate_basis_action]
      have h : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 2 = 1 := rfl
      rw [h, mul_one]
    · rw [hyperbolicFlowCoordinate_basis_action]
      have h : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 3 = 1 := rfl
      rw [h, mul_one]
  · simp
  · intro y z _ _ hy hz
    rw [map_add, hy, hz, smul_add]
  · intro a y _ hy
    rw [map_smul, hy, smul_smul, mul_comm, ← smul_smul]

theorem hyperbolicFlow_on_negativeWeight (t : ℝ) (x : Coord) (hx : x ∈ negativeWeightSubmodule) :
    hyperbolicFlowCoordinate t x = Real.exp (-t) • x := by
  refine Submodule.span_induction (p := fun y _ => hyperbolicFlowCoordinate t y = Real.exp (-t) • y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl | rfl | rfl
    · rw [hyperbolicFlowCoordinate_basis_action]
      have h : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 5 = -1 := rfl
      rw [h, mul_neg_one]
    · rw [hyperbolicFlowCoordinate_basis_action]
      have h : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 6 = -1 := rfl
      rw [h, mul_neg_one]
    · rw [hyperbolicFlowCoordinate_basis_action]
      have h : InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight 7 = -1 := rfl
      rw [h, mul_neg_one]
  · simp
  · intro y z _ _ hy hz
    rw [map_add, hy, hz, smul_add]
  · intro a y _ hy
    rw [map_smul, hy, smul_smul, mul_comm, ← smul_smul]

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
  simp

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
  simp

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
  rcases p with ⟨p, hp⟩
  induction p using Projectivization.ind with
  | h x hx =>
      obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℝ x hx
      have hu_ne : (u : ℝ) ≠ 0 := u.ne_zero
      have h_rep_pos : (Projectivization.mk ℝ x hx).rep ∈ positiveWeightSubmodule ↔ x ∈ positiveWeightSubmodule := by
        rw [← hu, Units.smul_def]
        change ((u : ℝ) • x ∈ positiveWeightSubmodule) ↔ _
        exact Submodule.smul_mem_iff _ hu_ne
      have h_rep_neg : (Projectivization.mk ℝ x hx).rep ∈ negativeWeightSubmodule ↔ x ∈ negativeWeightSubmodule := by
        rw [← hu, Units.smul_def]
        change ((u : ℝ) • x ∈ negativeWeightSubmodule) ↔ _
        exact Submodule.smul_mem_iff _ hu_ne
      have h_rep_zero : (Projectivization.mk ℝ x hx).rep ∈ zeroWeightSubmodule ↔ x ∈ zeroWeightSubmodule := by
        rw [← hu, Units.smul_def]
        change ((u : ℝ) • x ∈ zeroWeightSubmodule) ↔ _
        exact Submodule.smul_mem_iff _ hu_ne
      have h_rep_0 : (Projectivization.mk ℝ x hx).rep 0 = 0 ↔ x 0 = 0 := by
        rw [← hu, Units.smul_def]; simp [hu_ne]
      have h_rep_4 : (Projectivization.mk ℝ x hx).rep 4 = 0 ↔ x 4 = 0 := by
        rw [← hu, Units.smul_def]; simp [hu_ne]
      rw [h_rep_pos, h_rep_neg, h_rep_zero, h_rep_0, h_rep_4]
      have hQ : circularPeirceQuadratic x = 0 :=
        (isNull_mk_iff circularPeirceQuadratic x hx).mp hp
      have hproj_aux : hyperbolicFlowCoordinate t x ≠ 0 := by
        intro H; apply hx
        have H2 : (hyperbolicFlowCoordinateEquiv t) x = 0 := H
        exact (hyperbolicFlowCoordinateEquiv t).injective (by simpa using H2)
      have hproj : circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩ = ⟨Projectivization.mk ℝ x hx, hp⟩ ↔
          Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) hproj_aux = Projectivization.mk ℝ x hx := by
        constructor
        · intro h
          have h1 : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ x hx := congr_arg Subtype.val h
          have aux : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) hproj_aux := by
            have := circularNullBoundaryFlow_mk_axialFlow t x hx hp
            have h_eq : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (axialFlowCoordinate t x) (by rw [axialFlowCoordinate_eq_hyperbolicFlowCoordinate]; exact hproj_aux) := congr_arg Subtype.val this
            simpa only [axialFlowCoordinate_eq_hyperbolicFlowCoordinate t] using h_eq
          rw [aux] at h1
          exact h1
        · intro h
          apply Subtype.ext
          have aux : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) hproj_aux := by
            have := circularNullBoundaryFlow_mk_axialFlow t x hx hp
            have h_eq : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (axialFlowCoordinate t x) (by rw [axialFlowCoordinate_eq_hyperbolicFlowCoordinate]; exact hproj_aux) := congr_arg Subtype.val this
            simpa only [axialFlowCoordinate_eq_hyperbolicFlowCoordinate t] using h_eq
          rw [aux, h]
      have hsep : Real.exp t ≠ Real.exp (-t) := by
        intro h
        apply ht
        have := Real.exp_injective h
        linarith
      constructor
      · intro hfixed
        have hfixed2 := hproj.mp hfixed
        have he : ∃ a : ℝ, a • x = hyperbolicFlowCoordinate t x := (Projectivization.mk_eq_mk_iff' ℝ (hyperbolicFlowCoordinate t x) x hproj_aux hx).mp hfixed2
        obtain ⟨a, hax⟩ := he
        have hc (i : Fin 8) : a = Real.exp (t * InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i) ∨ x i = 0 := by
          have hax'' := congrFun hax i
          simpa [hyperbolicFlowCoordinate_apply, smul_eq_mul] using hax''
        have kill (i : Fin 8) (c : ℝ) (he : a ≠ c)
            (hi : Real.exp (t * InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i) = c) :
            x i = 0 := by
          have := hc i
          rcases this with (ha | hxi)
          · exfalso; apply he; rw [ha, hi]
          · exact hxi
        have memPos : ∀ {y : Coord}, y 0 = 0 → y 4 = 0 → y 5 = 0 → y 6 = 0 → y 7 = 0 → y ∈ positiveWeightSubmodule := by
          intro y h0 h4 h5 h6 h7
          rw [show y = y 1 • (Pi.single 1 1 : Coord) + y 2 • (Pi.single 2 1 : Coord) + y 3 • (Pi.single 3 1 : Coord) by
            ext i; fin_cases i <;> simp [h0, h4, h5, h6, h7]]
          exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have memNeg : ∀ {y : Coord}, y 0 = 0 → y 1 = 0 → y 2 = 0 → y 3 = 0 → y 4 = 0 → y ∈ negativeWeightSubmodule := by
          intro y h0 h1 h2 h3 h4
          rw [show y = y 5 • (Pi.single 5 1 : Coord) + y 6 • (Pi.single 6 1 : Coord) + y 7 • (Pi.single 7 1 : Coord) by
            ext i; fin_cases i <;> simp [h0, h1, h2, h3, h4]]
          exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have memZero : ∀ {y : Coord}, y 1 = 0 → y 2 = 0 → y 3 = 0 → y 5 = 0 → y 6 = 0 → y 7 = 0 → y ∈ zeroWeightSubmodule := by
          intro y h1 h2 h3 h5 h6 h7
          rw [show y = y 0 • (Pi.single 0 1 : Coord) + y 4 • (Pi.single 4 1 : Coord) by
            ext i; fin_cases i <;> simp [h1, h2, h3, h5, h6, h7]]
          exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        by_cases h1 : x 1 ≠ 0
        · have ha' : a = Real.exp t := by
            have := hc 1
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx1); exact ha; exfalso; exact h1 hx1
          exact Or.inl (memPos (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])) (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 5 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 6 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 7 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])))
        by_cases h2 : x 2 ≠ 0
        · have ha' : a = Real.exp t := by
            have := hc 2
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx2); exact ha; exfalso; exact h2 hx2
          exact Or.inl (memPos (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])) (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 5 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 6 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 7 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])))
        by_cases h3 : x 3 ≠ 0
        · have ha' : a = Real.exp t := by
            have := hc 3
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx3); exact ha; exfalso; exact h3 hx3
          exact Or.inl (memPos (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])) (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 5 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 6 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 7 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])))
        by_cases h5 : x 5 ≠ 0
        · have ha' : a = Real.exp (-t) := by
            have := hc 5
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx5); exact ha; exfalso; exact h5 hx5
          exact Or.inr (Or.inl (memNeg (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 1 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 2 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 3 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))))
        by_cases h6 : x 6 ≠ 0
        · have ha' : a = Real.exp (-t) := by
            have := hc 6
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx6); exact ha; exfalso; exact h6 hx6
          exact Or.inr (Or.inl (memNeg (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 1 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 2 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 3 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))))
        by_cases h7 : x 7 ≠ 0
        · have ha' : a = Real.exp (-t) := by
            have := hc 7
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx7); exact ha; exfalso; exact h7 hx7
          exact Or.inr (Or.inl (memNeg (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 1 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 2 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 3 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))))
        · right; right
          have hz := memZero (y := x) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          refine ⟨hz, ?_⟩
          rw [circularPeirceQuadratic_formula] at hQ
          simp_all
      · rintro (h | h | ⟨h, h04⟩)
        · apply hproj.mpr
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨Real.exp t, ?_⟩
          rw [hyperbolicFlow_on_positiveWeight t x h]
        · apply hproj.mpr
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨Real.exp (-t), ?_⟩
          rw [hyperbolicFlow_on_negativeWeight t x h]
        · apply hproj.mpr
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨1, ?_⟩
          rw [hyperbolicFlow_on_zeroWeight t x h]
          simp

theorem circularNullBoundaryFlow_preserves_incidence (t : ℝ) (p q : CircularNullBoundary) :
    NullPolarIncident SplitOctonionEllCircularQuadraticCoordinates.circularPeirceQuadratic (circularNullBoundaryFlow t p) (circularNullBoundaryFlow t q) ↔
      NullPolarIncident SplitOctonionEllCircularQuadraticCoordinates.circularPeirceQuadratic p q := by
  exact InfoGeometry.Twistor.ProjectiveNullIsometryIncidence.nullIsometryEquiv_preserves_incidence
    (circularFlowQuadraticIsometry t) p q

end InfoGeometry.Lie.SplitOctonionCircularProjectiveFixedLocus
