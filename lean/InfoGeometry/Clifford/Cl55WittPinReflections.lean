import InfoGeometry.Clifford.Cl55WittOrthogonalReflections

namespace InfoGeometry.Clifford.Clifford55

open BigOperators

noncomputable def fNegUnit (i : Fin 5) : Cl55ˣ :=
  (CliffordAlgebra.isUnit_ι_of_isUnit Q55
    (show IsUnit (Q55 (f_neg i)) by
      rw [Q55_f_neg i]
      exact ⟨-1, by simp⟩)).unit

theorem fNegUnit_coe (i : Fin 5) :
    (fNegUnit i : Cl55) = ι55 (f_neg i) := by
  exact (CliffordAlgebra.isUnit_ι_of_isUnit Q55
    (show IsUnit (Q55 (f_neg i)) by
      rw [Q55_f_neg i]
      exact ⟨-1, by simp⟩)).unit_spec

theorem f_neg_mem_pinGroup (i : Fin 5) :
    ι55 (f_neg i) ∈ Pin55 := by
  rw [← fNegUnit_coe i]
  apply pinGroup.mem_iff.mpr
  constructor
  · apply Submonoid.mem_map.mpr
    refine ⟨fNegUnit i, ?_, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨f_neg i, ?_⟩
    exact (fNegUnit_coe i).symm
  · rw [Unitary.mem_iff]
    constructor
    · rw [fNegUnit_coe, CliffordAlgebra.star_ι, neg_mul,
        f_neg_mul_self]
      simp
    · simp only [fNegUnit_coe, CliffordAlgebra.star_ι]
      rw [mul_neg, f_neg_mul_self]
      simp

theorem f_neg_pin_twisted_action_mem_range (i : Fin 5) (x : V55) :
    CliffordAlgebra.involute (fNegUnit i : Cl55) * ι55 x *
        (↑((fNegUnit i)⁻¹) : Cl55) ∈ (ι55).range := by
  apply pinGroup.involute_act_ι_mem_range_ι
  rw [fNegUnit_coe]
  exact f_neg_mem_pinGroup i

theorem f_neg_pin_twisted_action_exists (i : Fin 5) (x : V55) :
    ∃ y : V55,
      CliffordAlgebra.involute (fNegUnit i : Cl55) * ι55 x *
          (↑((fNegUnit i)⁻¹) : Cl55) = ι55 y := by
  rcases LinearMap.mem_range.mp (f_neg_pin_twisted_action_mem_range i x) with
    ⟨y, hy⟩
  exact ⟨y, hy.symm⟩

noncomputable def fNegPin (i : Fin 5) : Pin55 :=
  ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩

@[simp] theorem fNegPin_coe (i : Fin 5) :
    (fNegPin i : Cl55) = ι55 (f_neg i) := rfl

noncomputable def globalSheetPin : Pin55 :=
  fNegPin 0 * fNegPin 1 * fNegPin 2 * fNegPin 3 * fNegPin 4

theorem globalSheetPin_mem_pinGroup :
    (globalSheetPin : Cl55) ∈ Pin55 := (globalSheetPin).property

theorem globalSheetPin_coe :
    (globalSheetPin : Cl55) =
      ι55 (f_neg 0) * ι55 (f_neg 1) * ι55 (f_neg 2) *
        ι55 (f_neg 3) * ι55 (f_neg 4) := by
  simp [globalSheetPin]

noncomputable def globalSheetUnit : Cl55ˣ :=
  fNegUnit 0 * fNegUnit 1 * fNegUnit 2 * fNegUnit 3 * fNegUnit 4

theorem globalSheetUnit_coe :
    (globalSheetUnit : Cl55) = (globalSheetPin : Cl55) := by
  simp [globalSheetUnit, globalSheetPin, fNegUnit_coe, fNegPin]

theorem globalSheetUnit_mem_pinGroup :
    (globalSheetUnit : Cl55) ∈ Pin55 := by
  rw [globalSheetUnit_coe]
  exact globalSheetPin.property

theorem globalSheetPin_twisted_action_mem_range (x : V55) :
    CliffordAlgebra.involute (globalSheetUnit : Cl55) * ι55 x *
        (↑(globalSheetUnit⁻¹) : Cl55) ∈ (ι55).range := by
  apply pinGroup.involute_act_ι_mem_range_ι
  exact globalSheetUnit_mem_pinGroup

theorem globalSheetPin_twisted_action_exists (x : V55) :
    ∃ y : V55,
      CliffordAlgebra.involute (globalSheetUnit : Cl55) * ι55 x *
          (↑(globalSheetUnit⁻¹) : Cl55) = ι55 y := by
  rcases LinearMap.mem_range.mp (globalSheetPin_twisted_action_mem_range x) with
    ⟨y, hy⟩
  exact ⟨y, hy.symm⟩

theorem fNegUnit_inv_coe (i : Fin 5) :
    (↑((fNegUnit i)⁻¹) : Cl55) = -ι55 (f_neg i) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [fNegUnit_coe]
  calc
    ι55 (f_neg i) * -ι55 (f_neg i) =
        -(ι55 (f_neg i) * ι55 (f_neg i)) := by rw [mul_neg]
    _ = 1 := by rw [f_neg_mul_self]; simp

private theorem negative_pin_reflection_orthogonal {A : Type*} [Ring A]
    (e f : A) (hff : f * f = -1)
    (hanti : f * e + e * f = 0) :
    -f * e * (-f) = e := by
  have hfe : f * e = -(e * f) := by
    rw [← add_eq_zero_iff_eq_neg]
    exact hanti
  calc
    -f * e * (-f) = f * e * f := by noncomm_ring
    _ = -(e * f) * f := by rw [hfe]
    _ = e := by
      calc
        -(e * f) * f = -((e * f) * f) := by rw [neg_mul]
        _ = -(e * (f * f)) := by rw [mul_assoc]
        _ = e := by rw [hff]; simp

theorem f_neg_pin_twisted_action_e_pos (i : Fin 5) :
    CliffordAlgebra.involute (fNegUnit i : Cl55) * ι55 (e_pos i) *
        (↑((fNegUnit i)⁻¹) : Cl55) = ι55 (e_pos i) := by
  rw [fNegUnit_coe, CliffordAlgebra.involute_ι, fNegUnit_inv_coe]
  apply negative_pin_reflection_orthogonal
  · exact f_neg_mul_self i
  · have h := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (Q := Q55) (e_pos_ortho_f_neg i i)
    simpa [add_comm] using h

theorem f_neg_pin_twisted_action_f_neg (i : Fin 5) :
    CliffordAlgebra.involute (fNegUnit i : Cl55) * ι55 (f_neg i) *
        (↑((fNegUnit i)⁻¹) : Cl55) = -ι55 (f_neg i) := by
  rw [fNegUnit_coe, CliffordAlgebra.involute_ι, fNegUnit_inv_coe]
  calc
    -ι55 (f_neg i) * ι55 (f_neg i) * -ι55 (f_neg i) =
        (ι55 (f_neg i) * ι55 (f_neg i)) * ι55 (f_neg i) := by
          noncomm_ring
    _ = (-1 : Cl55) * ι55 (f_neg i) := by rw [f_neg_mul_self]
    _ = -ι55 (f_neg i) := by simp

end InfoGeometry.Clifford.Clifford55
