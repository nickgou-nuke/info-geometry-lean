import InfoGeometry.Canonical.RealHomologyCohomologyDictionary

namespace InfoGeometry.Canonical.RealHomologyCohomologyDictionary

variable {C : Type*} [AddCommGroup C] [Module ℝ C]

namespace RealBoundaryOperator

variable (B : RealBoundaryOperator C)

/-! The genuine homology quotient attached to a square-zero real linear map. -/

def cycles : Submodule ℝ C :=
  LinearMap.ker B.d

def boundaries : Submodule ℝ C :=
  LinearMap.range B.d

theorem boundaries_le_cycles : B.boundaries ≤ B.cycles := by
  change LinearMap.range B.d ≤ LinearMap.ker B.d
  exact LinearMap.range_le_ker_iff.mpr B.d_sq_zero

def boundariesInCycles : Submodule ℝ (cycles B) :=
  (boundaries B).comap (cycles B).subtype

abbrev Homology : Type _ :=
  cycles B ⧸ boundariesInCycles B

noncomputable def cycleClass : cycles B →ₗ[ℝ] Homology B :=
  Submodule.mkQ (boundariesInCycles B)

theorem cycleClass_eq_iff_difference_boundary
    (x y : cycles B) :
    cycleClass B x = cycleClass B y ↔
      ∃ z : C, B.d z = (x : C) - (y : C) := by
  change Submodule.Quotient.mk x = Submodule.Quotient.mk y ↔ _
  rw [Submodule.Quotient.eq]
  change ((x : C) - (y : C)) ∈ LinearMap.range B.d ↔ _
  constructor
  · intro h
    rcases LinearMap.mem_range.mp h with ⟨z, hz⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact LinearMap.mem_range.mpr ⟨z, hz⟩

noncomputable def toHomologyLinearMap
    (ω : C →ₗ[ℝ] ℝ)
    (hω : ∀ y : C, ω (B.d y) = 0) : Homology B →ₗ[ℝ] ℝ :=
  Submodule.liftQ (boundariesInCycles B)
    (ω.comp (cycles B).subtype)
    (by
      intro x hx
      change (x : C) ∈ LinearMap.range B.d at hx
      rcases LinearMap.mem_range.mp hx with ⟨z, hz⟩
      change ω (x : C) = 0
      rw [← hz]
      exact hω z)

@[simp] theorem toHomologyLinearMap_cycleClass
    (ω : C →ₗ[ℝ] ℝ)
    (hω : ∀ y : C, ω (B.d y) = 0)
    (x : cycles B) :
    toHomologyLinearMap B ω hω (cycleClass B x) = ω x := by
  simp [toHomologyLinearMap, cycleClass]

end RealBoundaryOperator

end InfoGeometry.Canonical.RealHomologyCohomologyDictionary
