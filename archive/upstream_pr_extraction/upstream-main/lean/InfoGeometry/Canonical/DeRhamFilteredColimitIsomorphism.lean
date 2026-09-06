import InfoGeometry.Canonical.FilteredColimitColorDiracKahler

namespace InfoGeometry.Canonical

section CohomologyTransport

variable {R : Type*} [CommRing R]
variable (A : ℕ → Type*)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (AInf : Type*) [AddCommGroup AInf] [Module R AInf]

variable (d : ∀ n, A n →ₗ[R] A n)
variable (dInf : AInf →ₗ[R] AInf)
variable (psi : ∀ n, A n →ₗ[R] AInf)
variable (d_sq_zero : ∀ n, (d n).comp (d n) = 0)
variable (d_comm : ∀ n, dInf.comp (psi n) = (psi n).comp (d n))
variable (jointly_surjective : ∀ x : AInf, ∃ n : ℕ, ∃ y : A n, psi n y = x)

/-- 1. A closed form at stage n maps to a closed form in the colimit (AInf). -/
theorem colimit_closed_of_stage_closed
    (d_comm : ∀ n, dInf.comp (psi n) = (psi n).comp (d n))
    (n : ℕ) (x : A n) (hx : d n x = 0) :
    dInf (psi n x) = 0 := by
  have h := colimitDifferential_commutes_with_stage A AInf d dInf psi d_comm n x
  rw [h, hx, map_zero]

/-- 2. An exact form at stage n maps to an exact form in the colimit (AInf). -/
theorem colimit_exact_of_stage_exact
    (d_comm : ∀ n, dInf.comp (psi n) = (psi n).comp (d n))
    (n : ℕ) (x : A n) (y : A n) (hx : d n y = x) :
    ∃ yInf : AInf, dInf yInf = psi n x := by
  use psi n y
  have h := colimitDifferential_commutes_with_stage A AInf d dInf psi d_comm n y
  rw [h, hx]

/-- 3. Every closed form in the colimit comes from a weakly-closed sequence
    (assuming exactness of the filtered colimit). Here we prove that if an element 
    is closed in AInf, its preimage satisfies a stage-level exactness condition 
    relative to the colimit map. -/
theorem colimit_cohomology_surjective_bridge
    (jointly_surjective : ∀ x : AInf, ∃ n : ℕ, ∃ y : A n, psi n y = x)
    (d_comm : ∀ n, dInf.comp (psi n) = (psi n).comp (d n))
    (xInf : AInf) (hxInf : dInf xInf = 0) :
    ∃ n : ℕ, ∃ x : A n, psi n x = xInf ∧ psi n (d n x) = 0 := by
  rcases jointly_surjective xInf with ⟨n, x, rfl⟩
  use n, x
  refine ⟨rfl, ?_⟩
  have h := colimitDifferential_commutes_with_stage A AInf d dInf psi d_comm n x
  rw [← h, hxInf]

end CohomologyTransport

end InfoGeometry.Canonical
