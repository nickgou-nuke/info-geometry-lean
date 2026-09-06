import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

namespace InfoGeometry.Canonical.CliffordPinConjugation

open CliffordAlgebra

variable {R M : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

/-- A Pin element acts on Clifford generators by a genuine vector of `M`.

This is the carrier-level consequence of Mathlib's Pin/Lipschitz theorem;
the existential witness is extracted from the canonical linear-map range,
not supplied as an abstract compatibility field.
-/
theorem exists_vector_of_pin_conjugation
    (u : (CliffordAlgebra Q)ˣ)
    (hu : (u : CliffordAlgebra Q) ∈ pinGroup Q)
    [Invertible (2 : R)] (m : M) :
    ∃ m' : M,
      ConjAct.toConjAct u • CliffordAlgebra.ι Q m = CliffordAlgebra.ι Q m' := by
  rcases LinearMap.mem_range.mp
      (pinGroup.conjAct_smul_ι_mem_range_ι hu m) with ⟨m', hm'⟩
  exact ⟨m', hm'.symm⟩

/-- The twisted Pin action also remains on the Clifford vector carrier. -/
theorem exists_vector_of_pin_involute_conjugation
    (u : (CliffordAlgebra Q)ˣ)
    (hu : (u : CliffordAlgebra Q) ∈ pinGroup Q)
    [Invertible (2 : R)] (m : M) :
    ∃ m' : M,
      CliffordAlgebra.involute (Q := Q) (u : CliffordAlgebra Q) *
          CliffordAlgebra.ι Q m *
            ((u⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        CliffordAlgebra.ι Q m' := by
  rcases LinearMap.mem_range.mp
      (pinGroup.involute_act_ι_mem_range_ι hu m) with ⟨m', hm'⟩
  exact ⟨m', hm'.symm⟩

end InfoGeometry.Canonical.CliffordPinConjugation
