import InfoGeometry.Clifford.SplitOctonionChiralMatrixProduct

/-!
# Principal left ideals in the chained chiral-action algebra

The chained-action algebra is associative because it is a subalgebra of an
endomorphism algebra.  This file records the valid ideal construction that
does not assume a primitive idempotent or claim minimality.
-/

namespace InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

abbrev ChiralActionAlgebra : Type := ↥chiralCayleyChainedLeftActionAlgebra

def principalLeftIdeal (f : ChiralActionAlgebra) : Set ChiralActionAlgebra :=
  Set.range (fun a : ChiralActionAlgebra => a * f)

theorem mem_principalLeftIdeal_iff (f x : ChiralActionAlgebra) :
    x ∈ principalLeftIdeal f ↔ ∃ a : ChiralActionAlgebra, a * f = x := by
  rfl

theorem principalLeftIdeal_left_closed
    (f a x : ChiralActionAlgebra)
    (hx : x ∈ principalLeftIdeal f) :
    a * x ∈ principalLeftIdeal f := by
  rcases hx with ⟨b, rfl⟩
  refine ⟨a * b, ?_⟩
  simp [mul_assoc]

theorem principalLeftIdeal_add_mem
    (f x y : ChiralActionAlgebra)
    (hx : x ∈ principalLeftIdeal f)
    (hy : y ∈ principalLeftIdeal f) :
    x + y ∈ principalLeftIdeal f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a + b, by simp [add_mul]⟩

theorem principalLeftIdeal_smul_mem
    (f : ChiralActionAlgebra) (r : ℝ) (x : ChiralActionAlgebra)
    (hx : x ∈ principalLeftIdeal f) :
    r • x ∈ principalLeftIdeal f := by
  rcases hx with ⟨a, rfl⟩
  exact ⟨r • a, by simp [smul_mul_assoc]⟩

theorem generator_mem_principalLeftIdeal (f : ChiralActionAlgebra) :
    f ∈ principalLeftIdeal f := by
  exact ⟨1, by simp⟩

theorem idempotent_mem_principalLeftIdeal (f : ChiralActionAlgebra)
    (hf : f * f = f) :
    f ∈ principalLeftIdeal f := by
  exact ⟨f, hf⟩

theorem principalLeftIdeal_one_eq_univ :
    principalLeftIdeal (1 : ChiralActionAlgebra) = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨x, by simp⟩

end
end InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout
