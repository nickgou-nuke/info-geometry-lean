import proofs.HestenesEvenPauliEquiv
import proofs.HestenesCliffordCenter
import proofs.HestenesHermitianAdjoint

/-!
# Hodge parity and the odd--even Hestenes bridge

The Clifford realization used here is `⋆x = reverse(x) Ω₄`.  In four
dimensions multiplication by the even volume element preserves the `ZMod 2`
grade.  Right multiplication by the odd unit `γ₀`, not Hodge duality, is the
native parity-changing equivalence.
-/

noncomputable section
namespace HestenesHodgeParityBridge

open HestenesCl14
open HestenesCliffordCenter
open HestenesEvenPauliEquiv
open HestenesHermitianAdjoint

abbrev Algebra := Cl14
abbrev EvenPart := CliffordAlgebra.evenOdd Q14 0
abbrev OddPart := CliffordAlgebra.evenOdd Q14 1

def hodge (x : Algebra) : Algebra :=
  CliffordAlgebra.reverse x * (spacetimePseudoscalar : Algebra)

@[simp] theorem hodge_add (x y : Algebra) :
    hodge (x + y) = hodge x + hodge y := by
  simp [hodge, add_mul]

@[simp] theorem hodge_smul (r : ℝ) (x : Algebra) :
    hodge (r • x) = r • hodge x := by
  simp [hodge]

/-- Hodge duality preserves either Clifford parity in dimension four. -/
theorem hodge_mem_evenOdd (p : ZMod 2) {x : Algebra}
    (hx : x ∈ CliffordAlgebra.evenOdd Q14 p) :
    hodge x ∈ CliffordAlgebra.evenOdd Q14 p := by
  have hr : CliffordAlgebra.reverse x ∈ CliffordAlgebra.evenOdd Q14 p :=
    (CliffordAlgebra.reverse_mem_evenOdd_iff (Q := Q14)).2 hx
  have hm := SetLike.mul_mem_graded hr spacetimePseudoscalar.property
  simpa [hodge] using hm

theorem hodge_mem_even {x : Algebra} (hx : x ∈ CliffordAlgebra.evenOdd Q14 0) :
    hodge x ∈ CliffordAlgebra.evenOdd Q14 0 :=
  hodge_mem_evenOdd 0 hx

theorem hodge_mem_odd {x : Algebra} (hx : x ∈ CliffordAlgebra.evenOdd Q14 1) :
    hodge x ∈ CliffordAlgebra.evenOdd Q14 1 :=
  hodge_mem_evenOdd 1 hx

/-- The already established parity converter, exposed in the odd-to-even direction. -/
def oddToEven : OddPart ≃ₗ[ℝ] EvenPart := evenOddLinearEquiv.symm

@[simp] theorem oddToEven_val (x : OddPart) :
    ((oddToEven x : EvenPart) : Algebra) = (x : Algebra) * gamma 0 := rfl

theorem omega_anticomm_gamma_zero :
    (spacetimePseudoscalar : Algebra) * gamma 0 =
      -(gamma 0 * (spacetimePseudoscalar : Algebra)) := by
  have h01 : gamma 1 * gamma 0 = -(gamma 0 * gamma 1) := by
    have h := gamma_anticomm (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
    exact eq_neg_of_add_eq_zero_right h
  have h02 : gamma 2 * gamma 0 = -(gamma 0 * gamma 2) := by
    have h := gamma_anticomm (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
    exact eq_neg_of_add_eq_zero_right h
  have h03 : gamma 3 * gamma 0 = -(gamma 0 * gamma 3) := by
    have h := gamma_anticomm (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
    exact eq_neg_of_add_eq_zero_right h
  rw [spacetimePseudoscalar_val]
  calc
    (gamma 0 * gamma 1 * gamma 2 * gamma 3) * gamma 0 =
        gamma 0 * gamma 1 * gamma 2 * (gamma 3 * gamma 0) := by
          simp only [mul_assoc]
    _ = -(gamma 0 * gamma 1 * (gamma 2 * gamma 0) * gamma 3) := by
          rw [h03]
          noncomm_ring
    _ = gamma 0 * (gamma 1 * gamma 0) * gamma 2 * gamma 3 := by
          rw [h02]
          noncomm_ring
    _ = -(gamma 0 * gamma 0 * gamma 1 * gamma 2 * gamma 3) := by
          rw [h01]
          noncomm_ring
    _ = -(gamma 0 * (gamma 0 * gamma 1 * gamma 2 * gamma 3)) := by
          simp only [mul_assoc]

/-- Transport of odd-sector Hodge duality into the even paravector algebra. -/
theorem oddToEven_hodge (x : OddPart) :
    hodge (x : Algebra) * gamma 0 =
      -((hestenesAdjoint (oddToEven x) : ClPlus14) : Algebra) *
        (spacetimePseudoscalar : Algebra) := by
  change CliffordAlgebra.reverse (x : Algebra) *
      (spacetimePseudoscalar : Algebra) * gamma 0 =
    -(gamma 0 * CliffordAlgebra.reverse ((x : Algebra) * gamma 0) * gamma 0) *
      (spacetimePseudoscalar : Algebra)
  rw [CliffordAlgebra.reverse.map_mul]
  have hr0 : CliffordAlgebra.reverse (gamma 0) = gamma 0 := by simp [gamma]
  rw [hr0]
  simp only [mul_assoc]
  rw [← mul_assoc (gamma 0) (gamma 0), gamma_zero_sq, one_mul]
  rw [omega_anticomm_gamma_zero]
  noncomm_ring

theorem hodge_parity_bridge_packet :
    (∀ x : EvenPart, hodge (x : Algebra) ∈ CliffordAlgebra.evenOdd Q14 0) ∧
    (∀ x : OddPart, hodge (x : Algebra) ∈ CliffordAlgebra.evenOdd Q14 1) ∧
    (∀ x : OddPart,
      hodge (x : Algebra) * gamma 0 =
        -((hestenesAdjoint (oddToEven x) : ClPlus14) : Algebra) *
          (spacetimePseudoscalar : Algebra)) :=
  ⟨fun x => hodge_mem_even x.2, fun x => hodge_mem_odd x.2,
    oddToEven_hodge⟩

end HestenesHodgeParityBridge
end noncomputable section
