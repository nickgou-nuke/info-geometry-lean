import proofs.HestenesHodgeParityBridge

/-!
# Hodge duality transported to the even Hestenes carrier

Right multiplication by `γ₀` identifies the odd and even parity sectors.  This
owner packages the resulting even-side Hodge operator and proves the commuting
transport square on the whole odd sector.
-/

noncomputable section
namespace HestenesHodgeEvenTransport

open HestenesCl14
open HestenesCliffordCenter
open HestenesHermitianAdjoint
open HestenesHodgeParityBridge

abbrev Algebra := Cl14
abbrev EvenPart := CliffordAlgebra.evenOdd Q14 0
abbrev OddPart := CliffordAlgebra.evenOdd Q14 1

def asEvenAlgebra (y : EvenPart) : ClPlus14 := ⟨(y : Algebra), y.2⟩

@[simp] theorem asEvenAlgebra_add (x y : EvenPart) :
    asEvenAlgebra (x + y) = asEvenAlgebra x + asEvenAlgebra y := rfl

@[simp] theorem asEvenAlgebra_smul (r : ℝ) (x : EvenPart) :
    asEvenAlgebra (r • x) = r • asEvenAlgebra x := rfl

/-- Hodge duality restricted to the odd Clifford parity sector. -/
def oddHodge (x : OddPart) : OddPart :=
  ⟨hodge (x : Algebra), hodge_mem_odd x.2⟩

/-- The even Hestenes representative of odd-sector Hodge duality. -/
def evenHodge (y : EvenPart) : EvenPart :=
  -hestenesAdjoint (asEvenAlgebra y) * spacetimePseudoscalar

@[simp] theorem oddHodge_val (x : OddPart) :
    ((oddHodge x : OddPart) : Algebra) = hodge (x : Algebra) := rfl

@[simp] theorem evenHodge_val (y : EvenPart) :
    ((evenHodge y : EvenPart) : Algebra) =
      -((hestenesAdjoint y : ClPlus14) : Algebra) *
        (spacetimePseudoscalar : Algebra) := rfl

@[simp] theorem oddHodge_add (x y : OddPart) :
    oddHodge (x + y) = oddHodge x + oddHodge y := by
  apply Subtype.ext
  exact hodge_add (x : Algebra) (y : Algebra)

@[simp] theorem oddHodge_smul (r : ℝ) (x : OddPart) :
    oddHodge (r • x) = r • oddHodge x := by
  apply Subtype.ext
  exact hodge_smul r (x : Algebra)

@[simp] theorem evenHodge_add (x y : EvenPart) :
    evenHodge (x + y) = evenHodge x + evenHodge y := by
  unfold evenHodge
  rw [asEvenAlgebra_add, hestenesAdjoint_add, neg_add, add_mul]

@[simp] theorem evenHodge_smul (r : ℝ) (x : EvenPart) :
    evenHodge (r • x) = r • evenHodge x := by
  unfold evenHodge
  rw [asEvenAlgebra_smul, hestenesAdjoint_smul]
  rw [← smul_neg, smul_mul_assoc]

/-- The even-side formula is exactly Hodge conjugated by the odd--even equivalence. -/
theorem evenHodge_eq_transport (x : OddPart) :
    evenHodge (oddToEven x) = oddToEven (oddHodge x) := by
  apply Subtype.ext
  symm
  exact oddToEven_hodge x

/-- Type-level certificate that the transported operation remains in the even sector. -/
theorem evenHodge_preserves_even (y : EvenPart) :
    ((evenHodge y : EvenPart) : Algebra) ∈
      CliffordAlgebra.evenOdd Q14 0 :=
  (evenHodge y).2

/-- On Hestenes-self-adjoint paravectors, transported Hodge is right
multiplication by the negatively oriented pseudoscalar. -/
theorem evenHodge_on_selfAdjoint (y : EvenPart)
    (hy : hestenesAdjoint (asEvenAlgebra y) = asEvenAlgebra y) :
    evenHodge y =
      -(asEvenAlgebra y) * spacetimePseudoscalar := by
  unfold evenHodge
  rw [hy]

/-- Real-linear packaging of the transported even-side Hodge operation. -/
def evenHodgeLinear : EvenPart →ₗ[ℝ] EvenPart where
  toFun := evenHodge
  map_add' := evenHodge_add
  map_smul' := evenHodge_smul

theorem hodge_even_transport_packet :
    (∀ x : OddPart, evenHodge (oddToEven x) = oddToEven (oddHodge x)) ∧
    (∀ y : EvenPart,
      hestenesAdjoint (asEvenAlgebra y) = asEvenAlgebra y →
      evenHodge y = -(asEvenAlgebra y) * spacetimePseudoscalar) :=
  ⟨evenHodge_eq_transport, evenHodge_on_selfAdjoint⟩

end HestenesHodgeEvenTransport
end noncomputable section
