import proofs.HestenesHodgeParityBridge
import proofs.HestenesHodgeEvenTransport
import proofs.HestenesBivectorCarrier

/-!
# Distinct Hodge operators on the even carrier

`paravectorHodge` is the odd-Hodge operator transported through right
multiplication by `gamma 0`.  `intrinsicEvenHodge` is the direct restriction
of the ambient Clifford Hodge operation to the even graded subspace.
-/

noncomputable section
namespace HestenesDistinctHodge

open HestenesCl14 HestenesCliffordCenter HestenesHodgeParityBridge
open HestenesHermitianAdjoint HestenesEvenPauliEquiv

abbrev Algebra := Cl14
abbrev EvenPart := CliffordAlgebra.evenOdd Q14 0
abbrev OddPart := CliffordAlgebra.evenOdd Q14 1

def isHestenesSelfAdjoint (y : EvenPart) : Prop :=
  hestenesAdjoint (HestenesHodgeEvenTransport.asEvenAlgebra y) =
    HestenesHodgeEvenTransport.asEvenAlgebra y

def isHestenesSkewAdjoint (y : EvenPart) : Prop :=
  hestenesAdjoint (HestenesHodgeEvenTransport.asEvenAlgebra y) =
    -HestenesHodgeEvenTransport.asEvenAlgebra y

@[simp] theorem selfAdjoint_iff (y : EvenPart) :
    isHestenesSelfAdjoint y ↔
      hestenesAdjoint (HestenesHodgeEvenTransport.asEvenAlgebra y) =
        HestenesHodgeEvenTransport.asEvenAlgebra y := Iff.rfl

@[simp] theorem skewAdjoint_iff (y : EvenPart) :
    isHestenesSkewAdjoint y ↔
      hestenesAdjoint (HestenesHodgeEvenTransport.asEvenAlgebra y) =
        -HestenesHodgeEvenTransport.asEvenAlgebra y := Iff.rfl

def oddHodge (x : OddPart) : OddPart :=
  ⟨hodge (x : Algebra), hodge_mem_odd x.property⟩

/-- Odd Hodge transported to the even paravector carrier. -/
def paravectorHodge (y : EvenPart) : EvenPart :=
  oddToEven (oddHodge (oddToEven.symm y))

/-- Intrinsic ambient Hodge restricted to the even graded subspace. -/
def intrinsicEvenHodge (y : EvenPart) : EvenPart :=
  ⟨hodge (y : Algebra), hodge_mem_even y.property⟩

@[simp] theorem paravectorHodge_eq_transport (y : EvenPart) :
    paravectorHodge y = oddToEven (oddHodge (oddToEven.symm y)) := rfl

@[simp] theorem paravectorHodge_val (y : EvenPart) :
    (paravectorHodge y : Algebra) =
      -((hestenesAdjoint y : ClPlus14) : Algebra) *
        (spacetimePseudoscalar : Algebra) := by
  have h := oddToEven_hodge (oddToEven.symm y)
  simpa [paravectorHodge, oddHodge] using h

@[simp] theorem intrinsicEvenHodge_val (y : EvenPart) :
    (intrinsicEvenHodge y : Algebra) = hodge (y : Algebra) := rfl

@[simp] theorem intrinsicEvenHodge_mem_even (y : EvenPart) :
    (intrinsicEvenHodge y : Algebra) ∈ CliffordAlgebra.evenOdd Q14 0 :=
  (intrinsicEvenHodge y).property

@[simp] theorem hestenesAdjoint_spacetimePseudoscalar :
    hestenesAdjoint
        (HestenesHodgeEvenTransport.asEvenAlgebra spacetimePseudoscalar) =
      -(HestenesHodgeEvenTransport.asEvenAlgebra spacetimePseudoscalar) := by
  apply Subtype.ext
  change gamma 0 * CliffordAlgebra.reverse
      (spacetimePseudoscalar : Algebra) * gamma 0 =
    -(spacetimePseudoscalar : Algebra)
  rw [HestenesBivectorCarrier.reverse_spacetimePseudoscalar]
  have h := HestenesHodgeParityBridge.omega_anticomm_gamma_zero
  have hz : (spacetimePseudoscalar : Algebra) * gamma 0 +
      gamma 0 * (spacetimePseudoscalar : Algebra) = 0 := by
    rw [h]
    simp
  have hg : gamma 0 * (spacetimePseudoscalar : Algebra) =
      -((spacetimePseudoscalar : Algebra) * gamma 0) :=
    eq_neg_of_add_eq_zero_right hz
  rw [hg]
  noncomm_ring [gamma_zero_sq]

@[simp] theorem intrinsicEvenHodge_sq (y : EvenPart) :
    intrinsicEvenHodge (intrinsicEvenHodge y) = -y := by
  apply Subtype.ext
  change hodge (hodge (y : Algebra)) = -(y : Algebra)
  rw [hodge]
  rw [hodge]
  rw [CliffordAlgebra.reverse.map_mul,
    HestenesBivectorCarrier.reverse_spacetimePseudoscalar,
    CliffordAlgebra.reverse_reverse]
  rw [HestenesBivectorCarrier.spacetimePseudoscalar_comm_even y.property]
  noncomm_ring [HestenesBivectorCarrier.spacetimePseudoscalar_sq]

@[simp] theorem paravectorHodge_sq (y : EvenPart) :
    paravectorHodge (paravectorHodge y) = y := by
  apply Subtype.ext
  rw [paravectorHodge_val]
  have hp :
      HestenesHodgeEvenTransport.asEvenAlgebra (paravectorHodge y) =
        -(hestenesAdjoint (HestenesHodgeEvenTransport.asEvenAlgebra y) *
          HestenesHodgeEvenTransport.asEvenAlgebra spacetimePseudoscalar) := by
    apply Subtype.ext
    simpa [HestenesHodgeEvenTransport.asEvenAlgebra] using paravectorHodge_val y
  have hadj_neg (z : ClPlus14) : hestenesAdjoint (-z) = -hestenesAdjoint z := by
    simpa only [neg_one_smul] using hestenesAdjoint_smul (-1 : ℝ) z
  change -((hestenesAdjoint
      (HestenesHodgeEvenTransport.asEvenAlgebra (paravectorHodge y)) :
        ClPlus14) : Algebra) * (spacetimePseudoscalar : Algebra) = (y : Algebra)
  rw [hp, hadj_neg, hestenesAdjoint_mul, hestenesAdjoint_involutive,
    hestenesAdjoint_spacetimePseudoscalar]
  rw [show ((-(-HestenesHodgeEvenTransport.asEvenAlgebra spacetimePseudoscalar *
      HestenesHodgeEvenTransport.asEvenAlgebra y) : ClPlus14) : Algebra) =
      (spacetimePseudoscalar : Algebra) * (y : Algebra) by
        simp [HestenesHodgeEvenTransport.asEvenAlgebra]]
  simp only [neg_mul]
  rw [HestenesBivectorCarrier.spacetimePseudoscalar_comm_even y.property,
    mul_assoc, HestenesBivectorCarrier.spacetimePseudoscalar_sq]
  simp
end HestenesDistinctHodge
end noncomputable section
