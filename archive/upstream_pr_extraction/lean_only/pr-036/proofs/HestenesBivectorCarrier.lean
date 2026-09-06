import proofs.HestenesHodgeBivector
import proofs.HestenesOmegaHyperbolic

/-!
# The exact bivector carrier in `Cl(1,3)`

Inside the even Clifford sector, reversion has eigenvalue `-1` precisely on
grade two.  We therefore use the intrinsic intersection

`even ∩ ker (reverse + id)`

as the bivector carrier, rather than confusing it with the whole even
algebra.  The Lorentzian Hodge operator preserves this carrier and squares to
`-1` on it.
-/

noncomputable section
namespace HestenesBivectorCarrier

open HestenesCl14 HestenesCliffordCenter HestenesEvenPauliEquiv
open HestenesPauliSheetBridge HestenesHodgeParityBridge
open HestenesOmegaHyperbolic

abbrev Algebra := Cl14

/-- Exact grade-two carrier: even Clifford elements negated by reversion. -/
def Bivector13 : Submodule ℝ Algebra where
  carrier := {x | x ∈ CliffordAlgebra.evenOdd Q14 0 ∧
    CliffordAlgebra.reverse x = -x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor
    · exact (CliffordAlgebra.evenOdd Q14 0).add_mem hx.1 hy.1
    · rw [map_add, hx.2, hy.2]
      module
  smul_mem' := by
    intro r x hx
    constructor
    · exact (CliffordAlgebra.evenOdd Q14 0).smul_mem r hx.1
    · simp [hx.2]

abbrev Bivector := Bivector13

theorem mem_bivector_iff (x : Algebra) :
    x ∈ Bivector13 ↔
      x ∈ CliffordAlgebra.evenOdd Q14 0 ∧
        CliffordAlgebra.reverse x = -x := Iff.rfl

@[simp] theorem reverse_bivector (B : Bivector) :
    CliffordAlgebra.reverse (B : Algebra) = -B := B.property.2

theorem bivector_even (B : Bivector) :
    (B : Algebra) ∈ CliffordAlgebra.evenOdd Q14 0 := B.property.1

/-- The native pseudoscalar agrees with the Pauli-volume element. -/
theorem spacetimePseudoscalar_eq_volumeEven :
    spacetimePseudoscalar = volumeEven := by
  apply Subtype.ext
  rw [spacetimePseudoscalar_val]
  simp only [volumeEven]
  change gamma 0 * gamma 1 * gamma 2 * gamma 3 =
    (gamma 1 * gamma 0) * (gamma 2 * gamma 0) * (gamma 3 * gamma 0)
  have h01 := eq_neg_of_add_eq_zero_right
    (gamma_anticomm (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide))
  have k01 := eq_neg_of_add_eq_zero_left
    (gamma_anticomm (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide))
  have k02 := eq_neg_of_add_eq_zero_left
    (gamma_anticomm (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide))
  have k03 := eq_neg_of_add_eq_zero_left
    (gamma_anticomm (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide))
  symm
  calc
    (gamma 1 * gamma 0) * (gamma 2 * gamma 0) * (gamma 3 * gamma 0) =
        -(gamma 1 * gamma 2) * (gamma 3 * gamma 0) := by
      rw [show (gamma 1 * gamma 0) * (gamma 2 * gamma 0) =
        gamma 1 * (gamma 0 * gamma 2) * gamma 0 by simp [mul_assoc], k02]
      noncomm_ring [gamma_zero_sq]
    _ = -(gamma 1 * gamma 2 * gamma 3) * gamma 0 := by simp [mul_assoc]
    _ = gamma 0 * gamma 1 * gamma 2 * gamma 3 := by
      symm
      calc
        gamma 0 * gamma 1 * gamma 2 * gamma 3 =
            (gamma 0 * gamma 1) * (gamma 2 * gamma 3) := by simp [mul_assoc]
        _ = -(gamma 1 * gamma 0) * (gamma 2 * gamma 3) := by rw [k01]
        _ = -gamma 1 * (gamma 0 * gamma 2) * gamma 3 := by noncomm_ring
        _ = gamma 1 * gamma 2 * gamma 0 * gamma 3 := by rw [k02]; noncomm_ring
        _ = gamma 1 * gamma 2 * (gamma 0 * gamma 3) := by simp [mul_assoc]
        _ = -(gamma 1 * gamma 2 * gamma 3) * gamma 0 := by rw [k03]; noncomm_ring

@[simp] theorem spacetimePseudoscalar_sq :
    (spacetimePseudoscalar : Algebra) * spacetimePseudoscalar = -1 := by
  have h := HestenesOmegaHyperbolic.omega_sq
  rw [omega, ← spacetimePseudoscalar_eq_volumeEven] at h
  exact congrArg Subtype.val h

theorem spacetimePseudoscalar_comm_even
    {x : Algebra} (hx : x ∈ CliffordAlgebra.evenOdd Q14 0) :
    (spacetimePseudoscalar : Algebra) * x =
      x * spacetimePseudoscalar := by
  let xe : ClPlus14 := ⟨x, hx⟩
  have h : spacetimePseudoscalar * xe = xe * spacetimePseudoscalar := by
    apply clPlusToPauli_injective
    simp [spacetimePseudoscalar_eq_volumeEven,
      clPlusToPauli_volumeEven]
  exact congrArg Subtype.val h

theorem omega_comm_bivector (B : Bivector) :
    (spacetimePseudoscalar : Algebra) * B =
      B * spacetimePseudoscalar :=
  spacetimePseudoscalar_comm_even B.property.1

@[simp] theorem reverse_spacetimePseudoscalar :
    CliffordAlgebra.reverse (spacetimePseudoscalar : Algebra) =
      spacetimePseudoscalar := by
  rw [spacetimePseudoscalar_val]
  simp only [CliffordAlgebra.reverse.map_mul]
  have hr (i : Fin 4) : CliffordAlgebra.reverse (gamma i) = gamma i := by simp [gamma]
  rw [hr, hr, hr, hr]
  simp only [mul_assoc]
  have h01 := eq_neg_of_add_eq_zero_right
    (gamma_anticomm (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide))
  have h02 := eq_neg_of_add_eq_zero_right
    (gamma_anticomm (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide))
  have h03 := eq_neg_of_add_eq_zero_right
    (gamma_anticomm (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide))
  have h12 := eq_neg_of_add_eq_zero_right
    (gamma_anticomm (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide))
  have h13 := eq_neg_of_add_eq_zero_right
    (gamma_anticomm (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide))
  have h23 := eq_neg_of_add_eq_zero_right
    (gamma_anticomm (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide))
  have hs : gamma 3 * (gamma 2 * gamma 1) =
      -(gamma 1 * (gamma 2 * gamma 3)) := by
    calc
      gamma 3 * (gamma 2 * gamma 1) = gamma 3 * (-(gamma 1 * gamma 2)) := by rw [h12]
      _ = -(gamma 3 * gamma 1) * gamma 2 := by noncomm_ring
      _ = -(-(gamma 1 * gamma 3)) * gamma 2 := by rw [h13]
      _ = gamma 1 * (gamma 3 * gamma 2) := by noncomm_ring
      _ = -(gamma 1 * (gamma 2 * gamma 3)) := by rw [h23]; noncomm_ring
  have hs0 : (gamma 1 * (gamma 2 * gamma 3)) * gamma 0 =
      -(gamma 0 * (gamma 1 * (gamma 2 * gamma 3))) := by
    calc
      (gamma 1 * (gamma 2 * gamma 3)) * gamma 0 =
          gamma 1 * gamma 2 * (gamma 3 * gamma 0) := by simp [mul_assoc]
      _ = -(gamma 1 * gamma 2) * (gamma 0 * gamma 3) := by rw [h03]; noncomm_ring
      _ = -gamma 1 * (gamma 2 * gamma 0) * gamma 3 := by noncomm_ring
      _ = gamma 1 * (gamma 0 * gamma 2) * gamma 3 := by rw [h02]; noncomm_ring
      _ = (gamma 1 * gamma 0) * (gamma 2 * gamma 3) := by simp [mul_assoc]
      _ = -(gamma 0 * gamma 1) * (gamma 2 * gamma 3) := by rw [h01]
      _ = -(gamma 0 * (gamma 1 * (gamma 2 * gamma 3))) := by noncomm_ring
  calc
    gamma 3 * (gamma 2 * (gamma 1 * gamma 0)) =
        (gamma 3 * (gamma 2 * gamma 1)) * gamma 0 := by simp [mul_assoc]
    _ = -(gamma 1 * (gamma 2 * gamma 3)) * gamma 0 := by rw [hs]
    _ = gamma 0 * (gamma 1 * (gamma 2 * gamma 3)) := by
      rw [show -(gamma 1 * (gamma 2 * gamma 3)) * gamma 0 =
        -((gamma 1 * (gamma 2 * gamma 3)) * gamma 0) by noncomm_ring, hs0]
      simp

/-- Hodge duality restricted to the exact bivector carrier. -/
def hodgeBivector : Bivector →ₗ[ℝ] Bivector where
  toFun B := ⟨hodge B, by
    constructor
    · exact hodge_mem_even B.property.1
    · rw [hodge, CliffordAlgebra.reverse.map_mul,
        reverse_spacetimePseudoscalar, CliffordAlgebra.reverse_reverse,
        reverse_bivector]
      rw [spacetimePseudoscalar_comm_even B.property.1]
      noncomm_ring⟩
  map_add' x y := by
    apply Subtype.ext
    exact hodge_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact hodge_smul r x

@[simp] theorem hodgeBivector_val (B : Bivector) :
    (hodgeBivector B : Algebra) = hodge B := rfl

@[simp] theorem hodge_sq_bivector (B : Bivector) :
    hodgeBivector (hodgeBivector B) = -B := by
  apply Subtype.ext
  change hodge (hodge (B : Algebra)) = -(B : Algebra)
  rw [hodge]
  rw [show CliffordAlgebra.reverse (hodge (B : Algebra)) =
      -hodge (B : Algebra) by exact (hodgeBivector B).property.2]
  rw [hodge, reverse_bivector]
  noncomm_ring [spacetimePseudoscalar_sq]

theorem hodge_bivector_packet :
    (∀ B : Bivector,
      CliffordAlgebra.reverse (B : Algebra) = -B) ∧
    (∀ B : Bivector,
      (spacetimePseudoscalar : Algebra) * B =
        B * spacetimePseudoscalar) ∧
    (∀ B : Bivector, hodgeBivector (hodgeBivector B) = -B) :=
  ⟨reverse_bivector, omega_comm_bivector, hodge_sq_bivector⟩

end HestenesBivectorCarrier
end noncomputable section
