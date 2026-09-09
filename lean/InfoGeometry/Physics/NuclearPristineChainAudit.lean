import InfoGeometry.Exceptional.FreudenthalGlobalJacobiFrontier
import InfoGeometry.Physics.NuclearFiveGradeBdGSolovievClosure

/-!
# Pristine finite-chain boundary

This file composes the two verified sides of the nuclear formalization:

* the generic Freudenthal carrier, whose global Jacobi theorem is conditional
  on its explicit homogeneous-cell data; and
* the concrete finite CAR--CCR/BdG/Soloviev operator model.

The statement intentionally does not identify these carriers.  Such an
identification requires a separately proved grade-preserving intertwiner.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearPristineChainAudit

open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Physics.NuclearTwoModeCARFiveGrade
open InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation
open InfoGeometry.Physics.NuclearBdGSolovievCompression
open InfoGeometry.Physics.NuclearCARPhononCommonCarrier
open InfoGeometry.Physics.NuclearFiveGradeBdGSolovievClosure

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The current formal boundary: generic global Jacobi and concrete finite
operator closure coexist, while the missing carrier comparison remains an
explicit hypothesis-free frontier rather than a claimed theorem. -/
theorem pristine_chain_boundary_packet
    (data : FiveGradedHomogeneousJacobiData D)
    (Eqp ω V ξ Δ E : ℂ) :
    (∀ x y z : FiveGradedCarrier D, fiveJacobiator D x y z = 0) ∧
      (∀ g : Generator, HasGrade (degree g) (represent g)) ∧
      (∀ g h : Generator,
        HasGrade (degree g + degree h)
          (commutator (represent g) (represent h))) ∧
      (bdgBlock ξ Δ * bdgBlock ξ Δ =
        (ξ ^ 2 + Δ ^ 2) • (1 : Mat2)) ∧
      (solovievBlock Eqp ω V =
        (Eqp + ω / 2) • (1 : Mat2) + bdgBlock (ω / 2) V) ∧
      (∀ φ : EvenSector,
        compressedOscillatorHamiltonian Eqp ω V φ =
          Matrix.mulVec (solovievBlock Eqp ω V) φ) := by
  refine ⟨fun x y z => global_fiveGraded_jacobi_of_data D data x y z,
    represent_hasGrade, represented_commutator_hasGrade,
    bdgBlock_sq ξ Δ, solovievBlock_eq_center_add_bdg Eqp ω V,
    compressedOscillatorHamiltonian_eq_soloviev Eqp ω V⟩

end InfoGeometry.Physics.NuclearPristineChainAudit
