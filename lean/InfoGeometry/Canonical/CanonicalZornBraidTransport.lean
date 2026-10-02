import InfoGeometry.Physics.QCDCanonicalComplexZornBridge
import InfoGeometry.Physics.YangBaxterZornBridge
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornBraidTransport

open Matrix
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Physics.QCDCanonicalComplexZornBridge
open InfoGeometry.Physics.QCDFureyZornProjectorBridge
open InfoGeometry.Physics.SplitOctonionBraidSU3
open InfoGeometry.Physics.YangBaxterZornBridge
open InfoGeometry.Physics.B3PresentedGroup (B3 B3Gen)

def coordinates : CanonicalZorn ≃ₗ[ℂ] (Fin 8 → ℂ) where
  toFun state := zornToFin8 (canonicalComplexEquiv state)
  invFun vector := canonicalComplexEquiv.symm (fin8ToZorn vector)
  left_inv state := by
    change canonicalComplexEquiv.symm
      (fin8ToZorn (zornToFin8 (canonicalComplexEquiv state))) = state
    rw [fin8ToZorn_zornToFin8, Equiv.symm_apply_apply]
  right_inv vector := by
    change zornToFin8
      (canonicalComplexEquiv (canonicalComplexEquiv.symm (fin8ToZorn vector))) = vector
    rw [Equiv.apply_symm_apply, zornToFin8_fin8ToZorn]
  map_add' left right := by
    rw [canonicalComplexEquiv_add, zornToFin8_add]
  map_smul' scalar state := by
    change zornToFin8 (canonicalComplexEquiv (scalar • state)) =
      scalar • zornToFin8 (canonicalComplexEquiv state)
    rw [canonicalComplexEquiv_smul, zornToFin8_smul]

theorem canonical_Q_circular_lanes (axis : Fin 3) :
    canonicalComplexEquiv.symm (Q_k axis) =
      upperLane (e_k axis) + lowerLane (e_k axis) := by
  apply canonicalComplexEquiv.injective
  rw [Equiv.apply_symm_apply, canonicalComplexEquiv_add,
    canonicalComplexEquiv_upperLane, canonicalComplexEquiv_lowerLane]
  apply zorn_ext <;> simp [Q_k, zornAdd]

def operatorEquiv : Matrix (Fin 8) (Fin 8) ℂ ≃ₐ[ℂ] Module.End ℂ CanonicalZorn :=
  (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin 8)).trans
    (coordinates.symm.conjAlgEquiv ℂ)

theorem operatorEquiv_apply (operator : Matrix (Fin 8) (Fin 8) ℂ)
    (state : CanonicalZorn) :
    operatorEquiv operator state =
      coordinates.symm (operator *ᵥ coordinates state) := rfl

theorem coordinates_operatorEquiv_apply (operator : Matrix (Fin 8) (Fin 8) ℂ)
    (state : CanonicalZorn) :
    coordinates (operatorEquiv operator state) = operator *ᵥ coordinates state := by
  rw [operatorEquiv_apply, LinearEquiv.apply_symm_apply]

theorem operatorEquiv_leftMulQ_apply (axis : Fin 3) (state : CanonicalZorn) :
    operatorEquiv (LeftMulQ axis) state =
      zMul (canonicalComplexEquiv.symm (Q_k axis)) state := by
  apply coordinates.injective
  rw [coordinates_operatorEquiv_apply]
  change LeftMulQ axis *ᵥ zornToFin8 (canonicalComplexEquiv state) =
    zornToFin8 (canonicalComplexEquiv
      (zMul (canonicalComplexEquiv.symm (Q_k axis)) state))
  rw [LeftMulQ_apply, fin8ToZorn_zornToFin8, canonicalComplexEquiv_mul,
    Equiv.apply_symm_apply]

theorem operatorEquiv_leftMulR_apply (axis : Fin 3) (state : CanonicalZorn) :
    operatorEquiv (LeftMulR axis) state =
      state + Complex.I • zMul (canonicalComplexEquiv.symm (Q_k axis)) state := by
  rw [LeftMulR_eq]
  change operatorEquiv (1 + Complex.I • LeftMulQ axis) state = _
  rw [map_add, map_smul, map_one]
  change state + Complex.I • operatorEquiv (LeftMulQ axis) state = _
  rw [operatorEquiv_leftMulQ_apply]

theorem canonical_Q_operator_square (axis : Fin 3) :
    operatorEquiv (LeftMulQ axis) * operatorEquiv (LeftMulQ axis) = 1 := by
  simpa only [map_mul, Id8, map_one] using
    congrArg operatorEquiv (leftMulQ_sq axis)

def braidRepresentation : B3 →* (Module.End ℂ CanonicalZorn)ˣ :=
  (Units.map operatorEquiv.toRingEquiv.toMonoidHom).comp zornPhi

theorem braidRepresentation_apply (braid : B3) (state : CanonicalZorn) :
    (braidRepresentation braid : Module.End ℂ CanonicalZorn) state =
      coordinates.symm
        ((zornPhi braid : Matrix (Fin 8) (Fin 8) ℂ) *ᵥ coordinates state) := rfl

theorem coordinates_intertwines (braid : B3) (state : CanonicalZorn) :
    coordinates ((braidRepresentation braid : Module.End ℂ CanonicalZorn) state) =
      (zornPhi braid : Matrix (Fin 8) (Fin 8) ℂ) *ᵥ coordinates state := by
  rw [braidRepresentation_apply, LinearEquiv.apply_symm_apply]

theorem braidRepresentation_sig0_apply (state : CanonicalZorn) :
    (braidRepresentation (PresentedGroup.of B3Gen.sig0 : B3) :
        Module.End ℂ CanonicalZorn) state =
      state + Complex.I • zMul (canonicalComplexEquiv.symm (Q_k 0)) state := by
  change operatorEquiv
    (zornPhi (PresentedGroup.of B3Gen.sig0 : B3) : Matrix (Fin 8) (Fin 8) ℂ) state = _
  rw [zornPhi_sig0]
  exact operatorEquiv_leftMulR_apply 0 state

theorem braidRepresentation_sig1_apply (state : CanonicalZorn) :
    (braidRepresentation (PresentedGroup.of B3Gen.sig1 : B3) :
        Module.End ℂ CanonicalZorn) state =
      state + Complex.I • zMul (canonicalComplexEquiv.symm (Q_k 1)) state := by
  change operatorEquiv
    (zornPhi (PresentedGroup.of B3Gen.sig1 : B3) : Matrix (Fin 8) (Fin 8) ℂ) state = _
  rw [zornPhi_sig1]
  exact operatorEquiv_leftMulR_apply 1 state

theorem canonical_generators_artin :
    operatorEquiv (LeftMulR 0) * operatorEquiv (LeftMulR 1) *
        operatorEquiv (LeftMulR 0) =
      operatorEquiv (LeftMulR 1) * operatorEquiv (LeftMulR 0) *
        operatorEquiv (LeftMulR 1) := by
  simpa only [map_mul] using congrArg operatorEquiv leftMulR_B3_braid

theorem conjugated_generators_artin (transport : CanonicalZorn ≃ₗ[ℂ] CanonicalZorn) :
    transport.conjAlgEquiv ℂ (operatorEquiv (LeftMulR 0)) *
        transport.conjAlgEquiv ℂ (operatorEquiv (LeftMulR 1)) *
        transport.conjAlgEquiv ℂ (operatorEquiv (LeftMulR 0)) =
      transport.conjAlgEquiv ℂ (operatorEquiv (LeftMulR 1)) *
        transport.conjAlgEquiv ℂ (operatorEquiv (LeftMulR 0)) *
        transport.conjAlgEquiv ℂ (operatorEquiv (LeftMulR 1)) := by
  simpa only [map_mul] using
    congrArg (transport.conjAlgEquiv ℂ) canonical_generators_artin

theorem regular_generator_covariance
    (transport : CanonicalZorn ≃ₗ[ℂ] CanonicalZorn)
    (preserves_mul : ∀ left right,
      transport (zMul left right) = zMul (transport left) (transport right))
    (axis : Fin 3) (state : CanonicalZorn) :
    transport.conjAlgEquiv ℂ (operatorEquiv (LeftMulQ axis)) state =
      zMul (transport (canonicalComplexEquiv.symm (Q_k axis))) state := by
  change transport (operatorEquiv (LeftMulQ axis) (transport.symm state)) = _
  rw [operatorEquiv_leftMulQ_apply, preserves_mul, LinearEquiv.apply_symm_apply]

theorem braid_generator_covariance
    (transport : CanonicalZorn ≃ₗ[ℂ] CanonicalZorn)
    (preserves_mul : ∀ left right,
      transport (zMul left right) = zMul (transport left) (transport right))
    (axis : Fin 3) (state : CanonicalZorn) :
    transport.conjAlgEquiv ℂ (operatorEquiv (LeftMulR axis)) state =
      state + Complex.I •
        zMul (transport (canonicalComplexEquiv.symm (Q_k axis))) state := by
  change transport (operatorEquiv (LeftMulR axis) (transport.symm state)) = _
  simp only [operatorEquiv_leftMulR_apply, map_add, map_smul, preserves_mul,
    LinearEquiv.apply_symm_apply]

end InfoGeometry.Canonical.CanonicalZornBraidTransport
