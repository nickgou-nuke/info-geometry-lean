import Mathlib.Algebra.Ring.TransferInstance
import InfoGeometry.Clifford.OperatorValuedJones
import InfoGeometry.Canonical.CoordinateFreeConnectionChannels

/-!
# The causal-coordinate carrier as an operator ring

The four operator-valued causal coordinates are not a second matrix algebra.
Their associative ring structure is transported from `M₂(B)` through the
proved reconstruction equivalence.  Consequently the coordinate-free
connection-channel theorems apply without introducing another curvature or
commutator definition.
-/

noncomputable section

namespace InfoGeometry.Clifford

open InfoGeometry.Canonical.CoordinateFreeConnectionChannels

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- The associative ring structure transported from `M₂(B)`. -/
noncomputable instance causalOperatorCoordinatesRing :
    Ring (CausalOperatorCoordinates B) :=
  Equiv.ring (causalOperatorCoordinatesEquiv (B := B))

/-- Complex scalar multiplication transported from the matrix algebra. -/
noncomputable instance causalOperatorCoordinatesAlgebra :
    Algebra ℂ (CausalOperatorCoordinates B) :=
  Equiv.algebra ℂ (causalOperatorCoordinatesEquiv (B := B))

/-- Reconstruction is a genuine ring equivalence, not merely a coordinate bijection. -/
noncomputable def causalOperatorCoordinatesRingEquiv :
    CausalOperatorCoordinates B ≃+* Matrix (Fin 2) (Fin 2) B where
  toEquiv := causalOperatorCoordinatesEquiv (B := B)
  map_add' A C := by
    change reconstruct_causal
        ((causalOperatorCoordinatesEquiv (B := B)).symm
          (reconstruct_causal A + reconstruct_causal C)) = _
    exact reconstruct_causalCoordinates _
  map_mul' A C := by
    change reconstruct_causal
        ((causalOperatorCoordinatesEquiv (B := B)).symm
          (reconstruct_causal A * reconstruct_causal C)) = _
    exact reconstruct_causalCoordinates _

/-- Reconstruction as a complex-algebra equivalence. -/
noncomputable def causalOperatorCoordinatesAlgEquiv :
    CausalOperatorCoordinates B ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) B where
  toFun := reconstruct_causal
  invFun := causalCoordinates
  left_inv := causalCoordinates_reconstruct
  right_inv := reconstruct_causalCoordinates
  map_mul' A C := by
    change reconstruct_causal
        ((causalOperatorCoordinatesEquiv (B := B)).symm
          (reconstruct_causal A * reconstruct_causal C)) = _
    exact reconstruct_causalCoordinates _
  map_add' A C := by
    change reconstruct_causal
        ((causalOperatorCoordinatesEquiv (B := B)).symm
          (reconstruct_causal A + reconstruct_causal C)) = _
    exact reconstruct_causalCoordinates _
  commutes' c := by
    change reconstruct_causal
        ((causalOperatorCoordinatesEquiv (B := B)).symm
          (algebraMap ℂ (Matrix (Fin 2) (Fin 2) B) c)) = _
    exact reconstruct_causalCoordinates _

@[simp] theorem reconstruct_causal_zero :
    reconstruct_causal (0 : CausalOperatorCoordinates B) = 0 :=
  map_zero (causalOperatorCoordinatesRingEquiv (B := B))

@[simp] theorem reconstruct_causal_one :
    reconstruct_causal (1 : CausalOperatorCoordinates B) = 1 :=
  map_one (causalOperatorCoordinatesRingEquiv (B := B))

@[simp] theorem reconstruct_causal_add
    (A C : CausalOperatorCoordinates B) :
    reconstruct_causal (A + C) = reconstruct_causal A + reconstruct_causal C :=
  map_add (causalOperatorCoordinatesRingEquiv (B := B)) A C

@[simp] theorem reconstruct_causal_neg
    (A : CausalOperatorCoordinates B) :
    reconstruct_causal (-A) = -reconstruct_causal A :=
  map_neg (causalOperatorCoordinatesRingEquiv (B := B)) A

@[simp] theorem reconstruct_causal_sub
    (A C : CausalOperatorCoordinates B) :
    reconstruct_causal (A - C) = reconstruct_causal A - reconstruct_causal C :=
  map_sub (causalOperatorCoordinatesRingEquiv (B := B)) A C

@[simp] theorem reconstruct_causal_mul
    (A C : CausalOperatorCoordinates B) :
    reconstruct_causal (A * C) = reconstruct_causal A * reconstruct_causal C :=
  map_mul (causalOperatorCoordinatesRingEquiv (B := B)) A C

/-- Reconstruction as the repository's coordinate-free connection channel. -/
noncomputable def causalReconstructionChannel :
    ConnectionChannel
      (A := CausalOperatorCoordinates B)
      (B := Matrix (Fin 2) (Fin 2) B) :=
  (causalOperatorCoordinatesRingEquiv (B := B)).toRingHom

/-- Operator-coordinate commutators reconstruct to matrix commutators. -/
theorem reconstruct_causal_commutator
    (A C : CausalOperatorCoordinates B) :
    reconstruct_causal (commutator A C) =
      commutator (reconstruct_causal A) (reconstruct_causal C) := by
  exact ConnectionChannel.map_commutator
    (causalReconstructionChannel (B := B)) A C

/-- The complete two-slot curvature expression is preserved by reconstruction. -/
theorem reconstruct_causal_twoSlotCurvature
    (dAC dCA A C : CausalOperatorCoordinates B) :
    reconstruct_causal (twoSlotCurvature dAC dCA A C) =
      twoSlotCurvature
        (reconstruct_causal dAC) (reconstruct_causal dCA)
        (reconstruct_causal A) (reconstruct_causal C) := by
  exact ConnectionChannel.map_twoSlotCurvature
    (causalReconstructionChannel (B := B)) dAC dCA A C

/-- Left-action torsion is preserved by the causal reconstruction channel. -/
theorem reconstruct_causal_twoSlotTorsionLeft
    (dEAC dECA OA EC OC EA : CausalOperatorCoordinates B) :
    reconstruct_causal (twoSlotTorsionLeft dEAC dECA OA EC OC EA) =
      twoSlotTorsionLeft
        (reconstruct_causal dEAC) (reconstruct_causal dECA)
        (reconstruct_causal OA) (reconstruct_causal EC)
        (reconstruct_causal OC) (reconstruct_causal EA) := by
  exact ConnectionChannel.map_twoSlotTorsionLeft
    (causalReconstructionChannel (B := B)) dEAC dECA OA EC OC EA

/-- A coordinate Bianchi identity remains a matrix Bianchi identity. -/
theorem reconstruct_causal_cyclicSum_of_zero
    (X Y Z : CausalOperatorCoordinates B)
    (h : cyclicSum X Y Z = 0) :
    cyclicSum (reconstruct_causal X) (reconstruct_causal Y)
      (reconstruct_causal Z) = 0 := by
  exact ConnectionChannel.map_cyclicSum_of_zero
    (causalReconstructionChannel (B := B)) X Y Z h

end InfoGeometry.Clifford
