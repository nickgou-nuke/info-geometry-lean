/-
InfoGeometry/OperatorAlgebra/OperatorChiralLightcone.lean

Operator chiral algebra and chiral lightcone.

The operator chiral algebra is the Peirce decomposition of an ambient operator
algebra by the chiral projectors `P_left` and `P_right`.

The chiral lightcone is the Krein null cone on a carrier, refined by left/right
chiral support.

The two are not definitionally the same object. Algebraic defects live in the
represented operator algebra; lightlike vectors live in the carrier. A
representation bridge should relate them.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.ChiralPolarization
import InfoGeometry.OperatorAlgebra.KreinIsotropicCone

noncomputable section

namespace OperatorChiralLightcone

open InfoGeometry.OperatorAlgebra

/-! ## 1. Chiral side labels -/

/--
The two chiral sides.
-/
inductive ChiralSide where
  | left
  | right
deriving DecidableEq, Repr

namespace ChiralSide

/-- The opposite chiral side. -/
def opposite : ChiralSide → ChiralSide
  | left => right
  | right => left

@[simp]
theorem opposite_left :
    opposite left = right :=
  rfl

@[simp]
theorem opposite_right :
    opposite right = left :=
  rfl

/--
The operator-algebra projector associated to a chiral side.
-/
def opProjector
    {Op : Type*} [Ring Op] [Module ℝ Op]
    (C : CircularPolarization Op) :
    ChiralSide → Op
  | left => C.P_left
  | right => C.P_right

/--
The module-level projector associated to a chiral side.
-/
def moduleProjector
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (C : ModuleCircularPolarization H) :
    ChiralSide → H →ₗ[ℝ] H
  | left => C.P_left
  | right => C.P_right

end ChiralSide

/-! ## 2. Operator chiral algebra -/

/--
An operator lies in the chiral corner `target ← source` when it is supported
as

`P_target * x * P_source = x`.

Thus:

* `left, left` is the left-preserving corner;
* `right, right` is the right-preserving corner;
* `right, left` maps left into right;
* `left, right` maps right into left.
-/
def IsChiralCorner
    {Op : Type*} [Ring Op] [Module ℝ Op]
    (C : CircularPolarization Op)
    (target source : ChiralSide)
    (x : Op) : Prop :=
  ChiralSide.opProjector C target *
      x *
      ChiralSide.opProjector C source = x

/--
The left-preserving operator corner.
-/
def IsLeftLeft
    {Op : Type*} [Ring Op] [Module ℝ Op]
    (C : CircularPolarization Op)
    (x : Op) : Prop :=
  IsChiralCorner C ChiralSide.left ChiralSide.left x

/--
The right-preserving operator corner.
-/
def IsRightRight
    {Op : Type*} [Ring Op] [Module ℝ Op]
    (C : CircularPolarization Op)
    (x : Op) : Prop :=
  IsChiralCorner C ChiralSide.right ChiralSide.right x

/--
The operator corner mapping right chirality into left chirality.
-/
def IsLeftRight
    {Op : Type*} [Ring Op] [Module ℝ Op]
    (C : CircularPolarization Op)
    (x : Op) : Prop :=
  IsChiralCorner C ChiralSide.left ChiralSide.right x

/--
The operator corner mapping left chirality into right chirality.
-/
def IsRightLeft
    {Op : Type*} [Ring Op] [Module ℝ Op]
    (C : CircularPolarization Op)
    (x : Op) : Prop :=
  IsChiralCorner C ChiralSide.right ChiralSide.left x

/--
Even operators commute with the chiral grading.
They preserve the chiral splitting.
-/
def IsChiralEven
    {Op : Type*} [Ring Op] [Module ℝ Op]
    (C : CircularPolarization Op)
    (x : Op) : Prop :=
  C.chi * x = x * C.chi

/--
Odd operators anticommute with the chiral grading.
They flip the chiral splitting.
-/
def IsChiralOdd
    {Op : Type*} [Ring Op] [Module ℝ Op]
    (C : CircularPolarization Op)
    (x : Op) : Prop :=
  C.chi * x = -(x * C.chi)

/--
The operator chiral algebra package.

This is just the ambient operator algebra equipped with its circular/chiral
polarization. The actual sectors are predicates/corners inside the same
ambient algebra.
-/
structure OperatorChiralAlgebra
    (Op : Type*) [Ring Op] [Module ℝ Op] where
  circular : CircularPolarization Op

namespace OperatorChiralAlgebra

variable {Op : Type*} [Ring Op] [Module ℝ Op]
variable (A : OperatorChiralAlgebra Op)

/-- Left-preserving corner of the operator chiral algebra. -/
def leftLeft
    (x : Op) : Prop :=
  IsLeftLeft A.circular x

/-- Right-preserving corner of the operator chiral algebra. -/
def rightRight
    (x : Op) : Prop :=
  IsRightRight A.circular x

/-- Right-to-left chiral-flipping corner. -/
def leftRight
    (x : Op) : Prop :=
  IsLeftRight A.circular x

/-- Left-to-right chiral-flipping corner. -/
def rightLeft
    (x : Op) : Prop :=
  IsRightLeft A.circular x

/-- Even/preserving operators. -/
def even
    (x : Op) : Prop :=
  IsChiralEven A.circular x

/-- Odd/flipping operators. -/
def odd
    (x : Op) : Prop :=
  IsChiralOdd A.circular x

end OperatorChiralAlgebra

/-! ## 3. Chiral vectors and the chiral lightcone -/

/--
A carrier vector is supported on a chiral side when the corresponding chiral
projector fixes it.
-/
def IsChiralVector
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (C : ModuleCircularPolarization H)
    (side : ChiralSide)
    (v : H) : Prop :=
  ChiralSide.moduleProjector C side v = v

/--
The chiral lightcone:

`v` is null for the Krein quadratic datum and is supported on one chiral side.
-/
def ChiralLightcone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H)
    (side : ChiralSide) : Set H :=
  {v : H | Q.IsNull v ∧ IsChiralVector C side v}

/--
The left chiral lightcone.
-/
def LeftChiralLightcone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H) : Set H :=
  ChiralLightcone Q C ChiralSide.left

/--
The right chiral lightcone.
-/
def RightChiralLightcone
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (Q : KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H) : Set H :=
  ChiralLightcone Q C ChiralSide.right

namespace ChiralLightcone

variable {H : Type*} [AddCommGroup H] [Module ℝ H]
variable {Q : KreinIsotropicCone.KreinQuadraticDatum H}
variable {C : ModuleCircularPolarization H}

/--
The chiral lightcone is closed under real scaling.

This is the projective property: scale is not part of the lightlike direction.
-/
theorem smul_mem
    (side : ChiralSide)
    (a : ℝ)
    {v : H}
    (hv : v ∈ ChiralLightcone Q C side) :
    a • v ∈ ChiralLightcone Q C side := by
  rcases hv with ⟨hnull, hchir⟩
  constructor
  · exact Q.null_smul a v hnull
  · dsimp [IsChiralVector] at hchir ⊢
    cases side with
    | left =>
        dsimp [ChiralSide.moduleProjector] at hchir ⊢
        rw [map_smul, hchir]
    | right =>
        dsimp [ChiralSide.moduleProjector] at hchir ⊢
        rw [map_smul, hchir]

end ChiralLightcone

/-! ## 4. Modular/CPT mirror of the chiral lightcone -/

/--
A mirror of chiral lightcones.

This is the carrier-level version of the CPT branch:

`J` preserves the Krein quadratic readout and swaps left/right chiral support.
-/
structure ChiralLightconeMirror
    (H : Type*) [AddCommGroup H] [Module ℝ H]
    (Q : KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H) where
  /-- Modular/CPT mirror on the carrier. -/
  J : H →ₗ[ℝ] H

  /-- The mirror preserves the Krein quadratic readout. -/
  q_preserving :
    ∀ v : H, Q.q (J v) = Q.q v

  /-- `J` sends left support to right support. -/
  maps_left_to_right :
    ∀ v : H, C.P_right (J v) = J (C.P_left v)

  /-- `J` sends right support to left support. -/
  maps_right_to_left :
    ∀ v : H, C.P_left (J v) = J (C.P_right v)

namespace ChiralLightconeMirror

variable {H : Type*} [AddCommGroup H] [Module ℝ H]
variable {Q : KreinIsotropicCone.KreinQuadraticDatum H}
variable {C : ModuleCircularPolarization H}
variable (M : ChiralLightconeMirror H Q C)

/--
The mirror sends the left chiral lightcone to the right chiral lightcone.
-/
theorem maps_left_lightcone_to_right
    {v : H}
    (hv : v ∈ LeftChiralLightcone Q C) :
    M.J v ∈ RightChiralLightcone Q C := by
  rcases hv with ⟨hnull, hleft⟩
  constructor
  · dsimp [KreinIsotropicCone.KreinQuadraticDatum.IsNull] at hnull ⊢
    rw [M.q_preserving, hnull]
  · dsimp [IsChiralVector] at hleft ⊢
    dsimp [ChiralSide.moduleProjector] at hleft ⊢
    rw [M.maps_left_to_right, hleft]

/--
The mirror sends the right chiral lightcone to the left chiral lightcone.
-/
theorem maps_right_lightcone_to_left
    {v : H}
    (hv : v ∈ RightChiralLightcone Q C) :
    M.J v ∈ LeftChiralLightcone Q C := by
  rcases hv with ⟨hnull, hright⟩
  constructor
  · dsimp [KreinIsotropicCone.KreinQuadraticDatum.IsNull] at hnull ⊢
    rw [M.q_preserving, hnull]
  · dsimp [IsChiralVector] at hright ⊢
    dsimp [ChiralSide.moduleProjector] at hright ⊢
    rw [M.maps_right_to_left, hright]

end ChiralLightconeMirror

/-! ## 5. Operator defects and chiral lightcone bridge -/

/--
A represented algebraic defect hits a chiral lightcone.

This is the correct bridge between the operator defect algebra and the carrier
null geometry. The defect is algebraic; the lightcone is geometric.
-/
structure OperatorDefectChiralLightconeBridge
    (Split Op H : Type*)
    [Ring Op]
    [AddCommGroup H] [Module ℝ H]
    (Q : KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H) where
  /-- Representation of split algebra elements by operators. -/
  rep : Split → Op

  /-- Action of represented operators on the carrier. -/
  act : Op → H → H

  /-- Defect locus inside the split algebra. -/
  defectLocus : Set Split

  /-- Defects map to nilpotent represented operators. -/
  defect_maps_to_nilpotent :
    ∀ a : Split,
      a ∈ defectLocus →
        IsNilpotentElement (rep a)

  /--
  Defects hit either the left or the right chiral lightcone.

  Concrete models may refine this into a fixed side or into a charge-dependent
  side.
  -/
  defect_hits_chiral_lightcone :
    ∀ a : Split,
      a ∈ defectLocus →
        ∃ side : ChiralSide,
        ∃ v : H,
          v ≠ 0 ∧
          act (rep a) v ∈ ChiralLightcone Q C side

namespace OperatorDefectChiralLightconeBridge

variable
    {Split Op H : Type*}
    [Ring Op]
    [AddCommGroup H] [Module ℝ H]
    {Q : KreinIsotropicCone.KreinQuadraticDatum H}
    {C : ModuleCircularPolarization H}

variable (B : OperatorDefectChiralLightconeBridge Split Op H Q C)

/--
A defect maps to a nilpotent represented operator.
-/
theorem defect_nilpotent
    {a : Split}
    (ha : a ∈ B.defectLocus) :
    IsNilpotentElement (B.rep a) :=
  B.defect_maps_to_nilpotent a ha

/--
A defect has a nonzero carrier vector whose image is on a chiral lightcone.
-/
theorem defect_has_chiral_lightlike_image
    {a : Split}
    (ha : a ∈ B.defectLocus) :
    ∃ side : ChiralSide,
    ∃ v : H,
      v ≠ 0 ∧
      B.act (B.rep a) v ∈ ChiralLightcone Q C side :=
  B.defect_hits_chiral_lightcone a ha

end OperatorDefectChiralLightconeBridge

end OperatorChiralLightcone
