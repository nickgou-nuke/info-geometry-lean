/-
InfoGeometry/OperatorAlgebra/ChiralProjectorFromInvolution.lean

Constructive chiral projectors from an involution.

This module hardens the first chiral step:

  chi^2 = 1
    => Pleft = (1 + chi) / 2
    => Pright = (1 - chi) / 2

and proves the projector laws rather than accepting them as fields.

The result can be exported both as a `CircularPolarization` and as the
`ChiralStage` used by the Tomita-Cartan routing layer.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ChiralPolarization
import InfoGeometry.OperatorAlgebra.TomitaCartanSplit
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-! ## 1. Chiral projectors from an involution -/

/--
A chiral involution in an associative real algebra.

This is the constructive lane where the half-projectors are derived from
`chi_sq`, rather than supplied as proof-carrying fields.
-/
structure ChiralInvolution
    (Op : Type*) [Ring Op] [Algebra ℝ Op] where
  /-- Chiral grading/involution. -/
  chi : Op

  /-- Involution law. -/
  chi_sq :
    chi * chi = 1

namespace ChiralInvolution

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]
variable (C : ChiralInvolution Op)

/-- Left chiral projector, `(1 + chi) / 2`. -/
def Pleft : Op :=
  (1 / 2 : ℝ) • ((1 : Op) + C.chi)

/-- Right chiral projector, `(1 - chi) / 2`. -/
def Pright : Op :=
  (1 / 2 : ℝ) • ((1 : Op) - C.chi)

private theorem one_add_chi_mul_one_add_chi :
    ((1 : Op) + C.chi) * ((1 : Op) + C.chi) =
      (2 : ℝ) • ((1 : Op) + C.chi) := by
  calc
    ((1 : Op) + C.chi) * ((1 : Op) + C.chi)
        = (1 : Op) + C.chi + C.chi + C.chi * C.chi := by
            noncomm_ring
    _ = (1 : Op) + C.chi + C.chi + 1 := by
            rw [C.chi_sq]
    _ = (2 : ℝ) • ((1 : Op) + C.chi) := by
            rw [two_smul]
            abel

private theorem one_sub_chi_mul_one_sub_chi :
    ((1 : Op) - C.chi) * ((1 : Op) - C.chi) =
      (2 : ℝ) • ((1 : Op) - C.chi) := by
  calc
    ((1 : Op) - C.chi) * ((1 : Op) - C.chi)
        = (1 : Op) - C.chi - C.chi + C.chi * C.chi := by
            noncomm_ring
    _ = (1 : Op) - C.chi - C.chi + 1 := by
            rw [C.chi_sq]
    _ = (2 : ℝ) • ((1 : Op) - C.chi) := by
            rw [two_smul]
            abel

private theorem one_add_chi_mul_one_sub_chi :
    ((1 : Op) + C.chi) * ((1 : Op) - C.chi) = 0 := by
  calc
    ((1 : Op) + C.chi) * ((1 : Op) - C.chi)
        = (1 : Op) - C.chi + C.chi - C.chi * C.chi := by
            noncomm_ring
    _ = (1 : Op) - C.chi + C.chi - 1 := by
            rw [C.chi_sq]
    _ = 0 := by
            abel

private theorem one_sub_chi_mul_one_add_chi :
    ((1 : Op) - C.chi) * ((1 : Op) + C.chi) = 0 := by
  calc
    ((1 : Op) - C.chi) * ((1 : Op) + C.chi)
        = (1 : Op) + C.chi - C.chi - C.chi * C.chi := by
            noncomm_ring
    _ = (1 : Op) + C.chi - C.chi - 1 := by
            rw [C.chi_sq]
    _ = 0 := by
            abel

/-- The left chiral projector is idempotent. -/
@[simp]
theorem Pleft_idem :
    C.Pleft * C.Pleft = C.Pleft := by
  dsimp [Pleft]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul,
    C.one_add_chi_mul_one_add_chi, smul_smul]
  norm_num

/-- The right chiral projector is idempotent. -/
@[simp]
theorem Pright_idem :
    C.Pright * C.Pright = C.Pright := by
  dsimp [Pright]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul,
    C.one_sub_chi_mul_one_sub_chi, smul_smul]
  norm_num

/-- The left and right chiral projectors are orthogonal. -/
@[simp]
theorem Pleft_mul_Pright :
    C.Pleft * C.Pright = 0 := by
  dsimp [Pleft, Pright]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul,
    C.one_add_chi_mul_one_sub_chi]
  simp

/-- Orthogonality in the other order. -/
@[simp]
theorem Pright_mul_Pleft :
    C.Pright * C.Pleft = 0 := by
  dsimp [Pleft, Pright]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul,
    C.one_sub_chi_mul_one_add_chi]
  simp

/-- The chiral projectors are complementary. -/
theorem Pleft_add_Pright :
    C.Pleft + C.Pright = 1 := by
  dsimp [Pleft, Pright]
  calc
    (1 / 2 : ℝ) • ((1 : Op) + C.chi) +
        (1 / 2 : ℝ) • ((1 : Op) - C.chi)
        = (1 / 2 : ℝ) • (((1 : Op) + C.chi) + ((1 : Op) - C.chi)) := by
            rw [← smul_add]
    _ = (1 / 2 : ℝ) • ((2 : ℝ) • (1 : Op)) := by
            congr 1
            rw [two_smul]
            abel
    _ = 1 := by
            rw [smul_smul]
            norm_num

/-- The difference of the chiral projectors is the grading. -/
theorem Pleft_sub_Pright :
    C.Pleft - C.Pright = C.chi := by
  dsimp [Pleft, Pright]
  calc
    (1 / 2 : ℝ) • ((1 : Op) + C.chi) -
        (1 / 2 : ℝ) • ((1 : Op) - C.chi)
        = (1 / 2 : ℝ) • (((1 : Op) + C.chi) - ((1 : Op) - C.chi)) := by
            rw [← smul_sub]
    _ = (1 / 2 : ℝ) • ((2 : ℝ) • C.chi) := by
            congr 1
            rw [two_smul]
            abel
    _ = C.chi := by
            rw [smul_smul]
            norm_num

/--
Export the constructive involution as the broader proof-carrying
`CircularPolarization` socket.
-/
def toCircularPolarization : CircularPolarization Op where
  chi := C.chi
  chi_sq := C.chi_sq
  P_left := C.Pleft
  P_right := C.Pright
  P_left_def := rfl
  P_right_def := rfl
  P_left_idem := C.Pleft_idem
  P_right_idem := C.Pright_idem
  P_left_mul_right := C.Pleft_mul_Pright
  P_right_mul_left := C.Pright_mul_Pleft
  P_sum := C.Pleft_add_Pright

/--
Export the constructive involution as the `ChiralStage` used by the
Tomita-Cartan split.
-/
def toChiralStage : TomitaCartanSplit.ChiralStage Op where
  Pleft := C.Pleft
  Pright := C.Pright
  Pleft_idem := C.Pleft_idem
  Pright_idem := C.Pright_idem
  complementary := C.Pleft_add_Pright
  disjoint_left := C.Pleft_mul_Pright
  disjoint_right := C.Pright_mul_Pleft

end ChiralInvolution

/-! ## 2. Symmetries preserving the involution preserve the projectors -/

/--
A minimal real-algebra symmetry action socket for chiral involutions.

This is deliberately small: it records only the preservation laws needed to
prove that `chi`-preserving dynamics preserves the derived projectors.
-/
structure ChiralInvolutionAction
    (G Op : Type*) [Group G] [Ring Op] [Algebra ℝ Op] where
  act : G → Op → Op

  map_one :
    ∀ g : G, act g 1 = 1

  map_add :
    ∀ (g : G) (x y : Op), act g (x + y) = act g x + act g y

  map_sub :
    ∀ (g : G) (x y : Op), act g (x - y) = act g x - act g y

  map_mul :
    ∀ (g : G) (x y : Op), act g (x * y) = act g x * act g y

  map_smul :
    ∀ (g : G) (a : ℝ) (x : Op), act g (a • x) = a • act g x

namespace ChiralInvolutionAction

variable {G Op : Type*} [Group G] [Ring Op] [Algebra ℝ Op]
variable (A : ChiralInvolutionAction G Op)
variable (C : ChiralInvolution Op)

/-- If a symmetry fixes `chi`, it fixes the left projector derived from `chi`. -/
theorem map_Pleft_of_chi_invariant
    (g : G)
    (hchi : A.act g C.chi = C.chi) :
    A.act g C.Pleft = C.Pleft := by
  dsimp [ChiralInvolution.Pleft]
  rw [A.map_smul, A.map_add, A.map_one, hchi]

/-- If a symmetry fixes `chi`, it fixes the right projector derived from `chi`. -/
theorem map_Pright_of_chi_invariant
    (g : G)
    (hchi : A.act g C.chi = C.chi) :
    A.act g C.Pright = C.Pright := by
  dsimp [ChiralInvolution.Pright]
  rw [A.map_smul, A.map_sub, A.map_one, hchi]

/-- A left support/image condition for a projector. -/
def leftImage
    (p : Op) : Set Op :=
  {x : Op | p * x = x}

/--
If a symmetry fixes a projector, then it preserves the left image of that
projector.
-/
theorem leftImage_invariant_of_projector_invariant
    (g : G)
    {p x : Op}
    (hp : A.act g p = p)
    (hx : x ∈ leftImage p) :
    A.act g x ∈ leftImage p := by
  dsimp [leftImage] at hx ⊢
  calc
    p * A.act g x
        = A.act g p * A.act g x := by
            rw [hp]
    _ = A.act g (p * x) := by
            exact (A.map_mul g p x).symm
    _ = A.act g x := by
            rw [hx]

/--
If a symmetry fixes `chi`, then it preserves the left chiral sector derived
from `chi`.
-/
theorem leftChiralImage_invariant_of_chi_invariant
    (g : G)
    (hchi : A.act g C.chi = C.chi)
    {x : Op}
    (hx : x ∈ leftImage C.Pleft) :
    A.act g x ∈ leftImage C.Pleft :=
  A.leftImage_invariant_of_projector_invariant
    g
    (A.map_Pleft_of_chi_invariant C g hchi)
    hx

/--
If a symmetry fixes `chi`, then it preserves the right chiral sector derived
from `chi`.
-/
theorem rightChiralImage_invariant_of_chi_invariant
    (g : G)
    (hchi : A.act g C.chi = C.chi)
    {x : Op}
    (hx : x ∈ leftImage C.Pright) :
    A.act g x ∈ leftImage C.Pright :=
  A.leftImage_invariant_of_projector_invariant
    g
    (A.map_Pright_of_chi_invariant C g hchi)
    hx

end ChiralInvolutionAction

/-! ## 3. Owner theorem -/

/--
Constructing chiral projector stages from involutions.
-/
theorem chiralProjectorFromInvolutionOwnerTarget :
  ∀ (Op : Type*) [Ring Op] [Algebra ℝ Op],
  ∀ C : ChiralInvolution Op,
    C.Pleft * C.Pleft = C.Pleft ∧
    C.Pright * C.Pright = C.Pright ∧
    C.Pleft * C.Pright = 0 ∧
    C.Pright * C.Pleft = 0 ∧
    C.Pleft + C.Pright = 1 ∧
    C.Pleft - C.Pright = C.chi := by
  intro Op _ _ C
  exact ⟨
    C.Pleft_idem,
    C.Pright_idem,
    C.Pleft_mul_Pright,
    C.Pright_mul_Pleft,
    C.Pleft_add_Pright,
    C.Pleft_sub_Pright
  ⟩

/-- Direct packet for one chiral involution's two projectors. -/
theorem chiralProjectorFromInvolution_packet
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (C : ChiralInvolution Op) :
    C.Pleft * C.Pleft = C.Pleft ∧
      C.Pright * C.Pright = C.Pright ∧
      C.Pleft * C.Pright = 0 ∧
      C.Pright * C.Pleft = 0 ∧
      C.Pleft + C.Pright = 1 ∧
      C.Pleft - C.Pright = C.chi :=
  chiralProjectorFromInvolutionOwnerTarget Op C

end InfoGeometry.OperatorAlgebra
