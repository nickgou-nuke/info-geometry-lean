/-
InfoGeometry/OperatorAlgebra/SplitCliffordZ2Four.lean

Four-bit split Clifford Cartan bookkeeping.

`Cl(1,1)^⊗̂4` is treated here as a chosen four-Cartan framing: a local
`Z2^4` address space, Cartan involutions, and edge operators that flip exactly
one bit.  This is a kinematic Clifford/Krein substrate, not a proof of a
global `Z16` interacting classification.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SplitCliffordZ2Four

/-! ## 1. Four-bit charges -/

/-- A four-bit Cartan charge attached to a chosen `Cl(1,1)^⊗̂4` framing. -/
abbrev Z2FourCharge : Type :=
  Fin 4 → Bool

/-- Flip the `i`th Clifford bit. -/
def flipBit
    (i : Fin 4)
    (q : Z2FourCharge) : Z2FourCharge :=
  fun j => if j = i then !q j else q j

@[simp]
theorem flipBit_self
    (i : Fin 4)
    (q : Z2FourCharge) :
    flipBit i q i = !q i := by
  simp [flipBit]

@[simp]
theorem flipBit_ne
    {i j : Fin 4}
    (hij : j ≠ i)
    (q : Z2FourCharge) :
    flipBit i q j = q j := by
  simp [flipBit, hij]

/-- Flipping the same bit twice returns the original charge. -/
@[simp]
theorem flipBit_involutive
    (i : Fin 4)
    (q : Z2FourCharge) :
    flipBit i (flipBit i q) = q := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flipBit]
  · simp [flipBit, hji]

/-- Interpret a Boolean Cartan bit as the scalar sign `+1` or `-1`. -/
def bitSign
    (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The scalar sign attached to a four-bit charge in the `i`th Cartan direction. -/
def chargeSign
    (q : Z2FourCharge)
    (i : Fin 4) : ℝ :=
  bitSign (q i)

/-- Flipping the `i`th bit negates the corresponding scalar sign. -/
theorem chargeSign_flip_self
    (i : Fin 4)
    (q : Z2FourCharge) :
    chargeSign (flipBit i q) i = -chargeSign q i := by
  cases h : q i <;> simp [chargeSign, bitSign, flipBit, h]

/-- Flipping the `i`th bit leaves every other scalar sign unchanged. -/
theorem chargeSign_flip_ne
    {i j : Fin 4}
    (hij : j ≠ i)
    (q : Z2FourCharge) :
    chargeSign (flipBit i q) j = chargeSign q j := by
  simp [chargeSign, flipBit_ne hij q]

/-! ## 2. Four Cartan involutions and edge flips -/

/--
A chosen four-Cartan framing by commuting real-linear involutions.

This is explicit data: it is not inferred from the bare algebra `Cl(4,4)`.
-/
structure FourCartanInvolutions
    (H : Type*) [AddCommGroup H] [Module ℝ H] where
  /-- The four Cartan sign operators. -/
  Hcartan : Fin 4 → H →ₗ[ℝ] H

  /-- Each Cartan operator is involutive. -/
  involutive :
    ∀ i : Fin 4, (Hcartan i).comp (Hcartan i) = LinearMap.id

  /-- The Cartan operators commute. -/
  commute :
    ∀ i j : Fin 4,
      (Hcartan i).comp (Hcartan j) =
        (Hcartan j).comp (Hcartan i)

/-- A vector has the four-bit Cartan charge `q`. -/
def HasZ2FourCharge
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (C : FourCartanInvolutions H)
    (v : H)
    (q : Z2FourCharge) : Prop :=
  ∀ i : Fin 4, C.Hcartan i v = chargeSign q i • v

/--
An edge operator that flips the `i`th Cartan bit.

It anticommutes with the `i`th Cartan involution and commutes with the other
three.
-/
structure CliffordBitFlip
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (C : FourCartanInvolutions H)
    (i : Fin 4) where
  /-- The represented edge/odd Clifford generator. -/
  G : H →ₗ[ℝ] H

  /-- `G_i` anticommutes with `H_i`. -/
  anticomm_self :
    (C.Hcartan i).comp G = -(G.comp (C.Hcartan i))

  /-- `G_i` commutes with `H_j` for `j ≠ i`. -/
  commute_ne :
    ∀ j : Fin 4, j ≠ i →
      (C.Hcartan j).comp G = G.comp (C.Hcartan j)

namespace CliffordBitFlip

variable
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    {C : FourCartanInvolutions H}
    {i : Fin 4}
    (B : CliffordBitFlip C i)

/--
An edge operator maps a weight vector of charge `q` to one of charge
`flipBit i q`.
-/
theorem maps_charge_to_flipBit
    {v : H}
    {q : Z2FourCharge}
    (hv : HasZ2FourCharge C v q) :
    HasZ2FourCharge C (B.G v) (flipBit i q) := by
  intro j
  by_cases hji : j = i
  · subst j
    have happ := congrArg (fun L : H →ₗ[ℝ] H => L v) B.anticomm_self
    calc
      C.Hcartan i (B.G v)
          = -B.G (C.Hcartan i v) := by
              simpa [LinearMap.comp_apply] using happ
      _ = -B.G (chargeSign q i • v) := by
              rw [hv i]
      _ = -(chargeSign q i • B.G v) := by
              rw [B.G.map_smul]
      _ = chargeSign (flipBit i q) i • B.G v := by
              rw [chargeSign_flip_self]
              simp
  · have happ := congrArg (fun L : H →ₗ[ℝ] H => L v) (B.commute_ne j hji)
    calc
      C.Hcartan j (B.G v)
          = B.G (C.Hcartan j v) := by
              simpa [LinearMap.comp_apply] using happ
      _ = B.G (chargeSign q j • v) := by
              rw [hv j]
      _ = chargeSign q j • B.G v := by
              rw [B.G.map_smul]
      _ = chargeSign (flipBit i q) j • B.G v := by
              rw [chargeSign_flip_ne hji]

end CliffordBitFlip

/-! ## 3. Local split Clifford atom -/

/-- A local split Clifford atom `Cl(1,1)`. -/
structure SplitCliffordAtom
    (Op : Type*) [Ring Op] where
  /-- Positive-square generator. -/
  e : Op

  /-- Negative-square generator. -/
  f : Op

  /-- `e² = +1`. -/
  e_sq :
    e * e = 1

  /-- `f² = -1`. -/
  f_sq :
    f * f = -1

  /-- Same-atom anticommutation. -/
  anticomm :
    e * f = -(f * e)

namespace SplitCliffordAtom

variable {Op : Type*} [Ring Op]
variable (A : SplitCliffordAtom Op)

/-- The local Cartan/chiral bit `h = e f`. -/
def h : Op :=
  A.e * A.f

/-- The local Cartan bit is an involution. -/
theorem h_sq :
    A.h * A.h = 1 := by
  calc
    A.h * A.h
        = (A.e * A.f) * (A.e * A.f) := by
            rfl
    _ = A.e * (A.f * A.e) * A.f := by
            noncomm_ring
    _ = A.e * (-(A.e * A.f)) * A.f := by
            rw [A.anticomm]
            simp
    _ = -(A.e * (A.e * A.f)) * A.f := by
            rw [mul_neg]
    _ = -((A.e * A.e) * A.f) * A.f := by
            rw [mul_assoc]
    _ = -((1 : Op) * A.f) * A.f := by
            rw [A.e_sq]
    _ = (-A.f) * A.f := by
            rw [one_mul]
    _ = -(A.f * A.f) := by
            rw [neg_mul]
    _ = -(-1 : Op) := by
            rw [A.f_sq]
    _ = 1 := by
            simp

end SplitCliffordAtom

end InfoGeometry.OperatorAlgebra.SplitCliffordZ2Four
