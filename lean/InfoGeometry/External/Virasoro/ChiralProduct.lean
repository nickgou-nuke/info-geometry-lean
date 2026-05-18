/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import InfoGeometry.External.Virasoro.VirasoroAlgebra

/-!
# Chiral product of the Virasoro algebra

This file does not rebuild the Virasoro algebra. It uses the formalized
`VirasoroProject.VirasoroAlgebra` from the vendored Kytölä development and
packages two copies into the direct product

`VirasoroAlgebra 𝕜 × VirasoroAlgebra 𝕜`.

The intention is the clean chiral split

`vir_chiral = vir_+ ⊕ vir_-`

as a finite direct product, together with sector injections and componentwise
bracket lemmas.
-/

namespace VirasoroProject

universe u

variable (𝕜 : Type u) [Field 𝕜] [CharZero 𝕜]

/-- The chiral Virasoro algebra as a direct product of two Virasoro algebras. -/
abbrev ChiralVirasoro : Type u :=
  VirasoroAlgebra 𝕜 × VirasoroAlgebra 𝕜

namespace ChiralVirasoro

variable {𝕜}

/-- Componentwise bracket on the chiral product. -/
noncomputable instance : Bracket (ChiralVirasoro 𝕜) (ChiralVirasoro 𝕜) where
  bracket X Y := (⁅X.1, Y.1⁆, ⁅X.2, Y.2⁆)

/-- Componentwise Lie ring structure on the chiral product. -/
noncomputable instance : LieRing (ChiralVirasoro 𝕜) where
  lie_add := by
    intro x y z
    ext <;> simp [Bracket.bracket]
  add_lie := by
    intro x y z
    ext <;> simp [Bracket.bracket]
  lie_self := by
    intro x
    ext <;> simp [Bracket.bracket]
  leibniz_lie := by
    intro x y z
    ext <;> simp [Bracket.bracket, leibniz_lie]

/-- Componentwise Lie algebra structure over `𝕜`. -/
noncomputable instance : LieAlgebra 𝕜 (ChiralVirasoro 𝕜) where
  lie_smul := by
    intro a x y
    ext <;> simp [Bracket.bracket, lie_smul]

/-- Left-sector inclusion. -/
noncomputable def inLeft (X : VirasoroAlgebra 𝕜) : ChiralVirasoro 𝕜 :=
  (X, 0)

/-- Right-sector inclusion. -/
noncomputable def inRight (X : VirasoroAlgebra 𝕜) : ChiralVirasoro 𝕜 :=
  (0, X)

/-- The left Virasoro generator in the chiral product. -/
noncomputable def lgenLeft (n : ℤ) : ChiralVirasoro 𝕜 :=
  inLeft (VirasoroAlgebra.lgen 𝕜 n)

/-- The right Virasoro generator in the chiral product. -/
noncomputable def lgenRight (n : ℤ) : ChiralVirasoro 𝕜 :=
  inRight (VirasoroAlgebra.lgen 𝕜 n)

/-- The left central element in the chiral product. -/
noncomputable def cgenLeft : ChiralVirasoro 𝕜 :=
  inLeft (VirasoroAlgebra.cgen 𝕜)

/-- The right central element in the chiral product. -/
noncomputable def cgenRight : ChiralVirasoro 𝕜 :=
  inRight (VirasoroAlgebra.cgen 𝕜)

/-- Componentwise bracket on the chiral product. -/
@[simp] theorem bracket_def (X Y : ChiralVirasoro 𝕜) :
    ⁅X, Y⁆ = (⁅X.1, Y.1⁆, ⁅X.2, Y.2⁆) := by
  rfl

/-- Left-sector brackets are computed in the left component. -/
@[simp] theorem inLeft_bracket (X Y : VirasoroAlgebra 𝕜) :
    ⁅inLeft X, inLeft Y⁆ = inLeft ⁅X, Y⁆ := by
  ext <;> simp [inLeft]

/-- Right-sector brackets are computed in the right component. -/
@[simp] theorem inRight_bracket (X Y : VirasoroAlgebra 𝕜) :
    ⁅inRight X, inRight Y⁆ = inRight ⁅X, Y⁆ := by
  ext <;> simp [inRight]

/-- Cross brackets vanish between the left and right sectors. -/
@[simp] theorem inLeft_bracket_inRight (X Y : VirasoroAlgebra 𝕜) :
    ⁅inLeft X, inRight Y⁆ = 0 := by
  ext <;> simp [inLeft, inRight]

/-- Cross brackets vanish between the right and left sectors. -/
@[simp] theorem inRight_bracket_inLeft (X Y : VirasoroAlgebra 𝕜) :
    ⁅inRight X, inLeft Y⁆ = 0 := by
  ext <;> simp [inLeft, inRight]

/-- The left sector `L_n` bracket is inherited from the Virasoro algebra. -/
@[simp] theorem lgenLeft_bracket (n m : ℤ) :
    ⁅lgenLeft (𝕜 := 𝕜) n, lgenLeft (𝕜 := 𝕜) m⁆ =
      inLeft (⁅VirasoroAlgebra.lgen 𝕜 n, VirasoroAlgebra.lgen 𝕜 m⁆) := by
  rfl

/-- The right sector `L_n` bracket is inherited from the Virasoro algebra. -/
@[simp] theorem lgenRight_bracket (n m : ℤ) :
    ⁅lgenRight (𝕜 := 𝕜) n, lgenRight (𝕜 := 𝕜) m⁆ =
      inRight (⁅VirasoroAlgebra.lgen 𝕜 n, VirasoroAlgebra.lgen 𝕜 m⁆) := by
  rfl

/-- The left and right central elements commute with everything in the product. -/
@[simp] theorem cgenLeft_bracket (X : ChiralVirasoro 𝕜) :
    ⁅cgenLeft (𝕜 := 𝕜), X⁆ = 0 := by
  ext <;> simp [cgenLeft]

/-- The right and left central elements commute with everything in the product. -/
@[simp] theorem cgenRight_bracket (X : ChiralVirasoro 𝕜) :
    ⁅cgenRight (𝕜 := 𝕜), X⁆ = 0 := by
  ext <;> simp [cgenRight]

/-- The two central elements commute with each other. -/
@[simp] theorem cgenLeft_bracket_cgenRight :
    ⁅cgenLeft (𝕜 := 𝕜), cgenRight (𝕜 := 𝕜)⁆ = 0 := by
  simp

/-- Chiral central charge bookkeeping. -/
structure CentralCharge where
  left : 𝕜
  right : 𝕜

namespace CentralCharge

variable {𝕜}

/-- Total central charge. -/
def total (c : CentralCharge (𝕜 := 𝕜)) : 𝕜 :=
  c.left + c.right

/-- Chiral imbalance of central charges. -/
def imbalance (c : CentralCharge (𝕜 := 𝕜)) : 𝕜 :=
  c.left - c.right

@[simp] theorem total_mk (cL cR : 𝕜) :
    total (𝕜 := 𝕜) ⟨cL, cR⟩ = cL + cR := rfl

@[simp] theorem imbalance_mk (cL cR : 𝕜) :
    imbalance (𝕜 := 𝕜) ⟨cL, cR⟩ = cL - cR := rfl

end CentralCharge

end ChiralVirasoro

end VirasoroProject
