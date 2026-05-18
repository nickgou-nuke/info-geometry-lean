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
    ext
    · simpa [Bracket.bracket] using (lie_add x.1 y.1 z.1)
    · simpa [Bracket.bracket] using (lie_add x.2 y.2 z.2)
  add_lie := by
    intro x y z
    ext
    · simpa [Bracket.bracket] using (add_lie x.1 y.1 z.1)
    · simpa [Bracket.bracket] using (add_lie x.2 y.2 z.2)
  lie_self := by
    intro x
    ext
    · simpa [Bracket.bracket] using (lie_self x.1)
    · simpa [Bracket.bracket] using (lie_self x.2)
  leibniz_lie := by
    intro x y z
    ext
    · simpa [Bracket.bracket] using (leibniz_lie x.1 y.1 z.1)
    · simpa [Bracket.bracket] using (leibniz_lie x.2 y.2 z.2)

/-- Componentwise Lie algebra structure over `𝕜`. -/
noncomputable instance : LieAlgebra 𝕜 (ChiralVirasoro 𝕜) where
  lie_smul := by
    intro a x y
    ext
    · simpa [Bracket.bracket] using (lie_smul a x.1 y.1)
    · simpa [Bracket.bracket] using (lie_smul a x.2 y.2)

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
  ext
  · rfl
  · simp [inLeft, Bracket.bracket]

/-- Right-sector brackets are computed in the right component. -/
@[simp] theorem inRight_bracket (X Y : VirasoroAlgebra 𝕜) :
    ⁅inRight X, inRight Y⁆ = inRight ⁅X, Y⁆ := by
  ext
  · simp [inRight, Bracket.bracket]
  · rfl

/-- Cross brackets vanish between the left and right sectors. -/
@[simp] theorem inLeft_bracket_inRight (X Y : VirasoroAlgebra 𝕜) :
    ⁅inLeft X, inRight Y⁆ = 0 := by
  have h1 : ⁅X, (0 : VirasoroAlgebra 𝕜)⁆ = 0 := by
    simp
  have h2 : ⁅(0 : VirasoroAlgebra 𝕜), Y⁆ = 0 := by
    simp
  ext
  · simpa [inLeft, inRight, Bracket.bracket] using h1
  · simpa [inLeft, inRight, Bracket.bracket] using h2

/-- Cross brackets vanish between the right and left sectors. -/
@[simp] theorem inRight_bracket_inLeft (X Y : VirasoroAlgebra 𝕜) :
    ⁅inRight X, inLeft Y⁆ = 0 := by
  have h1 : ⁅(0 : VirasoroAlgebra 𝕜), X⁆ = 0 := by
    simp
  have h2 : ⁅Y, (0 : VirasoroAlgebra 𝕜)⁆ = 0 := by
    simp
  ext
  · simpa [inLeft, inRight, Bracket.bracket] using h1
  · simpa [inLeft, inRight, Bracket.bracket] using h2

/-- The left sector `L_n` bracket is inherited from the Virasoro algebra. -/
@[simp] theorem lgenLeft_bracket (n m : ℤ) :
    ⁅lgenLeft (𝕜 := 𝕜) n, lgenLeft (𝕜 := 𝕜) m⁆ =
      inLeft (⁅VirasoroAlgebra.lgen 𝕜 n, VirasoroAlgebra.lgen 𝕜 m⁆) := by
  simpa [lgenLeft, inLeft] using
    congrArg (fun X : VirasoroAlgebra 𝕜 => (X, (0 : VirasoroAlgebra 𝕜)))
      (VirasoroAlgebra.lgen_bracket 𝕜 n m)

/-- The right sector `L_n` bracket is inherited from the Virasoro algebra. -/
@[simp] theorem lgenRight_bracket (n m : ℤ) :
    ⁅lgenRight (𝕜 := 𝕜) n, lgenRight (𝕜 := 𝕜) m⁆ =
      inRight (⁅VirasoroAlgebra.lgen 𝕜 n, VirasoroAlgebra.lgen 𝕜 m⁆) := by
  simpa [lgenRight, inRight] using
    congrArg (fun X : VirasoroAlgebra 𝕜 => ((0 : VirasoroAlgebra 𝕜), X))
      (VirasoroAlgebra.lgen_bracket 𝕜 n m)

/-- The left and right central elements commute with everything in the product. -/
@[simp] theorem cgenLeft_bracket (X : ChiralVirasoro 𝕜) :
    ⁅cgenLeft (𝕜 := 𝕜), X⁆ = 0 := by
  ext
  · simpa [cgenLeft, inLeft, Bracket.bracket] using
      (VirasoroAlgebra.cgen_bracket (𝕜 := 𝕜) X.1)
  · simpa [cgenLeft, inLeft, Bracket.bracket] using (zero_lie X.2)

/-- The right and left central elements commute with everything in the product. -/
@[simp] theorem cgenRight_bracket (X : ChiralVirasoro 𝕜) :
    ⁅cgenRight (𝕜 := 𝕜), X⁆ = 0 := by
  ext
  · simpa [cgenRight, inRight, Bracket.bracket] using (zero_lie X.1)
  · simpa [cgenRight, inRight, Bracket.bracket] using
      (VirasoroAlgebra.cgen_bracket (𝕜 := 𝕜) X.2)

/-- The two central elements commute with each other. -/
@[simp] theorem cgenLeft_bracket_cgenRight :
    ⁅cgenLeft (𝕜 := 𝕜), cgenRight (𝕜 := 𝕜)⁆ = 0 := by
  ext
  · simpa [cgenLeft, cgenRight, inLeft, inRight, Bracket.bracket] using
      (VirasoroAlgebra.cgen_bracket (𝕜 := 𝕜) (VirasoroAlgebra.cgen 𝕜))
  · simpa [cgenLeft, cgenRight, inLeft, inRight, Bracket.bracket] using
      (zero_lie (VirasoroAlgebra.cgen 𝕜))

/-- Chiral central charge bookkeeping. -/
structure CentralCharge where
  left : 𝕜
  right : 𝕜

namespace CentralCharge

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

/-- Left projector onto the left Virasoro sector. -/
noncomputable def projectLeft (X : ChiralVirasoro 𝕜) : ChiralVirasoro 𝕜 :=
  inLeft X.1

/-- Right projector onto the right Virasoro sector. -/
noncomputable def projectRight (X : ChiralVirasoro 𝕜) : ChiralVirasoro 𝕜 :=
  inRight X.2

@[simp] theorem projectLeft_fst (X : ChiralVirasoro 𝕜) :
    (projectLeft (𝕜 := 𝕜) X).1 = X.1 := by
  rfl

@[simp] theorem projectLeft_snd (X : ChiralVirasoro 𝕜) :
    (projectLeft (𝕜 := 𝕜) X).2 = 0 := by
  rfl

@[simp] theorem projectRight_fst (X : ChiralVirasoro 𝕜) :
    (projectRight (𝕜 := 𝕜) X).1 = 0 := by
  rfl

@[simp] theorem projectRight_snd (X : ChiralVirasoro 𝕜) :
    (projectRight (𝕜 := 𝕜) X).2 = X.2 := by
  rfl

@[simp] theorem projectLeft_idempotent (X : ChiralVirasoro 𝕜) :
    projectLeft (𝕜 := 𝕜) (projectLeft X) = projectLeft X := by
  ext <;> rfl

@[simp] theorem projectRight_idempotent (X : ChiralVirasoro 𝕜) :
    projectRight (𝕜 := 𝕜) (projectRight X) = projectRight X := by
  ext <;> rfl

@[simp] theorem projectLeft_projectRight_zero (X : ChiralVirasoro 𝕜) :
    projectLeft (𝕜 := 𝕜) (projectRight X) = 0 := by
  ext <;> rfl

@[simp] theorem projectRight_projectLeft_zero (X : ChiralVirasoro 𝕜) :
    projectRight (𝕜 := 𝕜) (projectLeft X) = 0 := by
  ext <;> rfl

@[simp] theorem projectLeft_add_projectRight (X : ChiralVirasoro 𝕜) :
    projectLeft (𝕜 := 𝕜) X + projectRight X = X := by
  ext <;> simp [projectLeft, projectRight, inLeft, inRight]

@[simp] theorem projectLeft_bracket (X Y : ChiralVirasoro 𝕜) :
    projectLeft (𝕜 := 𝕜) ⁅X, Y⁆ = ⁅projectLeft X, projectLeft Y⁆ := by
  rfl

@[simp] theorem projectRight_bracket (X Y : ChiralVirasoro 𝕜) :
    projectRight (𝕜 := 𝕜) ⁅X, Y⁆ = ⁅projectRight X, projectRight Y⁆ := by
  rfl

end ChiralVirasoro

end VirasoroProject
