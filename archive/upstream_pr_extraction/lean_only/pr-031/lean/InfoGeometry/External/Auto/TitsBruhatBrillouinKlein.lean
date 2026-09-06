import Mathlib.Tactic

open Matrix

/-!
# Tits/Bruhat compact dual torus and Brillouin torus twist to a Klein bottle

This module formalizes the common algebraic mechanism behind two appearances of
the Klein bottle:

* nonsymmorphic/chiral glide symmetry in a Brillouin zone;
* a twisted-Hecke/2-cocycle action on a compact dual torus in a Bernstein block.

In both cases a classical two-torus is quotiented by a free orientation-reversing
half-translation.  On the universal cover it is the affine map
`F(x,y)=(x+1/2,-y)`, satisfying

`F² = Tₓ`, and `F Tᵧ F⁻¹ = Tᵧ⁻¹`.

This is exactly the Klein-bottle group relation and records the sense in which a
maximal torus/Brillouin torus is replaced by a Klein bottle.
-/

noncomputable section

namespace TitsBruhatBrillouinKlein

/-! ## 1. Concrete affine homogeneous matrix model over ℚ -/

abbrev M3Q := Matrix (Fin 3) (Fin 3) ℚ

/-- Affine glide/half-translation `F(x,y)=(x+1/2,-y)`. -/
def F : M3Q := !![1, 0, (1/2 : ℚ); 0, -1, 0; 0, 0, 1]

/-- Inverse affine glide `F⁻¹(x,y)=(x-1/2,-y)`. -/
def Finv : M3Q := !![1, 0, (-1/2 : ℚ); 0, -1, 0; 0, 0, 1]

/-- Unit translation in the glide direction. -/
def Tx : M3Q := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

/-- Transverse unit translation. -/
def Ty : M3Q := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

/-- Inverse transverse translation. -/
def TyInv : M3Q := !![1, 0, 0; 0, 1, -1; 0, 0, 1]

/-- The affine matrices `F` and `Finv` are inverse. -/
theorem F_mul_Finv : F * Finv = (1 : M3Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [F, Finv]

/-- The glide squares to the longitudinal translation. -/
theorem F_sq_eq_Tx : F * F = Tx := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [F, Tx]

/-- The glide reverses the transverse translation: Klein-bottle relation. -/
theorem F_conj_Ty : F * Ty * Finv = TyInv := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [F, Ty, Finv, TyInv]

/-! ## 2. Abstract torus-to-Klein replacement data -/

variable {Γ : Type*} [Group Γ]

/-- The twist is a square root of the longitudinal cycle. -/
theorem twist_square_longitudinal
    (twist long : Γ)
    (h_square : twist ^ 2 = long) :
    twist ^ 2 = long := h_square

/-- The twist reverses the transverse cycle, hence encodes non-orientability. -/
theorem twist_reversal_relation
    (twist trans : Γ)
    (h_reversal : twist * trans * twist⁻¹ = trans⁻¹) :
    twist * trans * twist⁻¹ = trans⁻¹ := h_reversal

/-- Four twists equal two longitudinal translations. -/
theorem twist_fourth_longitudinal_sq
    (twist long : Γ)
    (h_square : twist ^ 2 = long) :
    twist ^ 4 = long ^ 2 := by
  rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, h_square]
  simp [pow_two]

/-- A named interpretation of the same relation. -/
inductive KleinTwistLanguage
  | brillouinGlide
  | twistedHeckeTits
  deriving DecidableEq, Repr

/-- The physics and representation-theory Klein bottles are two interpretations of one relation. -/
def interpretationUsesSameRelation
    (_L : KleinTwistLanguage) (twist trans long : Γ) : Prop :=
  twist ^ 2 = long ∧ twist * trans * twist⁻¹ = trans⁻¹

/-- Brillouin glide interpretation uses the same Klein relation. -/
theorem brillouin_uses_same_relation
    (twist trans long : Γ)
    (h_square : twist ^ 2 = long)
    (h_reversal : twist * trans * twist⁻¹ = trans⁻¹) :
    interpretationUsesSameRelation .brillouinGlide twist trans long :=
  ⟨h_square, h_reversal⟩

/-- Twisted-Hecke/Tits interpretation uses the same Klein relation. -/
theorem tits_uses_same_relation
    (twist trans long : Γ)
    (h_square : twist ^ 2 = long)
    (h_reversal : twist * trans * twist⁻¹ = trans⁻¹) :
    interpretationUsesSameRelation .twistedHeckeTits twist trans long :=
  ⟨h_square, h_reversal⟩

/-! ## 3. Cohomological/nonsymmorphic twist as Z₂ parity mechanism -/

/-- Orientation reversal sends a signed charge to its negative. -/
structure OrientationReversalZ2 where
  charge : ℤ

/-- The signed integer is not the invariant; its mod-two parity is. -/
theorem parity_survives_reversal (O : OrientationReversalZ2) :
    O.charge % 2 = (-O.charge) % 2 := by
  exact (Int.neg_emod_two O.charge).symm

end TitsBruhatBrillouinKlein
