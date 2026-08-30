import InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge

/-!
# Coxeter unit and inner action in the ternary Toeplitz--Cuntz carrier

This owner packages `c = β₂ β₁` and its generic ring automorphism.  It does
not claim a complex star-algebra equivalence without an additional algebra
structure.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterInnerAction

open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open ToeplitzCuntzThreeGenerators

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

def coxeterUnit : Aˣ where
  val := coxeterElement g
  inv := coxeterElement g * coxeterElement g
  val_inv := by simpa [mul_assoc] using coxeterElement_cube g
  inv_val := by simpa [mul_assoc] using coxeterElement_cube g

@[simp] theorem coxeterUnit_val :
    (coxeterUnit g : A) = coxeterElement g := rfl

@[simp] theorem coxeterUnit_inv :
    (coxeterUnit g).inv = coxeterElement g * coxeterElement g := rfl

def coxeterInnerAction (g : ToeplitzCuntzThreeGenerators A) (a : A) : A :=
  coxeterElement g * a * (↑((coxeterUnit g)⁻¹) : A)

@[simp] theorem coxeterInnerAction_one :
    coxeterInnerAction g 1 = 1 := by
  simp [coxeterInnerAction]

theorem coxeterInnerAction_mul (a b : A) :
    coxeterInnerAction g (a * b) =
      coxeterInnerAction g a * coxeterInnerAction g b := by
  have h : (↑((coxeterUnit g)⁻¹) : A) * coxeterElement g = 1 :=
    (coxeterUnit g).inv_val
  dsimp [coxeterInnerAction]
  calc
    coxeterElement g * (a * b) * (↑((coxeterUnit g)⁻¹) : A) =
        coxeterElement g * a *
            ((↑((coxeterUnit g)⁻¹) : A) * coxeterElement g) * b *
              (↑((coxeterUnit g)⁻¹) : A) := by rw [h]; noncomm_ring
    _ = (coxeterElement g * a * (↑((coxeterUnit g)⁻¹) : A)) *
        (coxeterElement g * b * (↑((coxeterUnit g)⁻¹) : A)) := by noncomm_ring

theorem coxeterInnerAction_add (a b : A) :
    coxeterInnerAction g (a + b) =
      coxeterInnerAction g a + coxeterInnerAction g b := by
  simp [coxeterInnerAction, add_mul, mul_add]

def coxeterInnerRingEquiv : A ≃+* A where
  toFun := coxeterInnerAction g
  invFun := fun a => (↑((coxeterUnit g)⁻¹) : A) * a * coxeterElement g
  left_inv := by
    intro a
    have h : (↑((coxeterUnit g)⁻¹) : A) * coxeterElement g = 1 :=
      (coxeterUnit g).inv_val
    dsimp [coxeterInnerAction]
    calc
      (↑((coxeterUnit g)⁻¹) : A) *
          (coxeterElement g * a * (coxeterUnit g).inv) * coxeterElement g =
        ((↑((coxeterUnit g)⁻¹) : A) * coxeterElement g) * a *
          ((↑((coxeterUnit g)⁻¹) : A) * coxeterElement g) := by noncomm_ring
      _ = a := by simpa [h]
  right_inv := by
    intro a
    have h : coxeterElement g * (↑((coxeterUnit g)⁻¹) : A) = 1 :=
      (coxeterUnit g).val_inv
    dsimp [coxeterInnerAction]
    calc
      coxeterElement g *
          ((coxeterUnit g).inv * a * coxeterElement g) *
            (↑((coxeterUnit g)⁻¹) : A) =
        (coxeterElement g * (↑((coxeterUnit g)⁻¹) : A)) * a *
          (coxeterElement g * (↑((coxeterUnit g)⁻¹) : A)) := by noncomm_ring
      _ = a := by simpa [h]
  map_mul' := coxeterInnerAction_mul g
  map_add' := coxeterInnerAction_add g

@[simp] theorem coxeterInnerRingEquiv_apply (a : A) :
    coxeterInnerRingEquiv g a = coxeterInnerAction g a := rfl


end InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterInnerAction
