import proofs.OctonionMatrixEncodings
import proofs.SplitOctonionNilpotent

/-!
# Octonion matrix obstruction and Zorn flow

This integrates the external obstruction/flow file into the active Zorn
split-octonion model.  Ordinary associative matrices cannot faithfully preserve
nonassociative multiplication; Zorn vector matrices provide the repaired
matrix-shaped construction.
-/

noncomputable section

namespace OctonionMatrixObstruction

/-- A faithful multiplicative representation into an associative target forces associativity. -/
theorem no_faithful_assoc_rep_of_nonassoc
    {A M : Type} [Mul A] [Semigroup M]
    (f : A → M) (h_hom : ∀ x y : A, f (x * y) = f x * f y)
    (h_faithful : Function.Injective f) :
    ∀ x y z : A, (x * y) * z = x * (y * z) := by
  intro x y z
  apply h_faithful
  calc
    f ((x * y) * z) = f (x * y) * f z := h_hom (x * y) z
    _ = (f x * f y) * f z := by rw [h_hom x y]
    _ = f x * (f y * f z) := by rw [mul_assoc]
    _ = f x * f (y * z) := by rw [h_hom y z]
    _ = f (x * (y * z)) := by rw [h_hom x (y * z)]

abbrev ZornMatrix := OctonionMatrixEncodings.Zorn
abbrev Vec3 := OctonionMatrixEncodings.Vec3

def zornMul : ZornMatrix → ZornMatrix → ZornMatrix := OctonionMatrixEncodings.zornMul

def ZornMatrix.zero : ZornMatrix := SplitOctonionNilpotent.ZornMatrix.zero

/-- Scaling element in the active integer Zorn model. -/
def scaleFlow (e eInv : ℤ) : ZornMatrix where
  a := e
  u := fun _ => 0
  v := fun _ => 0
  b := eInv

/-- Integer-coordinate version of the external Zorn scaling calculation. -/
theorem zorn_scaling_flow (X : ZornMatrix) (e eInv : ℤ) (hInv : e * eInv = 1) :
    zornMul (zornMul (scaleFlow e eInv) X) (scaleFlow eInv e) =
    { a := X.a, b := X.b, u := fun i => e ^ 2 * X.u i, v := fun i => eInv ^ 2 * X.v i } := by
  apply OctonionMatrixEncodings.zorn_ext
  · simp [zornMul, scaleFlow, OctonionMatrixEncodings.zornMul,
      OctonionMatrixEncodings.dot3]
    calc
      e * X.a * eInv = X.a * (e * eInv) := by ring
      _ = X.a := by rw [hInv]; ring
  · funext i
    fin_cases i <;> simp [zornMul, scaleFlow, OctonionMatrixEncodings.zornMul,
      OctonionMatrixEncodings.dot3, OctonionMatrixEncodings.cross3] <;> ring
  · funext i
    fin_cases i <;> simp [zornMul, scaleFlow, OctonionMatrixEncodings.zornMul,
      OctonionMatrixEncodings.dot3, OctonionMatrixEncodings.cross3] <;> ring
  · simp [zornMul, scaleFlow, OctonionMatrixEncodings.zornMul,
      OctonionMatrixEncodings.dot3]
    calc
      eInv * X.b * e = X.b * (e * eInv) := by ring
      _ = X.b := by rw [hInv]; ring

/-- The active Zorn construction gives a concrete nonassociativity inequality. -/
theorem zorn_nonassociative_ne :
    zornMul (zornMul OctonionMatrixEncodings.Zx OctonionMatrixEncodings.Zy)
        OctonionMatrixEncodings.Zz ≠
      zornMul OctonionMatrixEncodings.Zx
        (zornMul OctonionMatrixEncodings.Zy OctonionMatrixEncodings.Zz) :=
  OctonionMatrixEncodings.zorn_nonassociative

/-- The external nilpotent-attractor idea is the checked Zorn zero mode. -/
theorem zorn_nilpotent_protection :
    SplitOctonionNilpotent.zornMul SplitOctonionNilpotent.Z_mode SplitOctonionNilpotent.Z_mode =
      SplitOctonionNilpotent.ZornMatrix.zero :=
  SplitOctonionNilpotent.Z_mode_nilpotent

#check no_faithful_assoc_rep_of_nonassoc
#check zorn_scaling_flow
#check zorn_nonassociative_ne
#check zorn_nilpotent_protection

end OctonionMatrixObstruction
