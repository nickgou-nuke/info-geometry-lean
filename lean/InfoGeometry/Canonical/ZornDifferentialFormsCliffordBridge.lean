import InfoGeometry.Canonical.ZornFiniteVectorCalculus
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic

/-!
# Differential forms, Hodge operator, and Clifford morphism

This is a generic finite bridge.  Forms are represented by an exterior
algebra, the Hodge operator and differential are linear maps on that carrier,
and a Clifford representation is produced by Mathlib's universal `lift` from
an explicit generator square law.  No identification of the Zorn product
with an associative Clifford target is made.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge

variable {R V C : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [Semiring C] [Algebra R C]

structure FormHodgeCliffordData where
  Q : QuadraticForm R V
  differential : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V
  differential_sq : differential.comp differential = 0
  hodgeStar : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V
  hodgeSquareSign : R
  hodgeStar_sq : hodgeStar.comp hodgeStar = hodgeSquareSign • LinearMap.id
  generator : V →ₗ[R] C
  generator_sq : ∀ v, generator v * generator v = algebraMap R C (Q v)

def hodgeDirac (D : FormHodgeCliffordData (R := R) (V := V) (C := C)) :
    ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  D.differential +
    LinearMap.comp D.hodgeStar (LinearMap.comp D.differential D.hodgeStar)

@[simp] theorem hodgeDirac_apply
    (D : FormHodgeCliffordData (R := R) (V := V) (C := C))
    (ω : ExteriorAlgebra R V) :
    hodgeDirac D ω =
      D.differential ω + D.hodgeStar (D.differential (D.hodgeStar ω)) := by
  rfl

theorem differential_square_apply
    (D : FormHodgeCliffordData (R := R) (V := V) (C := C))
    (ω : ExteriorAlgebra R V) :
    D.differential (D.differential ω) = 0 := by
  have h := congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V => f ω)
    D.differential_sq
  simpa [LinearMap.comp_apply] using h

theorem hodgeStar_square_apply
    (D : FormHodgeCliffordData (R := R) (V := V) (C := C))
    (ω : ExteriorAlgebra R V) :
    D.hodgeStar (D.hodgeStar ω) = D.hodgeSquareSign • ω := by
  have h := congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V => f ω)
    D.hodgeStar_sq
  simpa [LinearMap.comp_apply] using h

theorem hodgeStar_involutive
    (D : FormHodgeCliffordData (R := R) (V := V) (C := C))
    (hSign : D.hodgeSquareSign = 1) :
    D.hodgeStar.comp D.hodgeStar = LinearMap.id := by
  simpa [hSign] using D.hodgeStar_sq

def cliffordMorphism
    (D : FormHodgeCliffordData (R := R) (V := V) (C := C)) :
    CliffordAlgebra D.Q →ₐ[R] C :=
  CliffordAlgebra.lift D.Q ⟨D.generator, D.generator_sq⟩

@[simp] theorem cliffordMorphism_generator
    (D : FormHodgeCliffordData (R := R) (V := V) (C := C)) (v : V) :
    cliffordMorphism D (CliffordAlgebra.ι D.Q v) = D.generator v := by
  rw [cliffordMorphism, CliffordAlgebra.lift_ι_apply]

theorem cliffordMorphism_mul
    (D : FormHodgeCliffordData (R := R) (V := V) (C := C))
    (x y : CliffordAlgebra D.Q) :
    cliffordMorphism D (x * y) = cliffordMorphism D x * cliffordMorphism D y := by
  exact (cliffordMorphism D).map_mul x y

theorem cliffordMorphism_one
    (D : FormHodgeCliffordData (R := R) (V := V) (C := C)) :
    cliffordMorphism D 1 = 1 := by
  exact (cliffordMorphism D).map_one

theorem cliffordMorphism_generator_square
    (D : FormHodgeCliffordData (R := R) (V := V) (C := C)) (v : V) :
    cliffordMorphism D (CliffordAlgebra.ι D.Q v) *
        cliffordMorphism D (CliffordAlgebra.ι D.Q v) =
      algebraMap R C (D.Q v) := by
  rw [cliffordMorphism_generator]
  exact D.generator_sq v

theorem hodgeDirac_sq_expansion
    (D : FormHodgeCliffordData (R := R) (V := V) (C := C)) :
    hodgeDirac D = D.differential +
      LinearMap.comp D.hodgeStar (LinearMap.comp D.differential D.hodgeStar) := by
  rfl

end InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
