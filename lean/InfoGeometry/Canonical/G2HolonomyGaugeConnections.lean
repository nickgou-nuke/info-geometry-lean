import InfoGeometry.Canonical.SplitG2StructureOnImaginaryOctonions
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Discrete split-`G₂` gauge connections on the imaginary split-octonion carrier

This file stays on the already verified split-`G₂` owner:

* the carrier is `imaginarySplitOctonion`;
* the preserved trilinear property is `canonicalSplitG2ThreeFormValue`;
* an automorphism is a linear equivalence preserving that property.

It packages finite edge-labelled transport and triangle curvature as
compositions of those automorphisms.  It does not claim a smooth holonomy
theorem, a Ricci-flatness theorem, or any analytic gauge completion.
-/

namespace InfoGeometry.Canonical

open scoped BigOperators

/-- A split-`G₂` automorphism on the imaginary split-octonion carrier. -/
structure SplitG2Automorphism where
  toLinearEquiv : imaginarySplitOctonion ≃ₗ[ℚ] imaginarySplitOctonion
  preservesThreeForm :
    ∀ x y z : imaginarySplitOctonion,
      canonicalSplitG2ThreeFormValue (toLinearEquiv x)
        (toLinearEquiv y) (toLinearEquiv z) =
      canonicalSplitG2ThreeFormValue x y z

namespace SplitG2Automorphism

instance : CoeFun SplitG2Automorphism
    (fun _ => imaginarySplitOctonion → imaginarySplitOctonion) :=
  ⟨fun φ => φ.toLinearEquiv⟩

@[simp] theorem apply_eq (φ : SplitG2Automorphism) (x : imaginarySplitOctonion) :
    φ x = φ.toLinearEquiv x :=
  rfl

@[simp] theorem map_threeForm (φ : SplitG2Automorphism)
    (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue (φ x) (φ y) (φ z) =
      canonicalSplitG2ThreeFormValue x y z :=
  φ.preservesThreeForm x y z

/-- The identity split-`G₂` automorphism. -/
def id : SplitG2Automorphism where
  toLinearEquiv := LinearEquiv.refl ℚ imaginarySplitOctonion
  preservesThreeForm := by
    intro x y z
    rfl

/-- Composition of split-`G₂` automorphisms. -/
def comp (φ ψ : SplitG2Automorphism) : SplitG2Automorphism where
  toLinearEquiv := ψ.toLinearEquiv.trans φ.toLinearEquiv
  preservesThreeForm := by
    intro x y z
    change canonicalSplitG2ThreeFormValue (φ (ψ x)) (φ (ψ y)) (φ (ψ z)) =
      canonicalSplitG2ThreeFormValue x y z
    calc
      canonicalSplitG2ThreeFormValue (φ (ψ x)) (φ (ψ y)) (φ (ψ z)) =
          canonicalSplitG2ThreeFormValue (ψ x) (ψ y) (ψ z) :=
        φ.preservesThreeForm (ψ x) (ψ y) (ψ z)
      _ = canonicalSplitG2ThreeFormValue x y z :=
        ψ.preservesThreeForm x y z

@[simp] theorem id_apply (x : imaginarySplitOctonion) :
    SplitG2Automorphism.id x = x := rfl

@[simp] theorem comp_apply (φ ψ : SplitG2Automorphism) (x : imaginarySplitOctonion) :
    SplitG2Automorphism.comp φ ψ x = φ (ψ x) := by
  change φ (ψ x) = φ (ψ x)
  rfl

end SplitG2Automorphism

/-- A discrete split-`G₂` gauge connection indexed by edges. -/
abbrev SplitG2GaugeConnection (E : Type*) := E → SplitG2Automorphism

namespace SplitG2GaugeConnection

abbrev edgeToG2 {E : Type*} (A : SplitG2GaugeConnection E) :
    E → SplitG2Automorphism := A

end SplitG2GaugeConnection

/-- Parallel transport along a finite path. -/
def parallelTransport {E : Type*} (A : SplitG2GaugeConnection E)
    : List E → SplitG2Automorphism :=
  List.foldr (fun e acc => SplitG2Automorphism.comp (A.edgeToG2 e) acc)
    SplitG2Automorphism.id

@[simp] theorem parallelTransport_nil {E : Type*} (A : SplitG2GaugeConnection E) :
    parallelTransport A [] = SplitG2Automorphism.id := rfl

@[simp] theorem parallelTransport_cons {E : Type*} (A : SplitG2GaugeConnection E)
    (e : E) (path : List E) :
    parallelTransport A (e :: path) =
      SplitG2Automorphism.comp (A.edgeToG2 e) (parallelTransport A path) := rfl

theorem parallelTransport_preserves_threeForm
    {E : Type*} (A : SplitG2GaugeConnection E) (path : List E)
    (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue
        (parallelTransport A path x)
        (parallelTransport A path y)
        (parallelTransport A path z) =
      canonicalSplitG2ThreeFormValue x y z := by
  induction path with
  | nil => rfl
  | cons e path ih =>
      calc
        canonicalSplitG2ThreeFormValue
            (parallelTransport A (e :: path) x)
            (parallelTransport A (e :: path) y)
            (parallelTransport A (e :: path) z) =
            canonicalSplitG2ThreeFormValue
              ((A.edgeToG2 e) (parallelTransport A path x))
              ((A.edgeToG2 e) (parallelTransport A path y))
              ((A.edgeToG2 e) (parallelTransport A path z)) := by
                simp [parallelTransport_cons, SplitG2Automorphism.comp_apply]
        _ = canonicalSplitG2ThreeFormValue
              (parallelTransport A path x)
              (parallelTransport A path y)
              (parallelTransport A path z) :=
          (A.edgeToG2 e).preservesThreeForm
            (parallelTransport A path x)
            (parallelTransport A path y)
            (parallelTransport A path z)
        _ = canonicalSplitG2ThreeFormValue x y z := ih

/-- Triangle curvature as the holonomy around a 3-cycle. -/
def curvature {E : Type*} (A : SplitG2GaugeConnection E)
    (e₁ e₂ e₃ : E) : SplitG2Automorphism :=
  SplitG2Automorphism.comp (SplitG2Automorphism.comp (A.edgeToG2 e₁) (A.edgeToG2 e₂))
    (A.edgeToG2 e₃)

@[simp] theorem curvature_eq
    {E : Type*} (A : SplitG2GaugeConnection E)
    (e₁ e₂ e₃ : E) :
    curvature A e₁ e₂ e₃ =
      SplitG2Automorphism.comp (SplitG2Automorphism.comp (A.edgeToG2 e₁) (A.edgeToG2 e₂))
        (A.edgeToG2 e₃) := rfl

theorem curvature_preserves_threeForm
    {E : Type*} (A : SplitG2GaugeConnection E)
    (e₁ e₂ e₃ : E) (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue
        (curvature A e₁ e₂ e₃ x)
        (curvature A e₁ e₂ e₃ y)
        (curvature A e₁ e₂ e₃ z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact (curvature A e₁ e₂ e₃).preservesThreeForm x y z

end Canonical
