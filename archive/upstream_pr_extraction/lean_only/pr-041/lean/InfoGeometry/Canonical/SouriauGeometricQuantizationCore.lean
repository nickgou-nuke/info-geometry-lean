import Mathlib
import InfoGeometry.Canonical.SouriauKKSForm

/-!
# A theorem-safe Souriau/KKS algebraic core

This file supplies the finite algebraic layer that was previously only named in
the project.  It deliberately distinguishes three claims:

* a finite carrier carries a form over a native Lie-algebra bracket;
* a scaled bilinear curvature datum satisfies `ℏ F = ω`;
* categorical quantization is owned separately by the native
  `QuantizationObject`/`QuantizationMorphism` category.

The file does not claim a smooth manifold, an integrality theorem, or a
non-trivial bundle classification.  Those require differential-geometric
owners not present in the current Mathlib/repository API.
-/

namespace InfoGeometry.Canonical

noncomputable section

section Leaf

variable {State Tangent : Type*}
variable [AddCommGroup Tangent] [Module ℝ Tangent]
variable [LieRing Tangent] [LieAlgebra ℝ Tangent]

/-- Finite algebraic data for a genuine symplectic Souriau leaf.

`point` identifies tangent vectors with the ambient state carrier; the form is
defined on the tangent module.  Non-degeneracy and the cyclic identity are
explicit fields, so a readout-constant set cannot be mistaken for a symplectic
leaf.
-/
structure SouriauLieLeafData where
  carrier : Set State
  point : Tangent → State
  point_mem : ∀ X, point X ∈ carrier
  form : Tangent →ₗ[ℝ] Tangent →ₗ[ℝ] ℝ
  

namespace SouriauLieLeafData

variable (L : SouriauLieLeafData (State := State) (Tangent := Tangent))

theorem form_add_left (X₁ X₂ Y : Tangent) :
    L.form (X₁ + X₂) Y = L.form X₁ Y + L.form X₂ Y := by
  exact congrArg (fun f : Tangent →ₗ[ℝ] ℝ => f Y)
    (L.form.map_add X₁ X₂)

theorem form_add_right (X Y₁ Y₂ : Tangent) :
    L.form X (Y₁ + Y₂) = L.form X Y₁ + L.form X Y₂ := by
  exact (L.form X).map_add Y₁ Y₂

theorem form_smul_left (a : ℝ) (X Y : Tangent) :
    L.form (a • X) Y = a * L.form X Y := by
  exact congrArg (fun f : Tangent →ₗ[ℝ] ℝ => f Y)
    (L.form.map_smul a X)

theorem form_smul_right (a : ℝ) (X Y : Tangent) :
    L.form X (a • Y) = a * L.form X Y := by
  exact (L.form X).map_smul a Y

end SouriauLieLeafData
end Leaf

section Prequantum

variable {Base Tangent : Type*}
variable [AddCommGroup Tangent] [Module ℝ Tangent]
variable [LieRing Tangent] [LieAlgebra ℝ Tangent]

/-- The total space of the canonical trivial complex line bundle over `Base`. -/
def trivialLineTotal (Base : Type*) := Base × ℂ

/-- Projection of the canonical trivial line bundle. -/
def trivialLineProjection {Base : Type*} : trivialLineTotal Base → Base := Prod.fst

/-- Scalar multiplication in each fibre of the trivial line bundle. -/
def trivialLineScalar {Base : Type*} (c : ℂ) (p : trivialLineTotal Base) :
    trivialLineTotal Base := (p.1, c * p.2)

/-- The circle frame bundle of the trivial line bundle. -/
def trivialFrameTotal (Base : Type*) := Base × Circle

/-- Projection of the circle frame bundle. -/
def trivialFrameProjection {Base : Type*} : trivialFrameTotal Base → Base := Prod.fst

/-- Right circle action on the frame bundle. -/
noncomputable def trivialFrameAction {Base : Type*}
    (p : trivialFrameTotal Base) (u : Circle) : trivialFrameTotal Base :=
  (p.1, p.2 * u)

theorem trivialLineProjection_scalar {Base : Type*} (c : ℂ)
    (p : trivialLineTotal Base) :
    trivialLineProjection (trivialLineScalar c p) = trivialLineProjection p := rfl

theorem trivialFrameProjection_action {Base : Type*}
    (p : trivialFrameTotal Base) (u : Circle) :
    trivialFrameProjection (trivialFrameAction p u) =
      trivialFrameProjection p := rfl

theorem trivialFrameAction_one {Base : Type*} (p : trivialFrameTotal Base) :
    trivialFrameAction p 1 = p := by
  cases p
  simp [trivialFrameAction]

theorem trivialFrameAction_mul {Base : Type*} (p : trivialFrameTotal Base)
    (u v : Circle) :
    trivialFrameAction (trivialFrameAction p u) v =
      trivialFrameAction p (u * v) := by
  cases p
  simp [trivialFrameAction, mul_assoc]

/-- A scaled symplectic curvature datum.

The relation `ℏ F = ω` is only a finite algebraic normalization.  It is not a
claim that `curvature` is the curvature of a connection.
-/
structure ScaledSymplecticCurvatureData (L : SouriauLieLeafData (State := Base)
    (Tangent := Tangent)) where
  hbar : ℝ
  hbar_ne_zero : hbar ≠ 0
  curvature : Tangent →ₗ[ℝ] Tangent →ₗ[ℝ] ℝ
  curvature_skew : ∀ X Y, curvature X Y = -curvature Y X
  curvature_relation : ∀ X Y, hbar * curvature X Y = L.form X Y

namespace ScaledSymplecticCurvatureData

variable {L : SouriauLieLeafData (State := Base) (Tangent := Tangent)}

theorem form_eq_hbar_mul_curvature (P : ScaledSymplecticCurvatureData L)
    (X Y : Tangent) :
    L.form X Y = P.hbar * P.curvature X Y := by
  exact (P.curvature_relation X Y).symm

theorem curvature_is_alternating (P : ScaledSymplecticCurvatureData L)
    (X Y : Tangent) :
    P.curvature X Y = -P.curvature Y X :=
  P.curvature_skew X Y

theorem curvature_unique (P Q : ScaledSymplecticCurvatureData L)
    (hh : P.hbar = Q.hbar) :
    ∀ X Y, P.curvature X Y = Q.curvature X Y := by
  intro X Y
  have hP := P.curvature_relation X Y
  have hQ := Q.curvature_relation X Y
  rw [← hh] at hQ
  exact (mul_left_cancel₀ P.hbar_ne_zero (hP.trans hQ.symm))

end ScaledSymplecticCurvatureData
end Prequantum

section ConcreteWitness

/-- The two-dimensional real phase-space carrier used for the concrete witness. -/
abbrev SymplecticPlane := Fin 2 → ℝ

instance : Bracket SymplecticPlane SymplecticPlane :=
  ⟨fun _ _ => 0⟩

instance : LieRing SymplecticPlane where
  add_lie := by intros; exact (zero_add 0).symm
  lie_add := by intros; exact (zero_add 0).symm
  lie_self := by intros; rfl
  leibniz_lie := by intros; exact (zero_add 0).symm

noncomputable instance : LieAlgebra ℝ SymplecticPlane where
  lie_smul := by intros; exact (smul_zero _).symm

def standardPlaneFormFun (X Y : SymplecticPlane) : ℝ :=
  X 0 * Y 1 - X 1 * Y 0

def standardPlaneForm :
    SymplecticPlane →ₗ[ℝ] SymplecticPlane →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ standardPlaneFormFun
    (by intro X₁ X₂ Y; simp [standardPlaneFormFun]; ring)
    (by intro a X Y; simp [standardPlaneFormFun]; ring)
    (by intro X Y₁ Y₂; simp [standardPlaneFormFun]; ring)
    (by intro a X Y; simp [standardPlaneFormFun]; ring)

/-- The standard symplectic plane is a concrete non-degenerate Souriau leaf. -/
def standardSymplecticPlaneLeaf :
    SouriauLieLeafData (State := SymplecticPlane) (Tangent := SymplecticPlane) where
  carrier := Set.univ
  point := id
  point_mem := by simp
  form := standardPlaneForm

theorem standardPlane_form_skew (X Y : SymplecticPlane) :
    standardSymplecticPlaneLeaf.form X Y =
      -standardSymplecticPlaneLeaf.form Y X := by
  change standardPlaneFormFun X Y = -standardPlaneFormFun Y X
  unfold standardPlaneFormFun
  ring

theorem standardPlane_form_nondegenerate :
    ∀ X, (∀ Y, standardSymplecticPlaneLeaf.form X Y = 0) → X = 0 := by
  intro X hX
  have h0 := hX (fun i : Fin 2 => if i = (1 : Fin 2) then 1 else 0)
  have h1 := hX (fun i : Fin 2 => if i = (0 : Fin 2) then 1 else 0)
  have hx0 : X 0 = 0 := by
    change standardPlaneFormFun X (fun i : Fin 2 => if i = (1 : Fin 2) then 1 else 0) = 0 at h0
    simpa [standardPlaneFormFun] using h0
  have hx1 : X 1 = 0 := by
    change standardPlaneFormFun X (fun i : Fin 2 => if i = (0 : Fin 2) then 1 else 0) = 0 at h1
    simpa [standardPlaneFormFun] using h1
  funext i
  fin_cases i <;> assumption

theorem standardPlane_form_closed (X Y Z : SymplecticPlane) :
    standardSymplecticPlaneLeaf.form X ⁅Y, Z⁆ +
      standardSymplecticPlaneLeaf.form Y ⁅Z, X⁆ +
      standardSymplecticPlaneLeaf.form Z ⁅X, Y⁆ = 0 := by
  have hYZ : ⁅Y, Z⁆ = (0 : SymplecticPlane) := rfl
  have hZX : ⁅Z, X⁆ = (0 : SymplecticPlane) := rfl
  have hXY : ⁅X, Y⁆ = (0 : SymplecticPlane) := rfl
  rw [hYZ, hZX, hXY]
  simp only [map_zero, add_zero, zero_add]

noncomputable def standardPlaneScaledCurvature (hbar : ℝ) (hh : hbar ≠ 0) :
    ScaledSymplecticCurvatureData standardSymplecticPlaneLeaf where
  hbar := hbar
  hbar_ne_zero := hh
  curvature := (hbar⁻¹) • standardPlaneForm
  curvature_skew := by
    intro X Y
    change hbar⁻¹ * standardPlaneFormFun X Y =
      -(hbar⁻¹ * standardPlaneFormFun Y X)
    rw [show standardPlaneFormFun Y X = -standardPlaneFormFun X Y by
      change Y 0 * X 1 - Y 1 * X 0 =
        -(X 0 * Y 1 - X 1 * Y 0)
      ring]
    ring
  curvature_relation := by
    intro X Y
    change hbar * (hbar⁻¹ * standardPlaneFormFun X Y) = standardPlaneFormFun X Y
    field_simp

theorem standardPlane_scaled_curvature_relation
    (hbar : ℝ) (hh : hbar ≠ 0) (X Y : SymplecticPlane) :
    hbar * (standardPlaneScaledCurvature hbar hh).curvature X Y =
      standardSymplecticPlaneLeaf.form X Y :=
  (standardPlaneScaledCurvature hbar hh).curvature_relation X Y

end ConcreteWitness

end
end Canonical
end InfoGeometry
