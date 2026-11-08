import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PositiveHomogeneousBarrier

namespace InfoGeometry.Geometry.ScaleTopologyShape

noncomputable section

/-!
# Decoupled scale, monodromy, and shape readouts

This file is an interface layer only.  It packages three independently typed
readouts of a carrier; it does not assert a universal Cartan decomposition or
identify an arbitrary Artin state with the concrete `G₂` Weyl carrier.
-/

/-- Three independent readouts on a geometric carrier. -/
structure ScaleTopologyShapeDatum (X : Type*)
    (ArtinState ShapeSpace : Type*) where
  /-- The radial or scale readout. -/
  scale : X → ℝ
  /-- The path-level or monodromy readout. -/
  monodromy : X → ArtinState
  /-- The homogeneous-shape readout. -/
  shape : X → ShapeSpace

/--
Read a concrete `G₂` Weyl index from an already supplied Artin-state map.
The map is an explicit parameter: this definition does not postulate an
Artin-to-Weyl projection for arbitrary `ArtinState`.
-/
def toWeylChamber {X ArtinState ShapeSpace : Type*}
    (datum : ScaleTopologyShapeDatum X ArtinState ShapeSpace)
    (artinToWeyl : ArtinState → (ZMod 6 × Bool)) (x : X) : ZMod 6 × Bool :=
  artinToWeyl (datum.monodromy x)

/--
The scale action changes only the scale readout while preserving the other
two readouts.  The additive law fixes the normalization of the scale
coordinate; no shape or monodromy equivalence is inferred from it.
-/
def IsScaleDecoupled {X ArtinState ShapeSpace : Type*}
    (datum : ScaleTopologyShapeDatum X ArtinState ShapeSpace)
    (scaleAction : ℝ → X → X) : Prop :=
  (∀ (t : ℝ) (x : X),
      datum.scale (scaleAction t x) = datum.scale x + t) ∧
    (∀ (t : ℝ) (x : X),
      datum.monodromy (scaleAction t x) = datum.monodromy x) ∧
    (∀ (t : ℝ) (x : X),
      datum.shape (scaleAction t x) = datum.shape x)

@[simp]
theorem toWeylChamber_scale_invariant
    {X ArtinState ShapeSpace : Type*}
    {datum : ScaleTopologyShapeDatum X ArtinState ShapeSpace}
    {scaleAction : ℝ → X → X}
    (compat : IsScaleDecoupled datum scaleAction)
    (artinToWeyl : ArtinState → (ZMod 6 × Bool)) (t : ℝ) (x : X) :
    toWeylChamber datum artinToWeyl (scaleAction t x) =
      toWeylChamber datum artinToWeyl x := by
  unfold toWeylChamber
  rw [compat.2.1]

/-! ## Two-dimensional positive-cone model -/

structure PosCone2DData where
  p : ℝ
  q : ℝ

def PosCone2D := {x : PosCone2DData // 0 < x.p ∧ 0 < x.q}

namespace PosCone2D

def scaleAction (t : ℝ) (x : PosCone2D) : PosCone2D where
  val := ⟨Real.exp (-t) * x.1.p, Real.exp (-t) * x.1.q⟩
  property := ⟨mul_pos (Real.exp_pos _) x.2.1,
    mul_pos (Real.exp_pos _) x.2.2⟩

@[simp] theorem scaleAction_zero (x : PosCone2D) :
    scaleAction 0 x = x := by
  rcases x with ⟨⟨p, q⟩, hpq⟩
  apply Subtype.ext
  simp [scaleAction]

theorem scaleAction_add (t u : ℝ) (x : PosCone2D) :
    scaleAction (t + u) x = scaleAction t (scaleAction u x) := by
  rcases x with ⟨⟨p, q⟩, hpq⟩
  apply Subtype.ext
  dsimp [scaleAction]
  change
    PosCone2DData.mk (Real.exp (-(t + u)) * p) (Real.exp (-(t + u)) * q) =
      PosCone2DData.mk (Real.exp (-t) * (Real.exp (-u) * p))
        (Real.exp (-t) * (Real.exp (-u) * q))
  congr 1
  · rw [show -(t + u) = -t + -u by ring, Real.exp_add]
    ring
  · rw [show -(t + u) = -t + -u by ring, Real.exp_add]
    ring

theorem scaleAction_comm (t u : ℝ) (x : PosCone2D) :
    scaleAction t (scaleAction u x) = scaleAction u (scaleAction t x) := by
  rw [← scaleAction_add, ← scaleAction_add, add_comm]

theorem scaleAction_neg_left (t : ℝ) (x : PosCone2D) :
    scaleAction (-t) (scaleAction t x) = x := by
  rw [← scaleAction_add]
  simp

theorem scaleAction_neg_right (t : ℝ) (x : PosCone2D) :
    scaleAction t (scaleAction (-t) x) = x := by
  rw [← scaleAction_add]
  simp

theorem scaleAction_injective (t : ℝ) :
    Function.Injective (scaleAction t) := by
  intro x y hxy
  have h := congrArg (scaleAction (-t)) hxy
  simpa only [scaleAction_neg_left] using h

theorem scaleAction_surjective (t : ℝ) :
    Function.Surjective (scaleAction t) := by
  intro y
  exact ⟨scaleAction (-t) y, scaleAction_neg_right t y⟩

theorem scaleAction_bijective (t : ℝ) :
    Function.Bijective (scaleAction t) :=
  ⟨scaleAction_injective t, scaleAction_surjective t⟩

theorem hp (x : PosCone2D) : 0 < x.1.p := x.2.1

theorem hq (x : PosCone2D) : 0 < x.1.q := x.2.2

def scaleCoord (x : PosCone2D) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (x.1.p * x.1.q)

def shapeCoord (x : PosCone2D) : ℝ := x.1.p / x.1.q

def trivialMonodromy (_ : PosCone2D) : Unit := ()

def posConeDatum : ScaleTopologyShapeDatum PosCone2D Unit ℝ where
  scale := scaleCoord
  monodromy := trivialMonodromy
  shape := shapeCoord

theorem scaleCoord_trans (t : ℝ) (x : PosCone2D) :
    scaleCoord (scaleAction t x) = scaleCoord x + t := by
  unfold scaleCoord scaleAction
  have hprod : 0 < x.1.p * x.1.q := mul_pos (hp x) (hq x)
  have h_exp : 0 < Real.exp (-t) := Real.exp_pos _
  have hmul :
      (Real.exp (-t) * x.1.p) * (Real.exp (-t) * x.1.q) =
        Real.exp (-2 * t) * (x.1.p * x.1.q) := by
    calc
      (Real.exp (-t) * x.1.p) * (Real.exp (-t) * x.1.q) =
          (Real.exp (-t) * Real.exp (-t)) * (x.1.p * x.1.q) := by ring
      _ = Real.exp (-t + -t) * (x.1.p * x.1.q) := by
        rw [← Real.exp_add]
      _ = Real.exp (-2 * t) * (x.1.p * x.1.q) := by ring_nf
  rw [hmul, Real.log_mul (ne_of_gt (Real.exp_pos (-2 * t)))
    (ne_of_gt hprod), Real.log_exp]
  ring

theorem shapeCoord_inv (t : ℝ) (x : PosCone2D) :
    shapeCoord (scaleAction t x) = shapeCoord x := by
  unfold shapeCoord scaleAction
  exact mul_div_mul_left x.1.p x.1.q (ne_of_gt (Real.exp_pos (-t)))

theorem posCone_isScaleDecoupled :
    IsScaleDecoupled posConeDatum scaleAction :=
  ⟨scaleCoord_trans, by intro t x; rfl, shapeCoord_inv⟩

end PosCone2D

/-! ## Canonical positive-homogeneous cone model -/

namespace PositiveHomogeneousConeModel

open InfoGeometry.Canonical.PositiveHomogeneousBarrier

def uniformScaleAction (t : ℝ) (x : PositiveHomogeneousCone) :
    PositiveHomogeneousCone :=
  ⟨(Real.exp (-t) * x.1.1, Real.exp (-t) * x.1.2), by
    exact ⟨mul_pos (Real.exp_pos _) x.2.1,
      mul_pos (Real.exp_pos _) x.2.2⟩⟩

@[simp] theorem uniformScaleAction_zero (x : PositiveHomogeneousCone) :
    uniformScaleAction 0 x = x := by
  apply Subtype.ext
  ext <;> simp [uniformScaleAction]

theorem uniformScaleAction_add (t u : ℝ) (x : PositiveHomogeneousCone) :
    uniformScaleAction (t + u) x = uniformScaleAction t (uniformScaleAction u x) := by
  apply Subtype.ext
  ext <;> dsimp [uniformScaleAction]
  · rw [show -(t + u) = -t + -u by ring, Real.exp_add]
    ring
  · rw [show -(t + u) = -t + -u by ring, Real.exp_add]
    ring

theorem uniformScaleAction_neg_left (t : ℝ) (x : PositiveHomogeneousCone) :
    uniformScaleAction (-t) (uniformScaleAction t x) = x := by
  rw [← uniformScaleAction_add]
  simp

theorem uniformScaleAction_neg_right (t : ℝ) (x : PositiveHomogeneousCone) :
    uniformScaleAction t (uniformScaleAction (-t) x) = x := by
  rw [← uniformScaleAction_add]
  simp

theorem uniformScaleAction_comm (t u : ℝ) (x : PositiveHomogeneousCone) :
    uniformScaleAction t (uniformScaleAction u x) =
      uniformScaleAction u (uniformScaleAction t x) := by
  rw [← uniformScaleAction_add, ← uniformScaleAction_add, add_comm]

theorem uniformScaleAction_injective (t : ℝ) :
    Function.Injective (uniformScaleAction t) := by
  intro x y hxy
  have h := congrArg (uniformScaleAction (-t)) hxy
  simpa only [uniformScaleAction_neg_left] using h

theorem uniformScaleAction_surjective (t : ℝ) :
    Function.Surjective (uniformScaleAction t) := by
  intro y
  exact ⟨uniformScaleAction (-t) y, uniformScaleAction_neg_right t y⟩

theorem uniformScaleAction_bijective (t : ℝ) :
    Function.Bijective (uniformScaleAction t) :=
  ⟨uniformScaleAction_injective t, uniformScaleAction_surjective t⟩

def scaleCoord (x : PositiveHomogeneousCone) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (x.1.1 * x.1.2)

def shapeCoord (x : PositiveHomogeneousCone) : ℝ :=
  x.1.1 / x.1.2

def trivialMonodromy (_ : PositiveHomogeneousCone) : Unit := ()

def datum : ScaleTopologyShapeDatum PositiveHomogeneousCone Unit ℝ where
  scale := scaleCoord
  monodromy := trivialMonodromy
  shape := shapeCoord

theorem uniformScaleAction_product (t : ℝ) (x : PositiveHomogeneousCone) :
    (uniformScaleAction t x).1.1 * (uniformScaleAction t x).1.2 =
      Real.exp (-2 * t) * (x.1.1 * x.1.2) := by
  change
    (Real.exp (-t) * x.1.1) * (Real.exp (-t) * x.1.2) =
      Real.exp (-2 * t) * (x.1.1 * x.1.2)
  calc
    (Real.exp (-t) * x.1.1) * (Real.exp (-t) * x.1.2) =
        (Real.exp (-t) * Real.exp (-t)) * (x.1.1 * x.1.2) := by ring
    _ = Real.exp (-t + -t) * (x.1.1 * x.1.2) := by
      rw [← Real.exp_add]
    _ = Real.exp (-2 * t) * (x.1.1 * x.1.2) := by ring_nf

theorem scaleCoord_eq_half_barrier (x : PositiveHomogeneousCone) :
    scaleCoord x = (1 / 2 : ℝ) * barrier x := by
  rw [barrier_eq_neg_log_product]
  unfold scaleCoord
  ring

theorem scaleCoord_trans (t : ℝ) (x : PositiveHomogeneousCone) :
    scaleCoord (uniformScaleAction t x) = scaleCoord x + t := by
  unfold scaleCoord uniformScaleAction
  have hprod : 0 < x.1.1 * x.1.2 := mul_pos x.2.1 x.2.2
  have hmul :
      (Real.exp (-t) * x.1.1) * (Real.exp (-t) * x.1.2) =
        Real.exp (-2 * t) * (x.1.1 * x.1.2) := by
    calc
      (Real.exp (-t) * x.1.1) * (Real.exp (-t) * x.1.2) =
          (Real.exp (-t) * Real.exp (-t)) * (x.1.1 * x.1.2) := by ring
      _ = Real.exp (-t + -t) * (x.1.1 * x.1.2) := by
        rw [← Real.exp_add]
      _ = Real.exp (-2 * t) * (x.1.1 * x.1.2) := by ring_nf
  rw [hmul, Real.log_mul (ne_of_gt (Real.exp_pos (-2 * t)))
    (ne_of_gt hprod), Real.log_exp]
  ring

theorem barrier_uniformScaleAction (t : ℝ) (x : PositiveHomogeneousCone) :
    barrier (uniformScaleAction t x) = barrier x + 2 * t := by
  have hprod : 0 < x.1.1 * x.1.2 := mul_pos x.2.1 x.2.2
  rw [barrier_eq_neg_log_product, uniformScaleAction_product,
    Real.log_mul (ne_of_gt (Real.exp_pos (-2 * t))) (ne_of_gt hprod),
    Real.log_exp, barrier_eq_neg_log_product]
  ring

theorem shapeCoord_inv (t : ℝ) (x : PositiveHomogeneousCone) :
    shapeCoord (uniformScaleAction t x) = shapeCoord x := by
  unfold shapeCoord uniformScaleAction
  exact mul_div_mul_left x.1.1 x.1.2 (ne_of_gt (Real.exp_pos (-t)))

theorem isScaleDecoupled :
    IsScaleDecoupled datum uniformScaleAction :=
  ⟨scaleCoord_trans, by intro t x; rfl, shapeCoord_inv⟩

end PositiveHomogeneousConeModel

/-! ## Morphisms of scale/topology/shape data -/

structure ScaleTopologyShapeHomData
    {X Y : Type*} {A₁ A₂ S₁ S₂ : Type*}
    (D₁ : ScaleTopologyShapeDatum X A₁ S₁)
    (D₂ : ScaleTopologyShapeDatum Y A₂ S₂) where
  toFun : X → Y
  mapMonodromy : A₁ → A₂
  mapShape : S₁ → S₂
  scale_shift : ℝ

def ScaleTopologyShapeHomLaws
    {X Y A₁ A₂ S₁ S₂ : Type*}
    {D₁ : ScaleTopologyShapeDatum X A₁ S₁}
    {D₂ : ScaleTopologyShapeDatum Y A₂ S₂}
    (f : ScaleTopologyShapeHomData D₁ D₂) : Prop :=
  (∀ x, D₂.scale (f.toFun x) = D₁.scale x + f.scale_shift) ∧
    (∀ x, D₂.monodromy (f.toFun x) = f.mapMonodromy (D₁.monodromy x)) ∧
    (∀ x, D₂.shape (f.toFun x) = f.mapShape (D₁.shape x))

def ScaleTopologyShapeHom
    {X Y A₁ A₂ S₁ S₂ : Type*}
    (D₁ : ScaleTopologyShapeDatum X A₁ S₁)
    (D₂ : ScaleTopologyShapeDatum Y A₂ S₂) : Type _ :=
  {f : ScaleTopologyShapeHomData D₁ D₂ // ScaleTopologyShapeHomLaws f}

namespace ScaleTopologyShapeHom

def id {X A S : Type*} (D : ScaleTopologyShapeDatum X A S) :
    ScaleTopologyShapeHom D D where
  val := ⟨(fun x => x), (fun a => a), (fun s => s), 0⟩
  property := ⟨fun x => by simp, fun x => rfl, fun x => rfl⟩

def comp
    {X Y Z : Type*} {A₁ A₂ A₃ S₁ S₂ S₃ : Type*}
    {D₁ : ScaleTopologyShapeDatum X A₁ S₁}
    {D₂ : ScaleTopologyShapeDatum Y A₂ S₂}
    {D₃ : ScaleTopologyShapeDatum Z A₃ S₃}
    (g : ScaleTopologyShapeHom D₂ D₃)
    (f : ScaleTopologyShapeHom D₁ D₂) :
    ScaleTopologyShapeHom D₁ D₃ := by
  refine ⟨⟨g.1.toFun ∘ f.1.toFun,
    g.1.mapMonodromy ∘ f.1.mapMonodromy,
    g.1.mapShape ∘ f.1.mapShape,
    f.1.scale_shift + g.1.scale_shift⟩, ?_⟩
  rcases f.2 with ⟨hfScale, hfMonodromy, hfShape⟩
  rcases g.2 with ⟨hgScale, hgMonodromy, hgShape⟩
  exact ⟨(fun x => by dsimp; rw [hgScale, hfScale]; ring),
    (fun x => by dsimp; rw [hgMonodromy, hfMonodromy]),
    (fun x => by dsimp; rw [hgShape, hfShape])⟩

@[simp] theorem id_toFun {X A S : Type*}
    (D : ScaleTopologyShapeDatum X A S) (x : X) :
    (id D).1.toFun x = x := rfl

@[simp] theorem id_mapMonodromy {X A S : Type*}
    (D : ScaleTopologyShapeDatum X A S) (a : A) :
    (id D).1.mapMonodromy a = a := rfl

@[simp] theorem id_mapShape {X A S : Type*}
    (D : ScaleTopologyShapeDatum X A S) (s : S) :
    (id D).1.mapShape s = s := rfl

theorem comp_id
    {X Y : Type*} {A₁ A₂ S₁ S₂ : Type*}
    {D₁ : ScaleTopologyShapeDatum X A₁ S₁}
    {D₂ : ScaleTopologyShapeDatum Y A₂ S₂}
    (f : ScaleTopologyShapeHom D₁ D₂) :
    comp (id D₂) f = f := by
  apply Subtype.ext
  simp [comp, id, Function.comp_def]

theorem id_comp
    {X Y : Type*} {A₁ A₂ S₁ S₂ : Type*}
    {D₁ : ScaleTopologyShapeDatum X A₁ S₁}
    {D₂ : ScaleTopologyShapeDatum Y A₂ S₂}
    (f : ScaleTopologyShapeHom D₁ D₂) :
    comp f (id D₁) = f := by
  apply Subtype.ext
  simp [comp, id, Function.comp_def]

theorem comp_assoc
    {W X Y Z : Type*}
    {A₀ A₁ A₂ A₃ S₀ S₁ S₂ S₃ : Type*}
    {D₀ : ScaleTopologyShapeDatum W A₀ S₀}
    {D₁ : ScaleTopologyShapeDatum X A₁ S₁}
    {D₂ : ScaleTopologyShapeDatum Y A₂ S₂}
    {D₃ : ScaleTopologyShapeDatum Z A₃ S₃}
    (h : ScaleTopologyShapeHom D₂ D₃)
    (g : ScaleTopologyShapeHom D₁ D₂)
    (f : ScaleTopologyShapeHom D₀ D₁) :
    comp h (comp g f) = comp (comp h g) f := by
  apply Subtype.ext
  simp [comp, Function.comp_def, add_assoc]

end ScaleTopologyShapeHom

end
end InfoGeometry.Geometry.ScaleTopologyShape
