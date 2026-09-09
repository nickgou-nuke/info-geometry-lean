import InfoGeometry.Lie.SplitOctonionAxialCartanSupport
import InfoGeometry.Lie.SplitOctonionAxialKleinProjective

/-!
# Projective action of the axial Cartan flow

The multiplication-preserving Cartan flow restricts to the active Zorn
support, and therefore descends to its projectivization.  This owner keeps
that restriction separate from the coordinate Klein/exterior equivalence.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitOctonionAxialCartanProjective

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Lie.SplitOctonionAxialCartanFlow
open InfoGeometry.Lie.SplitOctonionAxialCartanSupport
open InfoGeometry.Lie.SplitOctonionAxialKleinBridge
open InfoGeometry.Lie.SplitOctonionAxialKleinProjective
open InfoGeometry.Lie.SplitOctonionAxialSupportGrading
open InfoGeometry.Lie.SplitOctonionAxialWittReduction
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ

private theorem activeCartanFlow_mem
    (k : Fin 3 → ℝ) (t : ℝ) (X : ActiveSector) :
    axialCartanFlow k t X.1 ∈ ActiveSector := by
  rcases X.2 with ⟨Y, hY⟩
  refine ⟨axialCartanFlow k t Y, ?_⟩
  rw [axialCartanFlow_commutes_activeSupport]
  simp [hY]

private theorem activeSupport_self (X : ActiveSector) :
    axialActiveSupport X.1 = X.1 := by
  rcases X.2 with ⟨Y, hY⟩
  rw [← hY]
  simp [axialActiveSupport_apply]

/-- Restriction of the full Cartan equivalence to the active support. -/
def activeCartanFlow (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    ActiveSector ≃ₗ[ℝ] ActiveSector where
  toFun X :=
    ⟨axialCartanFlow k t X.1, activeCartanFlow_mem k t X⟩
  invFun X :=
    ⟨axialCartanFlow k (-t) X.1, activeCartanFlow_mem k (-t) X⟩
  map_add' X Y := by
    apply Subtype.ext
    exact (axialCartanFlow k t).map_add X.1 Y.1
  map_smul' r X := by
    apply Subtype.ext
    exact (axialCartanFlow k t).map_smul r X.1
  left_inv X := by
    apply Subtype.ext
    change axialCartanFlow k (-t) (axialCartanFlow k t X.1) = X.1
    rw [← axialCartanFlow_add, neg_add_cancel, axialCartanFlow_zero]
  right_inv X := by
    apply Subtype.ext
    change axialCartanFlow k t (axialCartanFlow k (-t) X.1) = X.1
    rw [← axialCartanFlow_add, add_neg_cancel, axialCartanFlow_zero]

@[simp] theorem activeCartanFlow_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : ActiveSector) :
    activeCartanFlow k hk t X =
      ⟨axialCartanFlow k t X.1, activeCartanFlow_mem k t X⟩ := rfl

@[simp] theorem activeCartanFlow_zero
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (X : ActiveSector) :
    activeCartanFlow k hk 0 X = X := by
  apply Subtype.ext
  simp [activeCartanFlow]

theorem activeCartanFlow_add
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (s t : ℝ) (X : ActiveSector) :
    activeCartanFlow k hk (s + t) X =
      activeCartanFlow k hk s (activeCartanFlow k hk t X) := by
  apply Subtype.ext
  change axialCartanFlow k (s + t) X.1 =
    axialCartanFlow k s (axialCartanFlow k t X.1)
  exact axialCartanFlow_add k s t X.1

@[simp] theorem activeCartanFlow_neg_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : ActiveSector) :
    (activeCartanFlow k hk t).symm X = activeCartanFlow k hk (-t) X := by
  rfl

/-- Projectivization of the restricted active Cartan flow. -/
def activeCartanProjectiveMap (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    ℙ ℝ ActiveSector → ℙ ℝ ActiveSector :=
  Projectivization.map (activeCartanFlow k hk t).toLinearMap
    (activeCartanFlow k hk t).injective

@[simp] theorem activeCartanProjectiveMap_zero
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) :
    activeCartanProjectiveMap k hk 0 = id := by
  funext p
  refine Projectivization.ind (p := p) ?_
  intro X hX
  rw [activeCartanProjectiveMap, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨1, by simp⟩

theorem activeCartanProjectiveMap_add
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (s t : ℝ) (p : ℙ ℝ ActiveSector) :
    activeCartanProjectiveMap k hk (s + t) p =
      activeCartanProjectiveMap k hk s
        (activeCartanProjectiveMap k hk t p) := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  rw [activeCartanProjectiveMap, Projectivization.map_mk]
  change Projectivization.mk ℝ (activeCartanFlow k hk (s + t) X) _ =
    Projectivization.mk ℝ
      (activeCartanFlow k hk s (activeCartanFlow k hk t X)) _
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨1, by rw [activeCartanFlow_add]; simp⟩

@[simp] theorem activeCartanProjectiveMap_neg
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    activeCartanProjectiveMap k hk (-t) ∘
        activeCartanProjectiveMap k hk t = id := by
  funext p
  change activeCartanProjectiveMap k hk (-t)
      (activeCartanProjectiveMap k hk t p) = p
  rw [← activeCartanProjectiveMap_add]
  simp

/-- The restricted Cartan flow is a genuine projective equivalence. -/
def activeCartanProjectiveEquiv
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    ℙ ℝ ActiveSector ≃ ℙ ℝ ActiveSector where
  toFun := activeCartanProjectiveMap k hk t
  invFun := activeCartanProjectiveMap k hk (-t)
  left_inv p := by
    rw [← activeCartanProjectiveMap_add]
    simp
  right_inv p := by
    rw [← activeCartanProjectiveMap_add]
    simp

theorem activeCartanProjectiveEquiv_add_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (s t : ℝ)
    (p : ℙ ℝ ActiveSector) :
    activeCartanProjectiveEquiv k hk (s + t) p =
      activeCartanProjectiveEquiv k hk s
        (activeCartanProjectiveEquiv k hk t p) := by
  change activeCartanProjectiveMap k hk (s + t) p =
    activeCartanProjectiveMap k hk s
      (activeCartanProjectiveMap k hk t p)
  exact activeCartanProjectiveMap_add k hk s t p

/-- The restricted Cartan flow preserves the native active determinant. -/
theorem activeCartanFlow_preserves_det
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : ActiveSector) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
        (activeCartanFlow k hk t X).1 =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X.1 := by
  change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
      (axialCartanFlow k t X.1) =
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X.1
  have h := axialCartanFlow_preserves_active_det k hk t X.1
  rw [axialCartanFlow_commutes_activeSupport] at h
  rw [activeSupport_self X] at h
  exact h

/-- The determinant invariance read through the genuine active Klein
linear equivalence. -/
theorem activeCartanFlow_preserves_activeKleinForm
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X : ActiveSector) :
    kleinForm (activeKleinLinearEquiv (activeCartanFlow k hk t X)) =
      kleinForm (activeKleinLinearEquiv X) := by
  rw [kleinForm_activeKleinLinearEquiv,
    kleinForm_activeKleinLinearEquiv]
  exact activeCartanFlow_preserves_det k hk t X

/-- The restricted Cartan flow preserves the full active determinant
polarization, hence active incidence rather than only self-nullness. -/
theorem activeCartanFlow_preserves_activeDetPolar
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X Y : ActiveSector) :
    activeDetPolar (activeCartanFlow k hk t X)
        (activeCartanFlow k hk t Y) =
      activeDetPolar X Y := by
  unfold activeDetPolar
  have hsum := congrArg Subtype.val
    ((activeCartanFlow k hk t).map_add X Y)
  change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
      ((activeCartanFlow k hk t X + activeCartanFlow k hk t Y).1) -
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
        (activeCartanFlow k hk t X).1 -
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
        (activeCartanFlow k hk t Y).1 = _
  rw [← hsum]
  rw [activeCartanFlow_preserves_det k hk t (X + Y),
    activeCartanFlow_preserves_det k hk t X,
    activeCartanFlow_preserves_det k hk t Y]
  simp

/-! The same invariance transported through the native active
Zorn/Klein linear equivalence. -/
theorem activeCartanFlow_preserves_activeKleinPolar
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X Y : ActiveSector) :
    activeKleinPolar (activeCartanFlow k hk t X)
        (activeCartanFlow k hk t Y) =
      activeKleinPolar X Y := by
  calc
    activeKleinPolar (activeCartanFlow k hk t X)
        (activeCartanFlow k hk t Y) =
      activeDetPolar (activeCartanFlow k hk t X)
        (activeCartanFlow k hk t Y) :=
      activeKleinLinearEquiv_preserves_polar _ _
    _ = activeDetPolar X Y :=
      activeCartanFlow_preserves_activeDetPolar k hk t X Y
    _ = activeKleinPolar X Y :=
      (activeKleinLinearEquiv_preserves_polar X Y).symm

/- The same invariant after transport to the literal exterior-square
Klein carrier. -/
theorem activeCartanFlow_preserves_activeExteriorPolar
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X Y : ActiveSector) :
    activeExteriorPolar (activeCartanFlow k hk t X)
        (activeCartanFlow k hk t Y) =
      activeExteriorPolar X Y := by
  calc
    activeExteriorPolar (activeCartanFlow k hk t X)
        (activeCartanFlow k hk t Y) =
      activeDetPolar (activeCartanFlow k hk t X)
        (activeCartanFlow k hk t Y) :=
      activeExteriorLinearEquiv_preserves_polar _ _
    _ = activeDetPolar X Y :=
      activeCartanFlow_preserves_activeDetPolar k hk t X Y
    _ = activeExteriorPolar X Y :=
      (activeExteriorLinearEquiv_preserves_polar X Y).symm

theorem activeCartanProjectiveMap_preserves_Klein_null
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (p : ActiveProjective) :
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein
        (activeExteriorProjectiveMap (activeCartanProjectiveMap k hk t p)) ↔
      _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein
        (activeExteriorProjectiveMap p) := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  let Y : ActiveSector := X
  have hY : activeCartanFlow k hk t Y ≠ 0 := by
    intro hzero
    apply hX
    apply Subtype.ext
    apply (axialCartanFlow k t).injective
    have hzero' := congrArg Subtype.val hzero
    dsimp [activeCartanFlow, Y] at hzero'
    change axialCartanFlow k t X.1 = axialCartanFlow k t (0 : CZ)
    rw [(axialCartanFlow k t).map_zero]
    exact hzero'
  rw [activeCartanProjectiveMap, Projectivization.map_mk]
  change
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein
        (activeExteriorProjectiveMap
          (Projectivization.mk ℝ (activeCartanFlow k hk t Y) hY)) ↔
      _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein
        (activeExteriorProjectiveMap (Projectivization.mk ℝ X hX))
  rw [isKlein_activeExteriorProjectiveMap_mk_iff
      (activeCartanFlow k hk t Y) hY,
    isKlein_activeExteriorProjectiveMap_mk_iff Y (by
      intro hzero
      exact hX hzero)]
  rw [activeCartanFlow_preserves_det k hk t Y]

/-- The Cartan flow descends to an equivalence of the projective Klein-null
locus.  The inverse is the flow at the opposite parameter. -/
def activeCartanProjectiveNullEquiv
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    ActiveKleinNullProjective ≃ ActiveKleinNullProjective where
  toFun p :=
    ⟨activeCartanProjectiveMap k hk t p.1,
      (activeCartanProjectiveMap_preserves_Klein_null k hk t p.1).2 p.2⟩
  invFun p :=
    ⟨activeCartanProjectiveMap k hk (-t) p.1,
      (activeCartanProjectiveMap_preserves_Klein_null k hk (-t) p.1).2 p.2⟩
  left_inv p := by
    apply Subtype.ext
    change activeCartanProjectiveMap k hk (-t)
        (activeCartanProjectiveMap k hk t p.1) = p.1
    rw [← activeCartanProjectiveMap_add, neg_add_cancel,
      activeCartanProjectiveMap_zero]
    rfl
  right_inv p := by
    apply Subtype.ext
    change activeCartanProjectiveMap k hk t
        (activeCartanProjectiveMap k hk (-t) p.1) = p.1
    rw [← activeCartanProjectiveMap_add, add_neg_cancel,
      activeCartanProjectiveMap_zero]
    rfl

abbrev ExteriorSquare :=
  (⋀[ℝ]^2 InfoGeometry.Canonical.FierzKleinFoundation.Vec4)

/-- The same Cartan flow written in the canonical exterior coordinates. -/
def exteriorCartanFlow
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    ExteriorSquare ≃ₗ[ℝ] ExteriorSquare :=
  activeExteriorLinearEquiv.symm.trans
    ((activeCartanFlow k hk t).trans activeExteriorLinearEquiv)

@[simp] theorem exteriorCartanFlow_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : ActiveSector) :
    exteriorCartanFlow k hk t (activeExteriorLinearEquiv X) =
      activeExteriorLinearEquiv (activeCartanFlow k hk t X) := by
  simp [exteriorCartanFlow]

theorem exteriorCartanFlow_preserves_Klein_form
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X : ExteriorSquare) :
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm
        (exteriorCartanFlow k hk t X) =
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm X := by
  rcases activeExteriorLinearEquiv.surjective X with ⟨Y, rfl⟩
  rw [exteriorCartanFlow_apply,
    InfoGeometry.Lie.SplitOctonionAxialKleinBridge.exteriorKleinForm_activeExterior,
    InfoGeometry.Lie.SplitOctonionAxialKleinBridge.exteriorKleinForm_activeExterior]
  exact activeCartanFlow_preserves_det k hk t Y

/-- The cross-term polarization of the literal exterior Klein form. -/
def exteriorKleinPolar (X Y : ExteriorSquare) : ℝ :=
  InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm (X + Y) -
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm X -
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm Y

theorem exteriorKleinPolar_activeExterior (X Y : ActiveSector) :
    exteriorKleinPolar (activeExteriorLinearEquiv X)
        (activeExteriorLinearEquiv Y) = activeExteriorPolar X Y := by
  unfold exteriorKleinPolar activeExteriorPolar
  rw [← map_add activeExteriorLinearEquiv X Y]

/-- The exterior-coordinate Cartan flow preserves the full Klein polar form. -/
theorem exteriorCartanFlow_preserves_Klein_polar
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X Y : ExteriorSquare) :
    exteriorKleinPolar (exteriorCartanFlow k hk t X)
        (exteriorCartanFlow k hk t Y) =
      exteriorKleinPolar X Y := by
  rcases activeExteriorLinearEquiv.surjective X with ⟨X, rfl⟩
  rcases activeExteriorLinearEquiv.surjective Y with ⟨Y, rfl⟩
  rw [exteriorCartanFlow_apply, exteriorCartanFlow_apply]
  rw [exteriorKleinPolar_activeExterior,
    exteriorKleinPolar_activeExterior]
  exact activeCartanFlow_preserves_activeExteriorPolar k hk t X Y

/-- Projectivization of the exterior-coordinate Cartan flow. -/
def exteriorCartanProjectiveMap
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    ℙ ℝ ExteriorSquare → ℙ ℝ ExteriorSquare :=
  Projectivization.map (exteriorCartanFlow k hk t).toLinearMap
    (exteriorCartanFlow k hk t).injective

theorem exteriorCartanProjectiveMap_intertwines
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (p : ℙ ℝ ActiveSector) :
    exteriorCartanProjectiveMap k hk t (activeExteriorProjectiveMap p) =
      activeExteriorProjectiveMap
        (activeCartanProjectiveMap k hk t p) := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  rw [activeExteriorProjectiveMap, Projectivization.map_mk,
    activeCartanProjectiveMap, Projectivization.map_mk,
    exteriorCartanProjectiveMap, Projectivization.map_mk]
  change Projectivization.mk ℝ
      (exteriorCartanFlow k hk t (activeExteriorLinearEquiv X)) _ =
    Projectivization.mk ℝ
      (activeExteriorLinearEquiv (activeCartanFlow k hk t X)) _
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨1, by simp [exteriorCartanFlow_apply]⟩

theorem exteriorCartanProjectiveMap_preserves_Klein_null
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (p : ExteriorKleinNullProjective) :
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein
      (exteriorCartanProjectiveMap k hk t p.1) := by
  let q : ActiveKleinNullProjective :=
    activeExteriorProjectiveNullEquiv.symm p
  have hq := exteriorCartanProjectiveMap_intertwines k hk t q.1
  have hqp : activeExteriorProjectiveMap q.1 = p.1 := by
    exact congrArg Subtype.val
      (activeExteriorProjectiveNullEquiv.apply_symm_apply p)
  rw [← hqp, hq]
  exact (activeCartanProjectiveNullEquiv k hk t q).2

end InfoGeometry.Lie.SplitOctonionAxialCartanProjective
