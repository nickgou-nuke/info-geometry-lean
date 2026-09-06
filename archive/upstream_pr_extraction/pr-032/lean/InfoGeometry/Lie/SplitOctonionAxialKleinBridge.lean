import InfoGeometry.Lie.SplitOctonionAxialWittReduction
import InfoGeometry.Lie.SplitOctonionAxialCartanSupport
import InfoGeometry.Canonical.KleinBivectorLinear
import InfoGeometry.Projective.ExteriorPowerPluckerBridge

/-!
# Axial Zorn support as Klein bivector coordinates

The active Drazin support of the diagonal axial tripotent has three upper and
three lower coordinates.  This file identifies those six coordinates with the
repo's canonical Pluecker-coordinate carrier and proves that the Zorn
determinant is exactly the Klein quadratic form.

This is a coordinate bridge to the existing exterior/Klein owner.  It does not
assert an orthogonal-group, spin-group, Grassmannian, or projective-space
equivalence.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialKleinBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Lie.SplitOctonionAxialSupportGrading
open InfoGeometry.Lie.SplitOctonionAxialWittReduction
open InfoGeometry.Lie.SplitOctonionAxialCartanSupport
open InfoGeometry.Lie.SplitOctonionAxialCartanFlow
open InfoGeometry.Projective.ExteriorPowerPluckerBridge

/-- The sign convention sending the three Witt pairs to the six canonical
Pluecker coordinates.  It is chosen so that the Klein form is `-x dot y`. -/
def wittKleinEquiv : WittCoordinates ≃ Bivector4 where
  toFun xy :=
    { p01 := xy.1 0
      p02 := xy.1 1
      p03 := xy.1 2
      p12 := -xy.2 2
      p13 := xy.2 1
      p23 := -xy.2 0 }
  invFun P :=
    (![P.p01, P.p02, P.p03], ![-P.p23, P.p13, -P.p12])
  left_inv xy := by
    rcases xy with ⟨x, y⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp
  right_inv P := by
    cases P
    simp

/-- Linear coordinate permutation/sign change underlying `wittKleinEquiv`. -/
def wittKleinCoordinatesLinearEquiv :
    WittCoordinates ≃ₗ[ℝ] (Fin 6 → ℝ) where
  toFun xy :=
    ![xy.1 0, xy.1 1, xy.1 2, -xy.2 2, xy.2 1, -xy.2 0]
  invFun c :=
    (![c 0, c 1, c 2], ![-c 5, c 4, -c 3])
  left_inv xy := by
    rcases xy with ⟨x, y⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp
  right_inv c := by
    funext i
    fin_cases i <;> simp
  map_add' X Y := by
    funext i
    fin_cases i <;> simp [add_comm]
  map_smul' r X := by
    funext i
    fin_cases i <;> simp

/-- Genuine real-linear equivalence between the three-Witt-pair carrier and
the canonical six Pluecker coordinates. -/
def wittKleinLinearEquiv : WittCoordinates ≃ₗ[ℝ] Bivector4 :=
  wittKleinCoordinatesLinearEquiv.trans bivector4CoordinateLinearEquiv.symm

theorem wittKleinLinearEquiv_toEquiv :
    wittKleinLinearEquiv.toEquiv = wittKleinEquiv := by
  apply Equiv.ext
  intro X
  rcases X with ⟨x, y⟩
  rfl

/-- The actual active Zorn sector and canonical Klein bivector coordinates
carry the same six real coordinates. -/
def activeKleinEquiv : ActiveSector ≃ Bivector4 :=
  activeSectorEquiv.toEquiv.trans wittKleinEquiv

/-- The active Drazin support and canonical Pluecker coordinates are linearly,
not merely set-theoretically, equivalent. -/
def activeKleinLinearEquiv : ActiveSector ≃ₗ[ℝ] Bivector4 :=
  activeSectorEquiv.trans wittKleinLinearEquiv

theorem activeKleinLinearEquiv_toEquiv :
    activeKleinLinearEquiv.toEquiv = activeKleinEquiv := by
  apply Equiv.ext
  intro X
  rfl

/-- The Klein quadratic form is the three-Witt-pair form under the concrete
coordinate equivalence. -/
theorem kleinForm_wittKleinEquiv (xy : WittCoordinates) :
    kleinForm (wittKleinEquiv xy) = -ZornMatrix.dot xy.1 xy.2 := by
  rcases xy with ⟨x, y⟩
  simp [wittKleinEquiv, kleinForm, ZornMatrix.dot]
  ring

/-- On the active Drazin support, the canonical Klein form is exactly the
native Zorn determinant. -/
theorem kleinForm_activeKleinEquiv (X : ActiveSector) :
    kleinForm (activeKleinEquiv X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X.1 := by
  rw [activeKleinEquiv, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
    kleinForm_wittKleinEquiv]
  rcases X with ⟨X, Y, hY⟩
  change -ZornMatrix.dot X.x X.y =
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X
  rw [← hY, detZ_axialActiveSupport]
  simp [axialActiveSupport_apply]

/-- The quadratic-form identity through the genuine linear equivalence.  This
is the native six-dimensional split-form isometry statement; the preceding
theorem is its underlying set-equivalence readout. -/
theorem kleinForm_activeKleinLinearEquiv (X : ActiveSector) :
    kleinForm (activeKleinLinearEquiv X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X.1 := by
  have hX : activeKleinLinearEquiv X = activeKleinEquiv X := by
    change activeKleinLinearEquiv.toEquiv X = activeKleinEquiv X
    rw [activeKleinLinearEquiv_toEquiv]
  rw [hX]
  exact kleinForm_activeKleinEquiv X

/-- The native cross-term polarization of the active Zorn determinant. -/
def activeDetPolar (X Y : ActiveSector) : ℝ :=
  InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (X.1 + Y.1) -
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X.1 -
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ Y.1

/-- The corresponding cross-term polarization of the Klein form. -/
def activeKleinPolar (X Y : ActiveSector) : ℝ :=
  kleinForm (activeKleinLinearEquiv (X + Y)) -
    kleinForm (activeKleinLinearEquiv X) -
      kleinForm (activeKleinLinearEquiv Y)

/-- The active Zorn/Klein linear equivalence preserves the full polar form,
not only the self-pairing quadratic values. -/
theorem activeKleinLinearEquiv_preserves_polar (X Y : ActiveSector) :
    activeKleinPolar X Y = activeDetPolar X Y := by
  unfold activeKleinPolar activeDetPolar
  rw [kleinForm_activeKleinLinearEquiv,
    kleinForm_activeKleinLinearEquiv,
    kleinForm_activeKleinLinearEquiv]
  rfl

/-- The active Zorn support is linearly identified with the genuine second
    exterior power of the four-coordinate carrier. -/
def activeExteriorLinearEquiv :
    ActiveSector ≃ₗ[ℝ] (⋀[ℝ]^2 FierzKleinFoundation.Vec4) :=
  activeKleinLinearEquiv.trans
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv.symm

theorem exteriorKleinForm_activeExterior (X : ActiveSector) :
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm
        (activeExteriorLinearEquiv X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X.1 := by
  rw [InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm,
    activeExteriorLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  have hX : activeKleinLinearEquiv X = activeKleinEquiv X := by
    change activeKleinLinearEquiv.toEquiv X = activeKleinEquiv X
    rw [activeKleinLinearEquiv_toEquiv]
  rw [hX]
  exact kleinForm_activeKleinEquiv X

/-- The cross-term polarization of the literal exterior Klein form along the
active-sector transport. -/
def activeExteriorPolar (X Y : ActiveSector) : ℝ :=
  InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm
      (activeExteriorLinearEquiv (X + Y)) -
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm
      (activeExteriorLinearEquiv X) -
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm
        (activeExteriorLinearEquiv Y)

/-- The literal exterior-power Klein polarization agrees with the native
active Zorn determinant polarization. -/
theorem activeExteriorLinearEquiv_preserves_polar (X Y : ActiveSector) :
    activeExteriorPolar X Y = activeDetPolar X Y := by
  unfold activeExteriorPolar activeDetPolar
  rw [exteriorKleinForm_activeExterior,
    exteriorKleinForm_activeExterior,
    exteriorKleinForm_activeExterior]
  rfl

/-- The active Zorn null cone is exactly the decomposable locus after the
    literal exterior-power transport. -/
theorem detZ_eq_zero_iff_activeExterior_decomposable (X : ActiveSector) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X.1 = 0 ↔
      ∃ u v : InfoGeometry.Canonical.FierzKleinFoundation.Vec4,
        activeExteriorLinearEquiv X =
          exteriorPower.ιMulti ℝ 2 ![u, v] := by
  constructor
  · intro hX
    apply (_root_.InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm_zero_iff_exists_ιMulti
      (activeExteriorLinearEquiv X)).1
    rw [exteriorKleinForm_activeExterior]
    exact hX
  · rintro ⟨u, v, hX⟩
    have hK :
        InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm
            (activeExteriorLinearEquiv X) = 0 := by
      rw [hX]
      exact _root_.InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm_ιMulti u v
    rw [exteriorKleinForm_activeExterior] at hK
    exact hK

/-- The active Zorn vector is null exactly when its corresponding Pluecker
coordinate lies on the Klein quadric. -/
theorem active_on_klein_iff_detZ_eq_zero (X : ActiveSector) :
    IsOnKleinQuadric (activeKleinEquiv X) ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X.1 = 0 := by
  unfold IsOnKleinQuadric
  rw [kleinForm_activeKleinEquiv]

/-- The affine null cone in the active Zorn support. -/
abbrev ActiveNullCone :=
  {X : ActiveSector // InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X.1 = 0}

/-- The affine Klein null cone in the repo's canonical six Pluecker
coordinates. -/
abbrev KleinNullCone := {P : Bivector4 // IsOnKleinQuadric P}

/-- Exact affine-null-cone equivalence induced by the quadratic-coordinate
equivalence.  Projectivization is deliberately not part of this theorem. -/
def activeNullKleinEquiv : ActiveNullCone ≃ KleinNullCone where
  toFun X :=
    ⟨activeKleinEquiv X.1,
      (active_on_klein_iff_detZ_eq_zero X.1).2 X.2⟩
  invFun P :=
    ⟨activeKleinEquiv.symm P.1,
      (active_on_klein_iff_detZ_eq_zero (activeKleinEquiv.symm P.1)).1
        (by simpa using P.2)⟩
  left_inv X := by
    apply Subtype.ext
    exact activeKleinEquiv.symm_apply_apply X.1
  right_inv P := by
    apply Subtype.ext
    exact activeKleinEquiv.apply_symm_apply P.1

/-- Expanded Pluecker relation for an active Zorn vector.  This theorem makes
the coordinate polynomial explicit rather than hiding it behind the Klein
predicate. -/
theorem detZ_eq_zero_iff_plucker_relation (X : ActiveSector) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X.1 = 0 ↔
      let P := activeKleinEquiv X
      P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12 = 0 := by
  rw [← active_on_klein_iff_detZ_eq_zero]
  rfl

/-! ## Cartan-flow readout on the Klein quadratic form -/

theorem axialCartanFlow_preserves_activeKleinForm
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (Z : InfoGeometry.Canonical.ZornMatrix ℝ) :
    kleinForm (activeKleinEquiv
        ⟨axialActiveSupport (axialCartanFlow k t Z), ⟨axialCartanFlow k t Z, rfl⟩⟩) =
      kleinForm (activeKleinEquiv
        ⟨axialActiveSupport Z, ⟨Z, rfl⟩⟩) := by
  rw [kleinForm_activeKleinEquiv, kleinForm_activeKleinEquiv]
  exact axialCartanFlow_preserves_active_det k hk t Z

end InfoGeometry.Lie.SplitOctonionAxialKleinBridge
