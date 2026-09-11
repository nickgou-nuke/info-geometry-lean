import InfoGeometry.Lie.SplitOctonionAxialKleinBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Polar-form isometry of the axial Zorn and Klein `(3,3)` models

The quadratic forms were identified in
`SplitOctonionAxialKleinBridge`.  Here we polarize them with the convention

`B(u,v) = Q(u+v) - Q(u) - Q(v)`

and prove that the same concrete coordinate equivalence preserves the resulting
bilinear polynomial.  No factor `1/2` is inserted.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialKleinPolar

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Lie.SplitOctonionAxialWittReduction
open InfoGeometry.Lie.SplitOctonionAxialKleinBridge
open InfoGeometry.Projective.ExteriorPowerPluckerBridge

/-- Polarization of the canonical Klein quadratic polynomial, written directly
in its six Pluecker coordinates. -/
def kleinPolar (P Q : Bivector4) : ℝ :=
  P.p01 * Q.p23 + Q.p01 * P.p23
    - P.p02 * Q.p13 - Q.p02 * P.p13
    + P.p03 * Q.p12 + Q.p03 * P.p12

/-- Polarization of the native Zorn determinant on the active support. -/
def activeDetPolar (X Y : ActiveSector) : ℝ :=
  InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 (X + Y).1
    - InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X.1
    - InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 Y.1

/-- In Witt coordinates the Klein polar form is the cross-pairing between the
two three-dimensional isotropic halves. -/
theorem kleinPolar_wittKleinEquiv (X Y : WittCoordinates) :
    kleinPolar (wittKleinEquiv X) (wittKleinEquiv Y) =
      -(InfoGeometry.Canonical.ZornMatrix.dot X.1 Y.2
        + InfoGeometry.Canonical.ZornMatrix.dot Y.1 X.2) := by
  rcases X with ⟨x, y⟩
  rcases Y with ⟨u, v⟩
  simp [kleinPolar, wittKleinEquiv,
    InfoGeometry.Canonical.ZornMatrix.dot]
  ring

/-- The concrete active-support/Klein equivalence preserves the polarized
quadratic forms exactly. -/
theorem kleinPolar_activeKleinEquiv (X Y : ActiveSector) :
    kleinPolar (activeKleinEquiv X) (activeKleinEquiv Y) =
      activeDetPolar X Y := by
  unfold activeDetPolar
  rw [← kleinForm_activeKleinEquiv (X + Y),
    ← kleinForm_activeKleinEquiv X,
    ← kleinForm_activeKleinEquiv Y]
  rcases X with ⟨X, hX⟩
  rcases Y with ⟨Y, hY⟩
  simp [activeKleinEquiv, activeSectorEquiv, wittKleinEquiv,
    kleinPolar, kleinForm]
  ring

/-- The same polarized identity through the genuine linear equivalence. -/
theorem kleinPolar_activeKleinLinearEquiv (X Y : ActiveSector) :
    kleinPolar (activeKleinLinearEquiv X) (activeKleinLinearEquiv Y) =
      activeDetPolar X Y := by
  have hX : activeKleinLinearEquiv X = activeKleinEquiv X := by
    change activeKleinLinearEquiv.toEquiv X = activeKleinEquiv X
    rw [activeKleinLinearEquiv_toEquiv]
  have hY : activeKleinLinearEquiv Y = activeKleinEquiv Y := by
    change activeKleinLinearEquiv.toEquiv Y = activeKleinEquiv Y
    rw [activeKleinLinearEquiv_toEquiv]
  rw [hX, hY]
  exact kleinPolar_activeKleinEquiv X Y

abbrev ExteriorSquare := ⋀[ℝ]^2 Vec4

/-- Polarization of the transported exterior Klein form. -/
def exteriorKleinPolar (X Y : ExteriorSquare) : ℝ :=
  exteriorKleinForm (X + Y) - exteriorKleinForm X - exteriorKleinForm Y

theorem exteriorKleinPolar_activeExterior (X Y : ActiveSector) :
    exteriorKleinPolar (activeExteriorLinearEquiv X)
        (activeExteriorLinearEquiv Y) =
      activeDetPolar X Y := by
  unfold exteriorKleinPolar activeDetPolar
  rw [← activeExteriorLinearEquiv.map_add]
  rw [exteriorKleinForm_activeExterior (X + Y),
    exteriorKleinForm_activeExterior X,
    exteriorKleinForm_activeExterior Y]

/-- Opposite exponential weights on the two Witt halves.  This is the
quadratic active-support Cartan action; multiplication preservation is a
separate theorem and requires the traceless condition on the three weights. -/
def wittCartanFlow (k : Fin 3 → ℝ) (t : ℝ) :
    WittCoordinates ≃ₗ[ℝ] WittCoordinates where
  toFun xy :=
    (fun i => Real.exp (t * k i) * xy.1 i,
      fun i => Real.exp (-(t * k i)) * xy.2 i)
  invFun xy :=
    (fun i => Real.exp (-(t * k i)) * xy.1 i,
      fun i => Real.exp (t * k i) * xy.2 i)
  map_add' X Y := by
    ext i <;> simp <;> ring
  map_smul' r X := by
    ext i <;> simp <;> ring
  left_inv X := by
    apply Prod.ext <;> funext i <;> simp [Real.exp_neg]
  right_inv X := by
    apply Prod.ext <;> funext i <;> simp [Real.exp_neg]

@[simp] theorem wittCartanFlow_apply (k : Fin 3 → ℝ) (t : ℝ)
    (X : WittCoordinates) :
    wittCartanFlow k t X =
      (fun i => Real.exp (t * k i) * X.1 i,
        fun i => Real.exp (-(t * k i)) * X.2 i) :=
  rfl

theorem wittCartanFlow_preserves_wittKleinForm
    (k : Fin 3 → ℝ) (t : ℝ) (X : WittCoordinates) :
    kleinForm (wittKleinEquiv (wittCartanFlow k t X)) =
      kleinForm (wittKleinEquiv X) := by
  rw [kleinForm_wittKleinEquiv, kleinForm_wittKleinEquiv]
  simp [wittCartanFlow, InfoGeometry.Canonical.ZornMatrix.dot,
    Real.exp_neg]
  field_simp [Real.exp_ne_zero]

theorem wittCartanFlow_preserves_kleinPolar
    (k : Fin 3 → ℝ) (t : ℝ) (X Y : WittCoordinates) :
    kleinPolar (wittKleinEquiv (wittCartanFlow k t X))
        (wittKleinEquiv (wittCartanFlow k t Y)) =
      kleinPolar (wittKleinEquiv X) (wittKleinEquiv Y) := by
  rw [kleinPolar_wittKleinEquiv, kleinPolar_wittKleinEquiv]
  simp [wittCartanFlow, InfoGeometry.Canonical.ZornMatrix.dot,
    Real.exp_neg]
  field_simp [Real.exp_ne_zero]

@[simp] theorem wittCartanFlow_zero (k : Fin 3 → ℝ) (X : WittCoordinates) :
    wittCartanFlow k 0 X = X := by
  apply Prod.ext <;> funext i <;> simp [wittCartanFlow]

theorem wittCartanFlow_add (k : Fin 3 → ℝ) (s t : ℝ) (X : WittCoordinates) :
    wittCartanFlow k (s + t) X =
      wittCartanFlow k s (wittCartanFlow k t X) := by
  apply Prod.ext <;> funext i
  · simp [wittCartanFlow]
    rw [show (s + t) * k i = s * k i + t * k i by ring, Real.exp_add]
    ring
  · simp [wittCartanFlow]
    rw [show -((s + t) * k i) = -(s * k i) + -(t * k i) by ring,
      Real.exp_add]
    ring

@[simp] theorem wittCartanFlow_neg_apply (k : Fin 3 → ℝ) (t : ℝ)
    (X : WittCoordinates) :
    (wittCartanFlow k t).symm X = wittCartanFlow k (-t) X := by
  apply Prod.ext <;> funext i <;> simp [wittCartanFlow, Real.exp_neg]

end InfoGeometry.Lie.SplitOctonionAxialKleinPolar
