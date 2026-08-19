import Mathlib.Tactic

import InfoGeometry.Projective.Cl55NullBoundaryBridge
import InfoGeometry.Projective.NullBoundary

/-!
# Projective affine conformal closure at `O(5,5)` / `Pin(5,5)`

Finite algebraic core:
* split affine space `ℝ^(4,4)` has quadratic form `Q44`;
* its projective conformal closure is modeled by the null cone of `ℝ^(5,5)`;
* the standard affine chart embedding
  `x ↦ (x, (1-Q44 x)/2, (1+Q44 x)/2)` is null for `Q55`;
* elementary `O(5,5)` reflections preserve `Q55`;
* the spectral CPT map has fixed locus `Re(s)=1/2`.
-/

noncomputable section

namespace ProjectiveAffineConformalClosure55

open scoped ComplexConjugate
open InfoGeometry.Projective
open InfoGeometry.Projective.ProjectiveNullBoundaryDatum

/-- Split-octonionic affine coordinate model `ℝ^(4,4)`. -/
structure PACSplit44 where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  y0 : ℝ
  y1 : ℝ
  y2 : ℝ
  y3 : ℝ

/-- Ambient conformal coordinate model `ℝ^(5,5) = ℝ^(4,4) ⊕ ℝ^(1,1)`. -/
structure PACSplit55 where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  y0 : ℝ
  y1 : ℝ
  y2 : ℝ
  y3 : ℝ
  u : ℝ
  v : ℝ

/-- Split quadratic form of signature `(4,4)`. -/
def Q44 (x : PACSplit44) : ℝ :=
  x.x0^2 + x.x1^2 + x.x2^2 + x.x3^2 -
    (x.y0^2 + x.y1^2 + x.y2^2 + x.y3^2)

/-- Split quadratic form of signature `(5,5)`. -/
def Q55 (X : PACSplit55) : ℝ :=
  X.x0^2 + X.x1^2 + X.x2^2 + X.x3^2 + X.u^2 -
    (X.y0^2 + X.y1^2 + X.y2^2 + X.y3^2 + X.v^2)

/-- Affine conformal embedding into the projective null cone. -/
def conformalEmbed44to55 (x : PACSplit44) : PACSplit55 where
  x0 := x.x0
  x1 := x.x1
  x2 := x.x2
  x3 := x.x3
  y0 := x.y0
  y1 := x.y1
  y2 := x.y2
  y3 := x.y3
  u := (1 - Q44 x) / 2
  v := (1 + Q44 x) / 2

/-- The affine chart lands on the null cone of `ℝ^(5,5)`. -/
theorem conformalEmbed44to55_null (x : PACSplit44) :
    Q55 (conformalEmbed44to55 x) = 0 := by
  unfold Q55 conformalEmbed44to55 Q44
  ring

@[simp]
theorem conformalEmbed44to55_affine_gauge (x : PACSplit44) :
    (conformalEmbed44to55 x).u + (conformalEmbed44to55 x).v = 1 := by
  unfold conformalEmbed44to55
  ring

@[simp]
theorem conformalEmbed44to55_complementary_gauge (x : PACSplit44) :
    (conformalEmbed44to55 x).u - (conformalEmbed44to55 x).v = -(Q44 x) := by
  unfold conformalEmbed44to55
  ring

/-- The base `(4,4)` coordinates of an ambient PAC point. -/
def pac55Base44 (X : PACSplit55) : PACSplit44 where
  x0 := X.x0
  x1 := X.x1
  x2 := X.x2
  x3 := X.x3
  y0 := X.y0
  y1 := X.y1
  y2 := X.y2
  y3 := X.y3

theorem Q55_eq_Q44_of_gauge_zero (X : PACSplit55)
    (hGauge : X.u + X.v = 0) :
    Q55 X = Q44 (pac55Base44 X) := by
  unfold Q55 Q44 pac55Base44
  have hv : X.v = -X.u := by linarith
  rw [hv]
  ring

theorem Q55_eq_zero_iff_Q44_eq_zero_of_gauge_zero (X : PACSplit55)
    (hGauge : X.u + X.v = 0) :
    Q55 X = 0 ↔ Q44 (pac55Base44 X) = 0 := by
  rw [Q55_eq_Q44_of_gauge_zero X hGauge]

theorem conformal_boundary_null_iff_base_null (X : PACSplit55)
    (hGauge : X.u + X.v = 0) :
    Q55 X = 0 ↔ Q44 (pac55Base44 X) = 0 := by
  exact Q55_eq_zero_iff_Q44_eq_zero_of_gauge_zero X hGauge

/-- Scalar multiplication in the ambient projective space. -/
def smul55 (a : ℝ) (X : PACSplit55) : PACSplit55 where
  x0 := a * X.x0
  x1 := a * X.x1
  x2 := a * X.x2
  x3 := a * X.x3
  y0 := a * X.y0
  y1 := a * X.y1
  y2 := a * X.y2
  y3 := a * X.y3
  u := a * X.u
  v := a * X.v

@[simp] theorem smul55_one (X : PACSplit55) : smul55 1 X = X := by
  cases X
  simp [smul55]

theorem smul55_smul (a b : ℝ) (X : PACSplit55) :
    smul55 a (smul55 b X) = smul55 (a * b) X := by
  cases X
  simp only [smul55]
  congr 1 <;> ring

/-- Projective same-line relation in the ambient conformal space. -/
def sameProjectiveLine55 (X Y : PACSplit55) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ Y = smul55 a X

/-- Projective equivalence is reflexive. -/
theorem sameProjectiveLine55_refl (X : PACSplit55) :
    sameProjectiveLine55 X X := by
  refine ⟨1, by norm_num, ?_⟩
  cases X
  simp [smul55]

theorem sameProjectiveLine55_symm {X Y : PACSplit55}
    (h : sameProjectiveLine55 X Y) :
    sameProjectiveLine55 Y X := by
  rcases h with ⟨a, ha, rfl⟩
  refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
  rw [smul55_smul, inv_mul_cancel₀ ha, smul55_one]

theorem sameProjectiveLine55_trans {X Y Z : PACSplit55}
    (hXY : sameProjectiveLine55 X Y)
    (hYZ : sameProjectiveLine55 Y Z) :
    sameProjectiveLine55 X Z := by
  rcases hXY with ⟨a, ha, rfl⟩
  rcases hYZ with ⟨b, hb, rfl⟩
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  rw [smul55_smul]

def projectiveSetoid55 : Setoid PACSplit55 where
  r := sameProjectiveLine55
  iseqv := {
    refl := sameProjectiveLine55_refl
    symm := sameProjectiveLine55_symm
    trans := sameProjectiveLine55_trans
  }

/-- The actual projective carrier of the split conformal ambient space. -/
def projectiveMk55 (X : PACSplit55) : Quotient projectiveSetoid55 :=
  Quotient.mk projectiveSetoid55 X

/-- The null cone condition is invariant under nonzero projective rescaling. -/
theorem Q55_smul (a : ℝ) (X : PACSplit55) :
    Q55 (smul55 a X) = a^2 * Q55 X := by
  cases X
  unfold Q55 smul55
  ring

def pacSplit55Zero : PACSplit55 where
  x0 := 0
  x1 := 0
  x2 := 0
  x3 := 0
  y0 := 0
  y1 := 0
  y2 := 0
  y3 := 0
  u := 0
  v := 0

/-! ## Explicit identification with the native `V55` carrier -/

/-- Coordinate-preserving map from the local PAC record to native `V55`. -/
def pacSplit55ToNativeV55 (X : PACSplit55) : InfoGeometry.Clifford.Clifford55.V55 :=
  (![X.x0, X.x1, X.x2, X.x3, X.u],
    ![X.y0, X.y1, X.y2, X.y3, X.v])

/-- Coordinate-preserving inverse map from native `V55` to the PAC record. -/
def nativeV55ToPacSplit55 (v : InfoGeometry.Clifford.Clifford55.V55) : PACSplit55 where
  x0 := v.1 0
  x1 := v.1 1
  x2 := v.1 2
  x3 := v.1 3
  y0 := v.2 0
  y1 := v.2 1
  y2 := v.2 2
  y3 := v.2 3
  u := v.1 4
  v := v.2 4

@[simp]
theorem nativeV55ToPacSplit55_pacSplit55ToNativeV55
    (X : PACSplit55) :
    nativeV55ToPacSplit55 (pacSplit55ToNativeV55 X) = X := by
  cases X
  rfl

@[simp]
theorem pacSplit55ToNativeV55_nativeV55ToPacSplit55
    (v : InfoGeometry.Clifford.Clifford55.V55) :
    pacSplit55ToNativeV55 (nativeV55ToPacSplit55 v) = v := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

theorem nativeQ55_pacSplit55ToNativeV55 (X : PACSplit55) :
    InfoGeometry.Clifford.Clifford55.Q55
        (pacSplit55ToNativeV55 X) = Q55 X := by
  rw [InfoGeometry.Clifford.Clifford55.Q55_apply]
  simp [pacSplit55ToNativeV55, Q55, Fin.sum_univ_succ]
  ring

theorem pacSplit55ToNativeV55_smul (a : ℝ) (X : PACSplit55) :
    pacSplit55ToNativeV55 (smul55 a X) =
      a • pacSplit55ToNativeV55 X := by
  cases X
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem smul55_ne_zero_of_unit
    (u : ℝˣ) (X : PACSplit55) (hX : X ≠ pacSplit55Zero) :
    smul55 (u : ℝ) X ≠ pacSplit55Zero := by
  intro hzero
  apply hX
  cases X
  have hu : (u : ℝ) ≠ 0 := Units.ne_zero u
  simp [smul55, pacSplit55Zero, mul_eq_zero, hu] at hzero ⊢
  exact hzero

/-- A nonzero representative is not the zero projective class. -/
theorem projectiveMk55_ne_zero_class_of_ne_zero
    {X : PACSplit55} (hX : X ≠ pacSplit55Zero) :
    projectiveMk55 X ≠ projectiveMk55 pacSplit55Zero := by
  intro h
  rcases Quotient.exact h with ⟨a, ha, hscale⟩
  apply hX
  cases X
  simp [smul55, pacSplit55Zero, ha] at hscale ⊢
  exact hscale

/-! ## Generic projective-null owner for the PAC carrier -/

noncomputable def projectiveNullBoundaryDatum55 :
    ProjectiveNullBoundaryDatum ℝ ℝ PACSplit55 where
  q := Q55
  zero := pacSplit55Zero
  scale := fun u X => smul55 (u : ℝ) X
  scale_one := by
    intro X
    simp
  scale_mul := by
    intro u v X
    simp [smul55_smul]
  null_scale := by
    intro u X
    constructor
    · intro h
      have hmul :
          (u : ℝ)^2 * Q55 X = 0 := by
        simpa [Q55_smul] using h
      rcases mul_eq_zero.mp hmul with husq | hq
      · exfalso
        have hu : (u : ℝ) = 0 := by
          nlinarith
        exact (Units.ne_zero u) hu
      · exact hq
    · intro h
      rw [Q55_smul, h]
      simp
  scale_ne_zero := by
    intro u X hX
    exact smul55_ne_zero_of_unit u X hX

/-- The coordinate equivalence is a genuine null-boundary morphism into the
native `Cl(5,5)` projective boundary datum. -/
noncomputable def pacToNativeBoundaryHom :
    ProjectiveNullBoundaryDatum.BoundaryHom
      projectiveNullBoundaryDatum55
      InfoGeometry.Projective.Cl55NullBoundaryBridge.datum where
  toFun := pacSplit55ToNativeV55
  map_zero := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_null := by
    intro X hX
    change Q55 X = 0 at hX
    change InfoGeometry.Clifford.Clifford55.Q55
        (pacSplit55ToNativeV55 X) = 0
    rw [nativeQ55_pacSplit55ToNativeV55, hX]
  map_ne_zero := by
    intro X hX hzero
    apply hX
    have hinv := congrArg nativeV55ToPacSplit55 hzero
    simpa [InfoGeometry.Projective.Cl55NullBoundaryBridge.datum]
      using hinv
  map_scale := by
    intro u X
    change pacSplit55ToNativeV55 (smul55 (u : ℝ) X) =
      (u : ℝ) • pacSplit55ToNativeV55 X
    exact pacSplit55ToNativeV55_smul (u : ℝ) X

noncomputable def pacToNativeBoundaryAction
    (X : ProjectiveNullBoundaryDatum.ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    InfoGeometry.Projective.Cl55NullBoundaryBridge.Boundary :=
  ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
    pacToNativeBoundaryHom X

theorem nativeV55ToPacSplit55_smul (a : ℝ) (v : InfoGeometry.Clifford.Clifford55.V55) :
    nativeV55ToPacSplit55 (a • v) =
      smul55 a (nativeV55ToPacSplit55 v) := by
  apply Function.LeftInverse.injective
    nativeV55ToPacSplit55_pacSplit55ToNativeV55
  calc
    pacSplit55ToNativeV55
        (nativeV55ToPacSplit55 (a • v)) = a • v := by
          simp
    _ = pacSplit55ToNativeV55
        (smul55 a (nativeV55ToPacSplit55 v)) := by
          rw [pacSplit55ToNativeV55_smul]
          simp

/-- The inverse coordinate map is also a genuine null-boundary morphism. -/
noncomputable def nativeToPacBoundaryHom :
    ProjectiveNullBoundaryDatum.BoundaryHom
      InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
      projectiveNullBoundaryDatum55 where
  toFun := nativeV55ToPacSplit55
  map_zero := by
    cases (0 : InfoGeometry.Clifford.Clifford55.V55)
    rfl
  map_null := by
    intro v hv
    have hQ := nativeQ55_pacSplit55ToNativeV55
      (nativeV55ToPacSplit55 v)
    rw [pacSplit55ToNativeV55_nativeV55ToPacSplit55] at hQ
    change Q55 (nativeV55ToPacSplit55 v) = 0
    rw [← hQ]
    exact hv
  map_ne_zero := by
    intro v hv hzero
    apply hv
    change nativeV55ToPacSplit55 v = pacSplit55Zero at hzero
    have hzero' := congrArg pacSplit55ToNativeV55 hzero
    have hzero_pac :
        pacSplit55ToNativeV55 pacSplit55Zero = (0 : InfoGeometry.Clifford.Clifford55.V55) := by
      apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
    have hzero'' : v = pacSplit55ToNativeV55 pacSplit55Zero := by
      simpa using hzero'
    rw [hzero_pac] at hzero''
    simpa [InfoGeometry.Projective.Cl55NullBoundaryBridge.datum]
      using hzero''
  map_scale := by
    intro u v
    exact nativeV55ToPacSplit55_smul (u : ℝ) v

noncomputable def nativeToPacBoundaryAction
    (X : InfoGeometry.Projective.Cl55NullBoundaryBridge.Boundary) :
    ProjectiveNullBoundaryDatum.ProjectiveNullBoundary projectiveNullBoundaryDatum55 :=
  ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
    nativeToPacBoundaryHom X

theorem pacToNativeBoundaryAction_left_inverse
    (X : ProjectiveNullBoundaryDatum.ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    nativeToPacBoundaryAction (pacToNativeBoundaryAction X) = X := by
  refine Quotient.inductionOn X ?_
  intro Z
  change ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
      nativeToPacBoundaryHom
      (ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
        pacToNativeBoundaryHom
        (ProjectiveNullBoundaryDatum.nullMk
          projectiveNullBoundaryDatum55 Z)) =
    ProjectiveNullBoundaryDatum.nullMk projectiveNullBoundaryDatum55 Z
  rw [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply Quotient.sound
  refine ⟨1, ?_⟩
  change smul55 1
      (nativeV55ToPacSplit55
        (pacSplit55ToNativeV55 Z.Z)) = Z.Z
  simp

theorem pacToNativeBoundaryAction_right_inverse
    (X : InfoGeometry.Projective.Cl55NullBoundaryBridge.Boundary) :
    pacToNativeBoundaryAction (nativeToPacBoundaryAction X) = X := by
  refine Quotient.inductionOn X ?_
  intro Z
  change ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
      pacToNativeBoundaryHom
      (ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
        nativeToPacBoundaryHom
        (ProjectiveNullBoundaryDatum.nullMk
          InfoGeometry.Projective.Cl55NullBoundaryBridge.datum Z)) =
    ProjectiveNullBoundaryDatum.nullMk
      InfoGeometry.Projective.Cl55NullBoundaryBridge.datum Z
  rw [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply Quotient.sound
  refine ⟨1, ?_⟩
  change (1 : ℝ) •
      pacSplit55ToNativeV55
        (nativeV55ToPacSplit55 Z.Z) = Z.Z
  simp

/-- Canonical equivalence between the local PAC quotient and the native
`Cl(5,5)` projective null boundary. -/
noncomputable def pacNativeProjectiveBoundaryEquiv :
    ProjectiveNullBoundaryDatum.ProjectiveNullBoundary projectiveNullBoundaryDatum55 ≃ InfoGeometry.Projective.Cl55NullBoundaryBridge.Boundary where
  toFun := pacToNativeBoundaryAction
  invFun := nativeToPacBoundaryAction
  left_inv := pacToNativeBoundaryAction_left_inverse
  right_inv := pacToNativeBoundaryAction_right_inverse

def genericProjectiveNullMk55 (Z : ProjectiveNullBoundaryDatum.NullRep projectiveNullBoundaryDatum55) :
    ProjectiveNullBoundaryDatum.ProjectiveNullBoundary projectiveNullBoundaryDatum55 :=
  ProjectiveNullBoundaryDatum.nullMk projectiveNullBoundaryDatum55 Z

/-- The nonzero null part of the bespoke projective carrier.  The separate
nonzero condition excludes the zero projective class, which is not present in
the generic `NullRep` quotient.
-/
def ProjectiveNonzeroNull55 : Type :=
  {P : Quotient projectiveSetoid55 //
    ∃ X : PACSplit55,
      projectiveMk55 X = P ∧ Q55 X = 0 ∧ X ≠ pacSplit55Zero}

noncomputable def genericNullBoundary_to_projectiveNonzeroNull55 :
    ProjectiveNullBoundaryDatum.ProjectiveNullBoundary projectiveNullBoundaryDatum55 → ProjectiveNonzeroNull55 :=
  Quotient.lift
    (fun Z : ProjectiveNullBoundaryDatum.NullRep projectiveNullBoundaryDatum55 =>
      (⟨projectiveMk55 Z.Z,
        ⟨Z.Z, rfl, Z.null, Z.nonzero⟩⟩ : ProjectiveNonzeroNull55))
    (by
      intro X Y hXY
      rcases hXY with ⟨u, hu⟩
      apply Subtype.ext
      apply Quotient.sound
      refine ⟨(u : ℝ), Units.ne_zero u, ?_⟩
      simpa [projectiveNullBoundaryDatum55] using hu.symm)

theorem genericNullBoundary_to_projectiveNonzeroNull55_injective :
    Function.Injective genericNullBoundary_to_projectiveNonzeroNull55 := by
  intro X Y hXY
  refine Quotient.inductionOn₂ X Y ?_ hXY
  intro X Y hXY
  have hproj : projectiveMk55 X.Z = projectiveMk55 Y.Z :=
    congrArg Subtype.val hXY
  have hray : sameProjectiveLine55 X.Z Y.Z :=
    Quotient.exact hproj
  rcases hray with ⟨a, ha, hY⟩
  apply Quotient.sound
  refine ⟨Units.mk0 a ha, ?_⟩
  change smul55 a X.Z = Y.Z
  exact hY.symm

noncomputable def projectiveNonzeroNull55_representative
    (P : ProjectiveNonzeroNull55) : PACSplit55 :=
  Classical.choose P.property

theorem projectiveNonzeroNull55_representative_projective
    (P : ProjectiveNonzeroNull55) :
    projectiveMk55 (projectiveNonzeroNull55_representative P) = P.1 :=
  (Classical.choose_spec P.property).1

theorem projectiveNonzeroNull55_representative_null
    (P : ProjectiveNonzeroNull55) :
    Q55 (projectiveNonzeroNull55_representative P) = 0 :=
  (Classical.choose_spec P.property).2.1

theorem projectiveNonzeroNull55_representative_nonzero
    (P : ProjectiveNonzeroNull55) :
    projectiveNonzeroNull55_representative P ≠ pacSplit55Zero :=
  (Classical.choose_spec P.property).2.2

noncomputable def projectiveNonzeroNull55_to_genericNullBoundary :
    ProjectiveNonzeroNull55 → ProjectiveNullBoundaryDatum.ProjectiveNullBoundary projectiveNullBoundaryDatum55 :=
  fun P =>
    genericProjectiveNullMk55
      ⟨projectiveNonzeroNull55_representative P,
        projectiveNonzeroNull55_representative_null P,
        projectiveNonzeroNull55_representative_nonzero P⟩

theorem genericNullBoundary_to_projectiveNonzeroNull55_right_inverse
    (P : ProjectiveNonzeroNull55) :
    genericNullBoundary_to_projectiveNonzeroNull55
        (projectiveNonzeroNull55_to_genericNullBoundary P) = P := by
  apply Subtype.ext
  exact projectiveNonzeroNull55_representative_projective P

theorem projectiveNonzeroNull55_to_genericNullBoundary_left_inverse
    (Z : ProjectiveNullBoundaryDatum.ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    projectiveNonzeroNull55_to_genericNullBoundary
        (genericNullBoundary_to_projectiveNonzeroNull55 Z) = Z := by
  apply genericNullBoundary_to_projectiveNonzeroNull55_injective
  exact genericNullBoundary_to_projectiveNonzeroNull55_right_inverse
    (genericNullBoundary_to_projectiveNonzeroNull55 Z)

noncomputable def genericNullBoundary_projectiveNonzeroNull55_equiv :
    ProjectiveNullBoundaryDatum.ProjectiveNullBoundary projectiveNullBoundaryDatum55 ≃ ProjectiveNonzeroNull55 where
  toFun := genericNullBoundary_to_projectiveNonzeroNull55
  invFun := projectiveNonzeroNull55_to_genericNullBoundary
  left_inv := projectiveNonzeroNull55_to_genericNullBoundary_left_inverse
  right_inv := genericNullBoundary_to_projectiveNonzeroNull55_right_inverse

/-- Projective rescaling preserves nullity. -/
theorem projective_rescale_preserves_null
    {X Y : PACSplit55} (h : sameProjectiveLine55 X Y) (hX : Q55 X = 0) :
    Q55 Y = 0 := by
  rcases h with ⟨a, _ha, rfl⟩
  rw [Q55_smul, hX]
  ring

theorem sameProjectiveLine55_null_iff {X Y : PACSplit55}
    (h : sameProjectiveLine55 X Y) :
    Q55 X = 0 ↔ Q55 Y = 0 := by
  constructor
  · exact projective_rescale_preserves_null h
  · exact projective_rescale_preserves_null (sameProjectiveLine55_symm h)

/-- Nullity is a well-defined predicate on the projective quotient. -/
def projectiveNull55 : Quotient projectiveSetoid55 → Prop :=
  Quotient.lift (fun X => Q55 X = 0) (by
    intro X Y h
    apply propext
    exact sameProjectiveLine55_null_iff h)

/-- A concrete `O(5,5)`-type reflection: flip the added positive coordinate. -/
def reflectU (X : PACSplit55) : PACSplit55 where
  x0 := X.x0; x1 := X.x1; x2 := X.x2; x3 := X.x3
  y0 := X.y0; y1 := X.y1; y2 := X.y2; y3 := X.y3
  u := -X.u; v := X.v

/-- A concrete `O(5,5)`-type reflection: flip the added negative coordinate. -/
def reflectV (X : PACSplit55) : PACSplit55 where
  x0 := X.x0; x1 := X.x1; x2 := X.x2; x3 := X.x3
  y0 := X.y0; y1 := X.y1; y2 := X.y2; y3 := X.y3
  u := X.u; v := -X.v

@[simp] theorem reflectU_involutive (X : PACSplit55) :
    reflectU (reflectU X) = X := by
  cases X
  simp [reflectU]

@[simp] theorem reflectV_involutive (X : PACSplit55) :
    reflectV (reflectV X) = X := by
  cases X
  simp [reflectV]

@[simp] theorem reflectU_reflectV_commute (X : PACSplit55) :
    reflectU (reflectV X) = reflectV (reflectU X) := by
  cases X
  rfl

theorem reflectU_smul (a : ℝ) (X : PACSplit55) :
    reflectU (smul55 a X) = smul55 a (reflectU X) := by
  cases X
  simp [reflectU, smul55]

theorem reflectV_smul (a : ℝ) (X : PACSplit55) :
    reflectV (smul55 a X) = smul55 a (reflectV X) := by
  cases X
  simp [reflectV, smul55]

def reflectUProjective : Quotient projectiveSetoid55 → Quotient projectiveSetoid55 :=
  Quotient.lift (fun X => projectiveMk55 (reflectU X)) (by
    intro X Y hXY
    rcases hXY with ⟨a, ha, hXY⟩
    change projectiveMk55 (reflectU X) = projectiveMk55 (reflectU Y)
    apply Quotient.sound
    refine ⟨a, ha, ?_⟩
    rw [hXY, reflectU_smul])

def reflectVProjective : Quotient projectiveSetoid55 → Quotient projectiveSetoid55 :=
  Quotient.lift (fun X => projectiveMk55 (reflectV X)) (by
    intro X Y hXY
    rcases hXY with ⟨a, ha, hXY⟩
    change projectiveMk55 (reflectV X) = projectiveMk55 (reflectV Y)
    apply Quotient.sound
    refine ⟨a, ha, ?_⟩
    rw [hXY, reflectV_smul])

/-- The `u` reflection preserves the split `(5,5)` quadratic form. -/
theorem reflectU_preserves_Q55 (X : PACSplit55) :
    Q55 (reflectU X) = Q55 X := by
  cases X
  unfold Q55 reflectU
  ring

/-- The `v` reflection preserves the split `(5,5)` quadratic form. -/
theorem reflectV_preserves_Q55 (X : PACSplit55) :
    Q55 (reflectV X) = Q55 X := by
  cases X
  unfold Q55 reflectV
  ring

/-- Reflections preserve the projective null cone. -/
theorem reflectU_preserves_null (X : PACSplit55) (hX : Q55 X = 0) :
    Q55 (reflectU X) = 0 := by
  rw [reflectU_preserves_Q55, hX]

theorem reflectV_preserves_null (X : PACSplit55) (hX : Q55 X = 0) :
    Q55 (reflectV X) = 0 := by
  rw [reflectV_preserves_Q55, hX]

theorem reflectUProjective_preserves_null (P : Quotient projectiveSetoid55)
    (hP : projectiveNull55 P) :
    projectiveNull55 (reflectUProjective P) := by
  revert hP
  refine Quotient.inductionOn P ?_
  intro X hX
  change Q55 X = 0 at hX
  change Q55 (reflectU X) = 0
  rw [reflectU_preserves_Q55, hX]

theorem reflectVProjective_preserves_null (P : Quotient projectiveSetoid55)
    (hP : projectiveNull55 P) :
    projectiveNull55 (reflectVProjective P) := by
  revert hP
  refine Quotient.inductionOn P ?_
  intro X hX
  change Q55 X = 0 at hX
  change Q55 (reflectV X) = 0
  rw [reflectV_preserves_Q55, hX]

@[simp] theorem reflectUProjective_involutive (P : Quotient projectiveSetoid55) :
    reflectUProjective (reflectUProjective P) = P := by
  refine Quotient.inductionOn P ?_
  intro X
  change projectiveMk55 (reflectU (reflectU X)) = projectiveMk55 X
  cases X
  simp [reflectU]

@[simp] theorem reflectVProjective_involutive (P : Quotient projectiveSetoid55) :
    reflectVProjective (reflectVProjective P) = P := by
  refine Quotient.inductionOn P ?_
  intro X
  change projectiveMk55 (reflectV (reflectV X)) = projectiveMk55 X
  cases X
  simp [reflectV]

/-- The `u` reflection as an involutive projective equivalence. -/
def reflectUProjectiveEquiv : Quotient projectiveSetoid55 ≃ Quotient projectiveSetoid55 where
  toFun := reflectUProjective
  invFun := reflectUProjective
  left_inv := reflectUProjective_involutive
  right_inv := reflectUProjective_involutive

/-- The `v` reflection as an involutive projective equivalence. -/
def reflectVProjectiveEquiv : Quotient projectiveSetoid55 ≃ Quotient projectiveSetoid55 where
  toFun := reflectVProjective
  invFun := reflectVProjective
  left_inv := reflectVProjective_involutive
  right_inv := reflectVProjective_involutive

theorem reflectUProjective_commute_reflectVProjective (P : Quotient projectiveSetoid55) :
    reflectUProjective (reflectVProjective P) =
      reflectVProjective (reflectUProjective P) := by
  refine Quotient.inductionOn P ?_
  intro X
  change projectiveMk55 (reflectU (reflectV X)) =
    projectiveMk55 (reflectV (reflectU X))
  cases X
  rfl

theorem reflectUProjectiveEquiv_commute_reflectVProjectiveEquiv :
    reflectUProjectiveEquiv * reflectVProjectiveEquiv =
      reflectVProjectiveEquiv * reflectUProjectiveEquiv := by
  apply Equiv.ext
  intro P
  exact reflectUProjective_commute_reflectVProjective P

/-! ## Native projective null-preserving symmetry closure -/

/-- An ambient projective permutation preserves the null boundary in both
directions.  The `↔` is essential: it makes the predicate closed under
permutation inverses, rather than recording only a one-way readout.
-/
def preservesProjectiveNull (e : Equiv.Perm (Quotient projectiveSetoid55)) : Prop :=
  ∀ P, projectiveNull55 (e P) ↔ projectiveNull55 P

/-- The projective permutations preserving the null boundary form a native
subgroup of the full permutation group.
-/
def projectiveNullPreservingPermSubgroup :
    Subgroup (Equiv.Perm (Quotient projectiveSetoid55)) where
  carrier := {e | preservesProjectiveNull e}
  one_mem' := by
    intro P
    simp
  mul_mem' := by
    intro e f he hf P
    change projectiveNull55 (e (f P)) ↔ projectiveNull55 P
    exact (he (f P)).trans (hf P)
  inv_mem' := by
    intro e he P
    change projectiveNull55 (e⁻¹ P) ↔ projectiveNull55 P
    have h := he (e⁻¹ P)
    simpa using h.symm

theorem reflectUProjective_preserves_null_iff (P : Quotient projectiveSetoid55) :
    projectiveNull55 (reflectUProjective P) ↔ projectiveNull55 P := by
  constructor
  · intro h
    have h' := reflectUProjective_preserves_null
      (reflectUProjective P) h
    simpa using h'
  · exact reflectUProjective_preserves_null P

theorem reflectVProjective_preserves_null_iff (P : Quotient projectiveSetoid55) :
    projectiveNull55 (reflectVProjective P) ↔ projectiveNull55 P := by
  constructor
  · intro h
    have h' := reflectVProjective_preserves_null
      (reflectVProjective P) h
    simpa using h'
  · exact reflectVProjective_preserves_null P

theorem reflectUProjectiveEquiv_mem_nullPreservingSubgroup :
    reflectUProjectiveEquiv ∈ projectiveNullPreservingPermSubgroup := by
  intro P
  simpa [reflectUProjectiveEquiv, preservesProjectiveNull] using
    reflectUProjective_preserves_null_iff P

theorem reflectVProjectiveEquiv_mem_nullPreservingSubgroup :
    reflectVProjectiveEquiv ∈ projectiveNullPreservingPermSubgroup := by
  intro P
  simpa [reflectVProjectiveEquiv, preservesProjectiveNull] using
    reflectVProjective_preserves_null_iff P

/-- The subgroup generated by the two concrete conformal reflections is a
null-boundary-preserving projective symmetry group.
-/
def projectiveNullReflectionGroup :
    Subgroup (Equiv.Perm (Quotient projectiveSetoid55)) :=
  Subgroup.closure
    {e | e = reflectUProjectiveEquiv ∨ e = reflectVProjectiveEquiv}

theorem projectiveNullReflectionGroup_le_nullPreserving :
    projectiveNullReflectionGroup ≤
      projectiveNullPreservingPermSubgroup := by
  refine (Subgroup.closure_le _).2 ?_
  intro e he
  rcases he with rfl | rfl
  · exact reflectUProjectiveEquiv_mem_nullPreservingSubgroup
  · exact reflectVProjectiveEquiv_mem_nullPreservingSubgroup

theorem projectiveNullReflectionGroup_preserves_null
    {e : Equiv.Perm (Quotient projectiveSetoid55)}
    (he : e ∈ projectiveNullReflectionGroup) (P : Quotient projectiveSetoid55) :
    projectiveNull55 (e P) ↔ projectiveNull55 P := by
  exact projectiveNullReflectionGroup_le_nullPreserving he P

/-! ## Native permutation representation of the projective symmetry group -/

/-- The concrete reflection closure acts on the full projective carrier by
native permutations.  This is the group-level action surface, rather than a
pointwise packet of reflection identities.
-/
noncomputable def projectiveNullReflectionRepresentation :
    projectiveNullReflectionGroup →* Equiv.Perm (Quotient projectiveSetoid55) :=
  Subgroup.subtype projectiveNullReflectionGroup

theorem projectiveNullReflectionRepresentation_preserves_null
    (g : projectiveNullReflectionGroup) (P : Quotient projectiveSetoid55)
    (hP : projectiveNull55 P) :
    projectiveNull55
        (projectiveNullReflectionRepresentation g P) := by
  change projectiveNull55 (g.1 P)
  exact (projectiveNullReflectionGroup_preserves_null g.2 P).2 hP

theorem projectiveNullReflectionRepresentation_injective :
    Function.Injective projectiveNullReflectionRepresentation := by
  intro g h hgh
  apply Subtype.ext
  exact hgh

/-! The permutation representation is also exposed as the native Mathlib
`MulAction` on the full projective carrier. -/

noncomputable instance projectiveNullReflectionGroupProjectiveMulAction :
    MulAction projectiveNullReflectionGroup (Quotient projectiveSetoid55) where
  smul := fun g P => projectiveNullReflectionRepresentation g P
  one_smul := by
    intro P
    exact congrArg (fun e : Equiv.Perm (Quotient projectiveSetoid55) => e P)
      projectiveNullReflectionRepresentation.map_one
  mul_smul := by
    intro g h P
    change projectiveNullReflectionRepresentation (g * h) P =
      projectiveNullReflectionRepresentation g
        (projectiveNullReflectionRepresentation h P)
    rw [projectiveNullReflectionRepresentation.map_mul]
    rfl

theorem projectiveNullReflectionGroup_smul_preserves_null
    (g : projectiveNullReflectionGroup) (P : Quotient projectiveSetoid55)
    (hP : projectiveNull55 P) :
    projectiveNull55 (g • P) := by
  change projectiveNull55
    (projectiveNullReflectionRepresentation g P)
  exact projectiveNullReflectionRepresentation_preserves_null g P hP

/-! ## Restricted nonzero-null action -/

/-- The zero projective class of the bespoke quotient. -/
def projectiveZeroClass55 : Quotient projectiveSetoid55 :=
  projectiveMk55 pacSplit55Zero

@[simp]
theorem reflectUProjective_zeroClass55 :
    reflectUProjective projectiveZeroClass55 = projectiveZeroClass55 := by
  change projectiveMk55 (reflectU pacSplit55Zero) =
    projectiveMk55 pacSplit55Zero
  simp [reflectU, pacSplit55Zero]

@[simp]
theorem reflectVProjective_zeroClass55 :
    reflectVProjective projectiveZeroClass55 = projectiveZeroClass55 := by
  change projectiveMk55 (reflectV pacSplit55Zero) =
    projectiveMk55 pacSplit55Zero
  simp [reflectV, pacSplit55Zero]

/-- Projective permutations fixing the zero class form a subgroup. -/
def projectiveZeroClassPreservingSubgroup :
    Subgroup (Equiv.Perm (Quotient projectiveSetoid55)) where
  carrier := {e | e projectiveZeroClass55 = projectiveZeroClass55}
  one_mem' := by simp
  mul_mem' := by
    intro e f he hf
    change e (f projectiveZeroClass55) = projectiveZeroClass55
    rw [hf, he]
  inv_mem' := by
    intro e he
    change e⁻¹ projectiveZeroClass55 = projectiveZeroClass55
    simpa using (congrArg (fun P => e.symm P) he).symm

theorem projectiveNullReflectionGroup_le_zeroClassPreserving :
    projectiveNullReflectionGroup ≤
      projectiveZeroClassPreservingSubgroup := by
  refine (Subgroup.closure_le _).2 ?_
  intro e he
  rcases he with rfl | rfl
  · change reflectUProjectiveEquiv projectiveZeroClass55 =
      projectiveZeroClass55
    simp [reflectUProjectiveEquiv]
  · change reflectVProjectiveEquiv projectiveZeroClass55 =
      projectiveZeroClass55
    simp [reflectVProjectiveEquiv]

theorem projectiveNonzeroNull55_null
    (P : ProjectiveNonzeroNull55) :
    projectiveNull55 P.1 := by
  rcases P.property with ⟨X, hP, hnull, hne⟩
  rw [← hP]
  change Q55 X = 0
  exact hnull

theorem projectiveNonzeroNull55_ne_zeroClass
    (P : ProjectiveNonzeroNull55) :
    P.1 ≠ projectiveZeroClass55 := by
  intro h
  rcases P.property with ⟨X, hP, _hnull, hne⟩
  apply projectiveMk55_ne_zero_class_of_ne_zero hne
  exact hP.trans h

/-- A reflection-group element preserves the restricted nonzero-null carrier. -/
noncomputable def restrictedProjectiveNullMap
    (g : projectiveNullReflectionGroup)
    (P : ProjectiveNonzeroNull55) : ProjectiveNonzeroNull55 := by
  have hnull :
      projectiveNull55 (g.1 P.1) := by
    exact
      (projectiveNullReflectionGroup_preserves_null g.2 P.1).2
        (projectiveNonzeroNull55_null P)
  have hzero :
      g.1 P.1 ≠ projectiveZeroClass55 := by
    intro h
    have hinv := congrArg (fun P => g.val.symm P) h
    have hzero_inv :
        g.val.symm projectiveZeroClass55 = projectiveZeroClass55 := by
      have hg_inv : g.val.symm ∈ projectiveNullReflectionGroup :=
        projectiveNullReflectionGroup.inv_mem g.2
      have hzero_mem :=
        projectiveNullReflectionGroup_le_zeroClassPreserving hg_inv
      exact hzero_mem
    have hPzero : P.1 = projectiveZeroClass55 := by
      simpa [hzero_inv] using hinv
    exact projectiveNonzeroNull55_ne_zeroClass P hPzero
  exact ⟨g.1 P.1, by
    obtain ⟨X, hRep⟩ := Quotient.exists_rep (g.1 P.1)
    rw [← hRep] at hnull ⊢
    change Q55 X = 0 at hnull
    have hXnonzero : X ≠ pacSplit55Zero := by
      intro hXzero
      apply hzero
      rw [← hRep, hXzero]
      rfl
    exact ⟨X, rfl, hnull, hXnonzero⟩⟩

/-! The restricted action is the native permutation representation on the
nonzero null carrier, with the group law inherited from `Equiv.Perm`. -/
noncomputable def restrictedProjectiveNullRepresentation :
    projectiveNullReflectionGroup →*
      Equiv.Perm (ProjectiveNonzeroNull55) where
  toFun := fun g =>
    { toFun := restrictedProjectiveNullMap g
      invFun := restrictedProjectiveNullMap g⁻¹
      left_inv := by
        intro P
        apply Subtype.ext
        change g.1.symm (g.1 P.1) = P.1
        exact g.1.left_inv P.1
      right_inv := by
        intro P
        apply Subtype.ext
        change g.1 (g.1.symm P.1) = P.1
        exact g.1.right_inv P.1 }
  map_one' := by
    ext P
    apply Subtype.ext
    rfl
  map_mul' := by
    intro g h
    ext P
    apply Subtype.ext
    rfl

@[simp]
theorem restrictedProjectiveNullMap_one
    (P : ProjectiveNonzeroNull55) :
    restrictedProjectiveNullMap 1 P = P := by
  apply Subtype.ext
  rfl

@[simp]
theorem restrictedProjectiveNullMap_mul
    (g h : projectiveNullReflectionGroup)
    (P : ProjectiveNonzeroNull55) :
    restrictedProjectiveNullMap (g * h) P =
      restrictedProjectiveNullMap g
        (restrictedProjectiveNullMap h P) := by
  apply Subtype.ext
  rfl

noncomputable instance projectiveNullReflectionGroupNonzeroNullMulAction :
    MulAction projectiveNullReflectionGroup ProjectiveNonzeroNull55 where
  smul := restrictedProjectiveNullMap
  one_smul := restrictedProjectiveNullMap_one
  mul_smul := restrictedProjectiveNullMap_mul

/-! ## Transport to the generic null-boundary quotient -/

/-- The restricted reflection action transported across the canonical
equivalence with the generic projective-null quotient. -/
noncomputable def genericProjectiveNullReflectionRepresentation :
    projectiveNullReflectionGroup →*
      Equiv.Perm
        (ProjectiveNullBoundaryDatum.ProjectiveNullBoundary
          projectiveNullBoundaryDatum55) where
  toFun := fun g =>
    genericNullBoundary_projectiveNonzeroNull55_equiv.trans
      ((restrictedProjectiveNullRepresentation g).trans
        genericNullBoundary_projectiveNonzeroNull55_equiv.symm)
  map_one' := by
    ext X
    change genericNullBoundary_projectiveNonzeroNull55_equiv.symm
        (restrictedProjectiveNullRepresentation 1
          (genericNullBoundary_projectiveNonzeroNull55_equiv X)) = X
    rw [restrictedProjectiveNullRepresentation.map_one]
    exact genericNullBoundary_projectiveNonzeroNull55_equiv.symm_apply_apply X
  map_mul' := by
    intro g h
    ext X
    change genericNullBoundary_projectiveNonzeroNull55_equiv.symm
        (restrictedProjectiveNullRepresentation (g * h)
          (genericNullBoundary_projectiveNonzeroNull55_equiv X)) =
      genericNullBoundary_projectiveNonzeroNull55_equiv.symm
        (restrictedProjectiveNullRepresentation g
          (genericNullBoundary_projectiveNonzeroNull55_equiv
            (genericNullBoundary_projectiveNonzeroNull55_equiv.symm
              (restrictedProjectiveNullRepresentation h
                (genericNullBoundary_projectiveNonzeroNull55_equiv X)))))
    rw [restrictedProjectiveNullRepresentation.map_mul]
    rw [Equiv.Perm.mul_apply]
    rw [genericNullBoundary_projectiveNonzeroNull55_equiv.apply_symm_apply]

noncomputable instance projectiveNullReflectionGroupGenericBoundaryMulAction :
    MulAction projectiveNullReflectionGroup
      (ProjectiveNullBoundaryDatum.ProjectiveNullBoundary
        projectiveNullBoundaryDatum55) where
  smul := fun g X => genericProjectiveNullReflectionRepresentation g X
  one_smul := by
    intro X
    exact congrArg
      (fun e : Equiv.Perm
        (ProjectiveNullBoundaryDatum.ProjectiveNullBoundary
          projectiveNullBoundaryDatum55) => e X)
      genericProjectiveNullReflectionRepresentation.map_one
  mul_smul := by
    intro g h X
    change genericProjectiveNullReflectionRepresentation (g * h) X =
      genericProjectiveNullReflectionRepresentation g
        (genericProjectiveNullReflectionRepresentation h X)
    rw [genericProjectiveNullReflectionRepresentation.map_mul]
    rfl

theorem genericProjectiveNullReflectionRepresentation_conjugates
    (g : projectiveNullReflectionGroup)
    (X : ProjectiveNullBoundaryDatum.ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    genericProjectiveNullReflectionRepresentation g X =
      genericNullBoundary_projectiveNonzeroNull55_equiv.symm
        (restrictedProjectiveNullRepresentation g
          (genericNullBoundary_projectiveNonzeroNull55_equiv X)) := by
  change
    genericNullBoundary_projectiveNonzeroNull55_equiv.symm
        (restrictedProjectiveNullRepresentation g
          (genericNullBoundary_projectiveNonzeroNull55_equiv X)) = _
  rfl

/-- Spectral CPT involution `s ↦ 1 - conj(s)`. -/
def spectralCPT (s : ℂ) : ℂ :=
  1 - conj s

/-- Fixed points of spectral CPT are exactly the critical line. -/
theorem spectralCPT_fixed_iff_criticalLine (s : ℂ) :
    spectralCPT s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre : (spectralCPT s).re = s.re := by rw [h]
    unfold spectralCPT at hre
    simp at hre
    linarith
  · intro h
    apply Complex.ext
    · simp [spectralCPT, h]
      norm_num
    · simp [spectralCPT]

end ProjectiveAffineConformalClosure55

end noncomputable section
