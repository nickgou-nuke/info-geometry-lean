import InfoGeometry.Projective.SplitOctonions.ZornConcrete
import Mathlib.Tactic

/-!
# Concrete projective Zorn instance

This file instantiates the abstract `ZornProjectiveDatum` using componentwise
unit scaling on the local Zorn cell

  [ a  v ]
  [ w  b ]

with determinant

  detZ X = a b - B v w.

The key theorem is

  detZ (u • X) = u^2 * detZ X,

so unit scaling preserves the null cone and therefore descends to the
projective null quotient.

This file is only the local projective Zorn layer.  It does not prove Zorn
composition multiplicativity, associator nonzero, Albert rank-one geometry,
or cyclic H³ statements.
-/

namespace InfoGeometry.Projective.SplitOctonions

universe u v

open ZornProjectiveDatum.PolarDatum

namespace ZornCell

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- The zero Zorn cell. -/
def zeroCell : ZornCell R V :=
  ⟨0, 0, 0, 0⟩

/--
Componentwise unit scaling of a Zorn cell.

For a unit `u : Rˣ`,

  u • [a v; w b] = [ua uv; uw ub].
-/
def scalarScale (u : Rˣ) (X : ZornCell R V) : ZornCell R V :=
  ⟨(u : R) * X.a,
   (u : R) * X.b,
   (u : R) • X.v,
   (u : R) • X.w⟩

@[simp]
theorem scalarScale_one (X : ZornCell R V) :
    scalarScale (1 : Rˣ) X = X := by
  ext <;> simp [scalarScale]

@[simp]
theorem scalarScale_mul (u v : Rˣ) (X : ZornCell R V) :
    scalarScale (u * v) X = scalarScale u (scalarScale v X) := by
  ext <;> simp [scalarScale, mul_assoc, smul_smul]

@[simp]
theorem scalarScale_zero (u : Rˣ) :
    scalarScale u (zeroCell : ZornCell R V) = zeroCell := by
  ext <;> simp [scalarScale, zeroCell]

@[simp]
theorem scalarScale_inv_scale (u : Rˣ) (X : ZornCell R V) :
    scalarScale u⁻¹ (scalarScale u X) = X := by
  ext <;> simp [scalarScale, smul_smul]

/--
Zorn determinant scaling law:

  detZ (u • X) = u² detZ X.
-/
theorem detZ_scalarScale
    (B : V →ₗ[R] V →ₗ[R] R)
    (u : Rˣ) (X : ZornCell R V) :
    ZornCell.detZ B (scalarScale u X)
      =
    ((u : R) ^ 2) * ZornCell.detZ B X := by
  unfold ZornCell.detZ scalarScale
  have hB :
      B ((u : R) • X.v) ((u : R) • X.w)
        =
      ((u : R) * (u : R)) * B X.v X.w := by
    simp [map_smul, mul_assoc]
  rw [hB]
  ring

/-- Multiplication by a unit preserves zero. -/
lemma unit_mul_eq_zero_iff (u : Rˣ) (x : R) :
    (u : R) * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h' : ((u⁻¹ : Rˣ) : R) * ((u : R) * x)
        =
      ((u⁻¹ : Rˣ) : R) * 0 := by
      rw [h]
    simpa [mul_assoc] using h'
  · intro hx
    simp [hx]

/--
Unit scaling preserves the null condition.
-/
theorem detZ_scalarScale_zero_iff
    (B : V →ₗ[R] V →ₗ[R] R)
    (u : Rˣ) (X : ZornCell R V) :
    ZornCell.detZ B (scalarScale u X) = 0
      ↔
    ZornCell.detZ B X = 0 := by
  rw [detZ_scalarScale]
  simpa [pow_two] using
    (unit_mul_eq_zero_iff (u * u) (ZornCell.detZ B X))

/--
Unit scaling preserves nonzeroness of Zorn cells.
-/
theorem scalarScale_ne_zero
    (u : Rˣ) (X : ZornCell R V)
    (hX : X ≠ zeroCell) :
    scalarScale u X ≠ zeroCell := by
  intro h
  apply hX
  have h' := congrArg (scalarScale u⁻¹) h
  simpa using h'

/--
The concrete projective datum for local Zorn cells.

The scale action is componentwise multiplication by a unit.
-/
def projectiveDatum
    (B : V →ₗ[R] V →ₗ[R] R) :
    ZornProjectiveDatum R V where
  B := B
  zero := zeroCell
  scale := scalarScale
  scale_one := scalarScale_one
  scale_mul := scalarScale_mul
  detZ_scale_zero := detZ_scalarScale_zero_iff B
  scale_ne_zero := scalarScale_ne_zero

/-! ## Canonical local null representatives -/

/-- Positive diagonal idempotent cell `[1 0; 0 0]`. -/
def pPlus : ZornCell R V :=
  ⟨1, 0, 0, 0⟩

/-- Negative diagonal idempotent cell `[0 0; 0 1]`. -/
def pMinus : ZornCell R V :=
  ⟨0, 1, 0, 0⟩

/-- Upper off-diagonal Zorn lightray cell `[0 v; 0 0]`. -/
def upperLightray (v : V) : ZornCell R V :=
  ⟨0, 0, v, 0⟩

/-- Lower off-diagonal Zorn lightray cell `[0 0; w 0]`. -/
def lowerLightray (w : V) : ZornCell R V :=
  ⟨0, 0, 0, w⟩

@[simp]
theorem pPlus_isNull
    (B : V →ₗ[R] V →ₗ[R] R) :
    ZornCell.detZ B (pPlus : ZornCell R V) = 0 := by
  simp [ZornCell.detZ, pPlus]

@[simp]
theorem pMinus_isNull
    (B : V →ₗ[R] V →ₗ[R] R) :
    ZornCell.detZ B (pMinus : ZornCell R V) = 0 := by
  simp [ZornCell.detZ, pMinus]

@[simp]
theorem upperLightray_isNull
    (B : V →ₗ[R] V →ₗ[R] R) (v : V) :
    ZornCell.detZ B (upperLightray v : ZornCell R V) = 0 := by
  simp [ZornCell.detZ, upperLightray]

@[simp]
theorem lowerLightray_isNull
    (B : V →ₗ[R] V →ₗ[R] R) (w : V) :
    ZornCell.detZ B (lowerLightray w : ZornCell R V) = 0 := by
  simp [ZornCell.detZ, lowerLightray]

omit [Module R V] in
theorem pPlus_ne_zero [Nontrivial R] :
    (pPlus : ZornCell R V) ≠ zeroCell := by
  intro h
  have ha : (1 : R) = 0 := by
    simpa [pPlus, zeroCell] using congrArg ZornCell.a h
  exact one_ne_zero ha

omit [Module R V] in
theorem pMinus_ne_zero [Nontrivial R] :
    (pMinus : ZornCell R V) ≠ zeroCell := by
  intro h
  have hb : (1 : R) = 0 := by
    simpa [pMinus, zeroCell] using congrArg ZornCell.b h
  exact one_ne_zero hb

omit [Module R V] in
theorem upperLightray_ne_zero {v : V} (hv : v ≠ 0) :
    (upperLightray v : ZornCell R V) ≠ zeroCell := by
  intro h
  apply hv
  simpa [upperLightray, zeroCell] using congrArg ZornCell.v h

omit [Module R V] in
theorem lowerLightray_ne_zero {w : V} (hw : w ≠ 0) :
    (lowerLightray w : ZornCell R V) ≠ zeroCell := by
  intro h
  apply hw
  simpa [lowerLightray, zeroCell] using congrArg ZornCell.w h

/-- `pPlus` as a nonzero null representative. -/
def pPlusNullRep
    [Nontrivial R]
    (B : V →ₗ[R] V →ₗ[R] R) :
    ZornProjectiveDatum.NullRep (projectiveDatum B) where
  rep := pPlus
  det_zero := pPlus_isNull B
  nonzero := pPlus_ne_zero

/-- `pMinus` as a nonzero null representative. -/
def pMinusNullRep
    [Nontrivial R]
    (B : V →ₗ[R] V →ₗ[R] R) :
    ZornProjectiveDatum.NullRep (projectiveDatum B) where
  rep := pMinus
  det_zero := pMinus_isNull B
  nonzero := pMinus_ne_zero

/-- An upper off-diagonal lightray as a nonzero null representative. -/
def upperLightrayNullRep
    (B : V →ₗ[R] V →ₗ[R] R)
    {v : V} (hv : v ≠ 0) :
    ZornProjectiveDatum.NullRep (projectiveDatum B) where
  rep := upperLightray v
  det_zero := upperLightray_isNull B v
  nonzero := upperLightray_ne_zero hv

/-- A lower off-diagonal lightray as a nonzero null representative. -/
def lowerLightrayNullRep
    (B : V →ₗ[R] V →ₗ[R] R)
    {w : V} (hw : w ≠ 0) :
    ZornProjectiveDatum.NullRep (projectiveDatum B) where
  rep := lowerLightray w
  det_zero := lowerLightray_isNull B w
  nonzero := lowerLightray_ne_zero hw

/-- The projective null ray represented by `pPlus`. -/
def pPlusNullRay
    [Nontrivial R]
    (B : V →ₗ[R] V →ₗ[R] R) :
    ZornProjectiveDatum.NullRay (projectiveDatum B) :=
  ZornProjectiveDatum.nullRayMk (projectiveDatum B) (pPlusNullRep B)

/-- The projective null ray represented by `pMinus`. -/
def pMinusNullRay
    [Nontrivial R]
    (B : V →ₗ[R] V →ₗ[R] R) :
    ZornProjectiveDatum.NullRay (projectiveDatum B) :=
  ZornProjectiveDatum.nullRayMk (projectiveDatum B) (pMinusNullRep B)

/-- The projective null ray represented by a nonzero upper lightray. -/
def upperLightrayNullRay
    (B : V →ₗ[R] V →ₗ[R] R)
    {v : V} (hv : v ≠ 0) :
    ZornProjectiveDatum.NullRay (projectiveDatum B) :=
  ZornProjectiveDatum.nullRayMk (projectiveDatum B) (upperLightrayNullRep B hv)

/-- The projective null ray represented by a nonzero lower lightray. -/
def lowerLightrayNullRay
    (B : V →ₗ[R] V →ₗ[R] R)
    {w : V} (hw : w ≠ 0) :
    ZornProjectiveDatum.NullRay (projectiveDatum B) :=
  ZornProjectiveDatum.nullRayMk (projectiveDatum B) (lowerLightrayNullRep B hw)

/-- The split-octonion projective null boundary contains the explicit `pPlus` ray. -/
theorem projectiveNullBoundary_nonempty
    [Nontrivial R]
    (B : V →ₗ[R] V →ₗ[R] R) :
    ∃ X : ZornProjectiveDatum.NullRep (projectiveDatum B),
      X.rep = pPlus ∧
        ZornProjectiveDatum.nullRayMk (projectiveDatum B) X = pPlusNullRay B := by
  exact ⟨pPlusNullRep B, rfl, rfl⟩

end ZornCell

end InfoGeometry.Projective.SplitOctonions
