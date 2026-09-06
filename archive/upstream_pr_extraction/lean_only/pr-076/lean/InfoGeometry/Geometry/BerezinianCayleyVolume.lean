/-
InfoGeometry/Geometry/BerezinianCayleyVolume.lean

Interface layer for the Hestenes-Krein Cayley transform and the
Fredholm/Berezinian volume ratio.

This file intentionally does not import a nonexistent or unstable Fredholm
determinant API. Fredholm data are supplied as structure fields.
-/

import Mathlib.Tactic
import InfoGeometry.Geometry.BilingualUpperHalfPlane

noncomputable section

namespace InfoGeometry.Geometry

open scoped InnerProductSpace

open InfoGeometry.Krein
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Quantum

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => DoubledEnd E

namespace BilingualUpperHalfPlane

variable {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}

/--
Invertibility datum for the Cayley denominator `τ + K`.

The upper-half-plane positivity gives strong evidence that `τ + K` has no
kernel, but in infinite dimension injectivity is not enough for bounded
invertibility. Hence the inverse is packaged explicitly.
-/
structure CayleyDenominator (Z : BilingualUpperHalfPlane D) where
  /-- The denominator as a unit of the operator algebra. -/
  unit : Units EndH
  /-- The unit is exactly `τ + K`. -/
  unit_eq : unit.val = Z.tau + D.K

/--
The operator Cayley transform

`U = (τ - K) (τ + K)⁻¹`.

This is the coordinate-free analogue of `z ↦ (z - i) / (z + i)`.
-/
def operatorCayleyTransform
    (Z : BilingualUpperHalfPlane D)
    (den : CayleyDenominator Z) :
    EndH :=
  (Z.tau - D.K).comp ((den.unit⁻¹).val)

/--
A Cayley disk point is not merely an operator `U`; it remembers the
upper-half-plane point and the denominator inverse used to construct it.
-/
abbrev CayleyDiskPoint :=
  Σ source : BilingualUpperHalfPlane D, CayleyDenominator source

namespace CayleyDiskPoint

abbrev source (X : CayleyDiskPoint (D := D)) : BilingualUpperHalfPlane D := X.1

abbrev denominator (X : CayleyDiskPoint (D := D)) : CayleyDenominator X.source := X.2

/-- The Cayley operator determined by the source and its invertible denominator. -/
abbrev U (X : CayleyDiskPoint (D := D)) : EndH :=
  operatorCayleyTransform X.source X.denominator

@[simp] theorem cayley_eq (X : CayleyDiskPoint (D := D)) :
    X.U = operatorCayleyTransform X.source X.denominator :=
  rfl

end CayleyDiskPoint

/--
A boson/fermion sector split on the doubled carrier.

This is the formal place where the Moore-Penrose metric sector and the
Drazin/topological sector should enter. Do not hard-code those sectors as
strings or `sorryAx`; package their projectors and algebraic laws.
-/
abbrev SectorSplit :=
  {P : EndH × EndH //
    P.1.comp P.1 = P.1 ∧
    P.2.comp P.2 = P.2 ∧
    P.1.comp P.2 = 0 ∧
    P.2.comp P.1 = 0 ∧
    P.1 + P.2 = 1}

namespace SectorSplit

abbrev bosonic (S : SectorSplit (E := E)) : EndH := S.1.1
abbrev fermionic (S : SectorSplit (E := E)) : EndH := S.1.2
abbrev bosonic_idem (S : SectorSplit (E := E)) : S.bosonic.comp S.bosonic = S.bosonic := S.2.1
abbrev fermionic_idem (S : SectorSplit (E := E)) : S.fermionic.comp S.fermionic = S.fermionic := S.2.2.1
abbrev orthogonal_bf (S : SectorSplit (E := E)) : S.bosonic.comp S.fermionic = 0 := S.2.2.2.1
abbrev orthogonal_fb (S : SectorSplit (E := E)) : S.fermionic.comp S.bosonic = 0 := S.2.2.2.2.1
abbrev complete (S : SectorSplit (E := E)) : S.bosonic + S.fermionic = 1 := S.2.2.2.2.2

end SectorSplit

/-- Compression of an operator to a sector projector. -/
def sectorCompress (P T : EndH) : EndH :=
  (P.comp T).comp P

/-- Bosonic/Moore-Penrose component of a deformation. -/
def bosonicPart (S : SectorSplit (E := E)) (T : EndH) : EndH :=
  sectorCompress S.bosonic T

/-- Fermionic/Drazin component of a deformation. -/
def fermionicPart (S : SectorSplit (E := E)) (T : EndH) : EndH :=
  sectorCompress S.fermionic T

/--
Abstract Fredholm determinant datum.

This is the correct interface point. Later, one can instantiate it by:

* finite-dimensional determinant;
* trace-class Fredholm determinant;
* regularized determinant;
* Krein-renormalized determinant.

The current file only needs the algebraic behavior required by the
Berezinian ratio.
-/
structure FredholmDeterminantDatum where
  /-- Operators on which the determinant is meaningful. -/
  admissible : EndH → Prop
  /-- The determinant functional. -/
  det : EndH → ℝ
  /-- Identity is admissible. -/
  admissible_one : admissible 1
  /-- Normalization. -/
  det_one : det 1 = 1
  /--
  Admissibility is invariant under conjugation by an invertible operator.
  This is the determinant-level shadow of coordinate-free geometry.
  -/
  admissible_conj :
    ∀ (u : Units EndH) {T : EndH},
      admissible T →
      admissible ((u.val.comp T).comp ((u⁻¹).val))
  /-- Determinant is invariant under conjugation. -/
  det_conj :
    ∀ (u : Units EndH) {T : EndH},
      admissible T →
      det ((u.val.comp T).comp ((u⁻¹).val)) = det T

/--
A pair of determinant-admissible flows whose ratio defines the Berezinian.

The bosonic flow is the Moore-Penrose/metriplectic contribution.
The fermionic flow is the Drazin/topological contribution.
-/
structure BerezinianFlow (FD : FredholmDeterminantDatum (E := E)) where
  bosonicFlow : EndH
  fermionicFlow : EndH
  bosonic_admissible :
    FD.admissible (1 + bosonicFlow)
  fermionic_admissible :
    FD.admissible (1 + fermionicFlow)
  fermionic_det_ne_zero :
    FD.det (1 + fermionicFlow) ≠ 0

/--
The Fredholm-Berezinian relative volume:

`Ber = det(I + B) / det(I + F)`.

Here `B` is the bosonic/Moore-Penrose deformation and `F` is the
fermionic/Drazin deformation.
-/
def berezinianRelativeVolume
    (FD : FredholmDeterminantDatum (E := E))
    (flow : BerezinianFlow (E := E) FD) :
    ℝ :=
  FD.det (1 + flow.bosonicFlow) /
    FD.det (1 + flow.fermionicFlow)

/--
A MaxEnt calibration is additional structure, not a free theorem.

The statement `Ber ≤ 1`, with equality exactly at the vacuum, requires analytic
hypotheses: positivity, contractivity, trace-class control, and the exact
definition of the bosonic/fermionic split.
-/
structure MaxEntBerezinianCalibration
    (FD : FredholmDeterminantDatum (E := E)) where
  /-- The central Cayley-disk vacuum, usually `0`. -/
  vacuum : EndH
  /-- The vacuum is the Cayley disk center. -/
  vacuum_eq_zero : vacuum = 0
  /-- The calibrated Berezinian is globally bounded by one. -/
  volume_le_one :
    ∀ flow : BerezinianFlow (E := E) FD,
      berezinianRelativeVolume FD flow ≤ 1
  /-- Equality characterizes the undeformed vacuum flow. -/
  volume_eq_one_iff :
    ∀ flow : BerezinianFlow (E := E) FD,
      berezinianRelativeVolume FD flow = 1 ↔
        flow.bosonicFlow = 0 ∧ flow.fermionicFlow = 0

end BilingualUpperHalfPlane

end InfoGeometry.Geometry
