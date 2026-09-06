import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Ring.Basic

/-!
# Tessellation incidence

This file contains the first algebraic incidence layer for the operator
tessellation picture.

A nilpotent alone does not define incidence.  Incidence is represented by an
element supported between two idempotent sectors.  Orthogonal supports then
force nilpotence as a theorem.

No cyclic cohomology or H³ gluing statement is introduced here.
-/

namespace InfoGeometry.Tessellation

/-- A causal diamond is an idempotent sector. -/
structure Diamond (A : Type*) [Semiring A] where
  /-- The sector idempotent. -/
  P : A
  /-- The sector law. -/
  idem : P * P = P

/-!
## Directional orthogonality

For a lightray `N ∈ tgt A src`, encoded by `tgt.P * N = N` and
`N * src.P = N`, square-zero propagation uses `src.P * tgt.P = 0`.
If the arrow orientation is reversed, the orthogonality condition is reversed
too.
-/
namespace Diamond

/-- Directional orthogonality for a ray from `src` to `tgt`. -/
def OrthogonalForRay {A : Type*} [Semiring A] (src tgt : Diamond A) : Prop :=
  src.P * tgt.P = 0

end Diamond

/--
A lightray from `src` to `tgt`.

The support laws say that `N` starts in the source sector and lands in the
target sector: `tgt.P * N = N` and `N * src.P = N`.
-/
structure IncidentLightray (A : Type*) [Semiring A]
    (src tgt : Diamond A) where
  /-- The off-diagonal transition element. -/
  N : A
  /-- Left support at the target sector. -/
  left_support : tgt.P * N = N
  /-- Right support at the source sector. -/
  right_support : N * src.P = N

/--
A supported lightray with the source/target orthogonality stored as part of the
incidence datum.

This is the geometric packet: the lightray knows its source sector, target
sector, support laws, and that those sectors are orthogonal.
-/
structure SupportedLightray (A : Type*) [Semiring A]
    (src tgt : Diamond A) extends IncidentLightray A src tgt where
  /-- Orthogonality of the source and target sectors. -/
  orthogonal : Diamond.OrthogonalForRay src tgt

/--
If the source and target idempotents are orthogonal, then every supported
lightray between them is automatically nilpotent.

This is the algebraic core of lightlike incidence.
-/
theorem incident_lightray_square_zero
    {A : Type*} [Semiring A]
    {P Q N : A}
    (hPQ : P * Q = 0)
    (hQN : Q * N = N)
    (hNP : N * P = N) :
    N * N = 0 := by
  calc
    N * N = (N * P) * (Q * N) := by
      rw [hNP, hQN]
    _ = N * (P * Q) * N := by
      simp [mul_assoc]
    _ = 0 := by
      simp [hPQ]

/--
Structure-level version of `incident_lightray_square_zero`.
-/
theorem IncidentLightray.square_zero_of_orthogonal
    {A : Type*} [Semiring A]
    {src tgt : Diamond A}
    (L : IncidentLightray A src tgt)
    (h_orthogonal : Diamond.OrthogonalForRay src tgt) :
    L.N * L.N = 0 :=
  incident_lightray_square_zero h_orthogonal L.left_support L.right_support

/--
Closed structure-level incidence theorem: a supported lightray between
orthogonal idempotent sectors is square-zero.
-/
theorem SupportedLightray.square_zero
    {A : Type*} [Semiring A]
    {src tgt : Diamond A}
    (L : SupportedLightray A src tgt) :
    L.N * L.N = 0 :=
  L.toIncidentLightray.square_zero_of_orthogonal L.orthogonal

/--
Name-level alias for the closed supported-incidence theorem:
a supported arrow between orthogonal idempotent sectors is square-zero.
-/
theorem supported_lightray_square_zero
    {A : Type*} [Semiring A]
    {src tgt : Diamond A}
    (L : SupportedLightray A src tgt) :
    L.N * L.N = 0 :=
  L.square_zero

end InfoGeometry.Tessellation
