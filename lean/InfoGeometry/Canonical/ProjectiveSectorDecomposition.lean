import InfoGeometry.Canonical.ProjectiveSplitQ11Realization
import InfoGeometry.Projective.Null

open scoped LinearAlgebra.Projectivization

/-!
# InfoGeometry.Canonical.ProjectiveSectorDecomposition

This module is a **coherence layer** above
`ProjectiveSplitQ11Realization`. It does not introduce a new projective
geometry. Instead it expresses the old pointed projective grading sectors and
their strict Mathlib-projectivized counterparts in one place.

The file owns three comparisons:

1. strict grade `±` and grade-null predicates on `ℙ ℝ (DoubledSpace E)`,
2. agreement of those strict predicates with the legacy pointed quotient away
   from the distinguished vacuum class, and
3. the corresponding fixed-point consequences for the descended modular mirror
   `J`.

What remains upstairs:

- linear projectors and eigenspace decompositions live on `DoubledSpace E`,
- the distinguished vacuum class belongs only to the old pointed quotient.

What descends here:

- grade sectors as predicates on strict rays,
- fixed-locus consequences for the descended `J`-action on those sectors.
-/

namespace InfoGeometry.Canonical.ProjectiveSectorDecomposition

open InfoGeometry.Krein
open InfoGeometry.Canonical.ProjectiveSplitQ11Realization

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "StrictProjectiveCarrier" => InfoGeometry.Convex.ProjectiveState (E := E)
local notation "PointedNonvacuumCarrier" =>
  { q : InfoGeometry.Projective.ProjectiveState (E := E) //
    q ≠ InfoGeometry.Projective.vacuum (E := E) }

/-- Strict `J = +1` grade sector on the Mathlib projective surface. -/
def IsStrictGradePlusRay : StrictProjectiveCarrier → Prop :=
  Projectivization.lift
    (fun (x : { v : H₂ // v ≠ 0 }) => inGradePlus (E := E) (x : H₂))
    (by
      intro a b t h
      have ht : t ≠ 0 := by
        intro ht0
        apply a.2
        rw [h, ht0, zero_smul]
      exact propext ((InfoGeometry.Projective.inGradePlus_smul_iff (E := E) ht (b : H₂)).symm))

/-- Strict `J = -1` grade sector on the Mathlib projective surface. -/
def IsStrictGradeMinusRay : StrictProjectiveCarrier → Prop :=
  Projectivization.lift
    (fun (x : { v : H₂ // v ≠ 0 }) => inGradeMinus (E := E) (x : H₂))
    (by
      intro a b t h
      have ht : t ≠ 0 := by
        intro ht0
        apply a.2
        rw [h, ht0, zero_smul]
      exact propext ((InfoGeometry.Projective.inGradeMinus_smul_iff (E := E) ht (b : H₂)).symm))

/-- Strict grade-null rays are exactly the union of the two strict grade sectors. -/
def IsStrictGradeNullRay (q : StrictProjectiveCarrier) : Prop :=
  IsStrictGradePlusRay (E := E) q ∨ IsStrictGradeMinusRay (E := E) q

@[simp] theorem IsStrictGradePlusRay_projectivize (v : H₂) (hv : v ≠ 0) :
    IsStrictGradePlusRay (E := E) (strictProjectivize (E := E) v hv) ↔ inGradePlus (E := E) v := by
  simp [IsStrictGradePlusRay, strictProjectivize, InfoGeometry.Convex.projectivize]

@[simp] theorem IsStrictGradeMinusRay_projectivize (v : H₂) (hv : v ≠ 0) :
    IsStrictGradeMinusRay (E := E) (strictProjectivize (E := E) v hv) ↔ inGradeMinus (E := E) v := by
  simp [IsStrictGradeMinusRay, strictProjectivize, InfoGeometry.Convex.projectivize]

theorem strictGradePlusRay_iff_pointed
    (q : PointedNonvacuumCarrier (E := E)) :
    IsStrictGradePlusRay (E := E)
        (projectiveRay_equiv_mathlibProjectivization (E := E) q)
      ↔
    InfoGeometry.Projective.IsGradePlusRay q.1 := by
  let v : H₂ := Quotient.out q.1
  have hv : v ≠ 0 := pointed_out_nonzero (E := E) q
  have hq : q.1 = InfoGeometry.Projective.projectivize (E := E) v := by
    simpa [v, InfoGeometry.Projective.projectivize] using (Quotient.out_eq' q.1)
  calc
    IsStrictGradePlusRay (E := E)
        (projectiveRay_equiv_mathlibProjectivization (E := E) q)
      ↔ inGradePlus (E := E) v := by
          simpa [projectiveRay_equiv_mathlibProjectivization,
            projectiveRay_toMathlibProjectivization, strictProjectivize, v]
            using (IsStrictGradePlusRay_projectivize (E := E) v hv)
    _ ↔ InfoGeometry.Projective.IsGradePlusRay q.1 := by
          rw [hq]
          simpa [v] using (InfoGeometry.Projective.IsGradePlusRay_projectivize (E := E) v)

theorem strictGradeMinusRay_iff_pointed
    (q : PointedNonvacuumCarrier (E := E)) :
    IsStrictGradeMinusRay (E := E)
        (projectiveRay_equiv_mathlibProjectivization (E := E) q)
      ↔
    InfoGeometry.Projective.IsGradeMinusRay q.1 := by
  let v : H₂ := Quotient.out q.1
  have hv : v ≠ 0 := pointed_out_nonzero (E := E) q
  have hq : q.1 = InfoGeometry.Projective.projectivize (E := E) v := by
    simpa [v, InfoGeometry.Projective.projectivize] using (Quotient.out_eq' q.1)
  calc
    IsStrictGradeMinusRay (E := E)
        (projectiveRay_equiv_mathlibProjectivization (E := E) q)
      ↔ inGradeMinus (E := E) v := by
          simpa [projectiveRay_equiv_mathlibProjectivization,
            projectiveRay_toMathlibProjectivization, strictProjectivize, v]
            using (IsStrictGradeMinusRay_projectivize (E := E) v hv)
    _ ↔ InfoGeometry.Projective.IsGradeMinusRay q.1 := by
          rw [hq]
          simpa [v] using (InfoGeometry.Projective.IsGradeMinusRay_projectivize (E := E) v)

theorem strictGradeNullRay_iff_pointed
    (q : PointedNonvacuumCarrier (E := E)) :
    IsStrictGradeNullRay (E := E)
        (projectiveRay_equiv_mathlibProjectivization (E := E) q)
      ↔
    InfoGeometry.Projective.IsGradeNullRay q.1 := by
  unfold IsStrictGradeNullRay InfoGeometry.Projective.IsGradeNullRay
  rw [strictGradePlusRay_iff_pointed (E := E) q, strictGradeMinusRay_iff_pointed (E := E) q]

theorem mathlibProjectiveJ_eq_self_of_strictGradePlusRay :
    ∀ {q : StrictProjectiveCarrier}, IsStrictGradePlusRay (E := E) q →
      mathlibProjectiveJ (E := E) q = q := by
  intro q hq
  induction q using Projectivization.ind with
  | h v hv =>
      change inGradePlus (E := E) v at hq
      calc
        mathlibProjectiveJ (E := E) (strictProjectivize (E := E) v hv)
          = strictProjectivize (E := E) (modular_j (E := E) v) (modular_j_ne_zero (E := E) hv) := by
              simpa using (mathlibProjectiveJ_projectivize (E := E) v hv)
        _ = strictProjectivize (E := E) v hv := by
              simpa [hq]

theorem mathlibProjectiveJ_eq_self_of_strictGradeMinusRay :
    ∀ {q : StrictProjectiveCarrier}, IsStrictGradeMinusRay (E := E) q →
      mathlibProjectiveJ (E := E) q = q := by
  intro q hq
  induction q using Projectivization.ind with
  | h v hv =>
      change inGradeMinus (E := E) v at hq
      have hsame : InfoGeometry.Projective.same_ray v (modular_j (E := E) v) := by
        refine ⟨(-1 : ℝ), by norm_num, ?_⟩
        simpa [hq]
      calc
        mathlibProjectiveJ (E := E) (strictProjectivize (E := E) v hv)
          = strictProjectivize (E := E) (modular_j (E := E) v) (modular_j_ne_zero (E := E) hv) := by
              simpa using (mathlibProjectiveJ_projectivize (E := E) v hv)
        _ = strictProjectivize (E := E) v hv := by
              simpa using
                (strict_projectivize_eq_of_same_ray (E := E) hsame hv
                  (modular_j_ne_zero (E := E) hv)).symm

theorem mathlibProjectiveJ_eq_self_of_strictGradeNullRay
    {q : StrictProjectiveCarrier} (hq : IsStrictGradeNullRay (E := E) q) :
    mathlibProjectiveJ (E := E) q = q := by
  rcases hq with hq | hq
  · exact mathlibProjectiveJ_eq_self_of_strictGradePlusRay (E := E) hq
  · exact mathlibProjectiveJ_eq_self_of_strictGradeMinusRay (E := E) hq

end InfoGeometry.Canonical.ProjectiveSectorDecomposition
