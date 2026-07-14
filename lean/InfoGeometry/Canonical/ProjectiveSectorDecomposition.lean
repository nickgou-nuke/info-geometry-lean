import InfoGeometry.Canonical.ProjectiveSplitQ11Realization
import InfoGeometry.Projective.Null

open scoped LinearAlgebra.Projectivization

/-!
# InfoGeometry.Canonical.ProjectiveSectorDecomposition

Coherence layer relating strict Mathlib projectivization sectors to the
existing pointed projective sectors away from the distinguished vacuum.
-/

namespace ProjectiveSectorDecomposition

open InfoGeometry.Krein
open InfoGeometry.Canonical.ProjectiveSplitQ11Realization

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "StrictProjectiveCarrier" => InfoGeometry.Convex.ProjectiveState (E := E)
local notation "PointedNonvacuumCarrier" =>
  { q : InfoGeometry.Projective.ProjectiveState (E := E) //
      q ≠ InfoGeometry.Projective.vacuum (E := E) }

/-- Strict `J = +1` grade sector on the Mathlib projective surface. -/
def IsStrictGradePlusRay (q : StrictProjectiveCarrier) : Prop :=
  InfoGeometry.Projective.IsGradePlusRay
    ((mathlibProjectivization_toProjectiveRay (E := E) q).1)

/-- Strict `J = -1` grade sector on the Mathlib projective surface. -/
def IsStrictGradeMinusRay (q : StrictProjectiveCarrier) : Prop :=
  InfoGeometry.Projective.IsGradeMinusRay
    ((mathlibProjectivization_toProjectiveRay (E := E) q).1)

/-- Strict grade-null rays are exactly the union of the two strict grade sectors. -/
def IsStrictGradeNullRay (q : StrictProjectiveCarrier) : Prop :=
  IsStrictGradePlusRay (E := E) q ∨ IsStrictGradeMinusRay (E := E) q

theorem strictGradePlusRay_iff_pointed (q : PointedNonvacuumCarrier) :
    IsStrictGradePlusRay (E := E)
        (projectiveRay_equiv_mathlibProjectivization (E := E) q)
      ↔
    InfoGeometry.Projective.IsGradePlusRay q.1 := by
  have hInv :
      mathlibProjectivization_toProjectiveRay (E := E)
          (projectiveRay_equiv_mathlibProjectivization (E := E) q) = q := by
    change
      mathlibProjectivization_toProjectiveRay (E := E)
          (projectiveRay_toMathlibProjectivization (E := E) q) = q
    exact
      mathlibProjectivization_toProjectiveRay_toMathlibProjectivization (E := E) q
  have hVal :
      (mathlibProjectivization_toProjectiveRay (E := E)
          (projectiveRay_equiv_mathlibProjectivization (E := E) q)).1 = q.1 :=
    congrArg Subtype.val hInv
  unfold IsStrictGradePlusRay
  simp [hVal]

theorem strictGradeMinusRay_iff_pointed (q : PointedNonvacuumCarrier) :
    IsStrictGradeMinusRay (E := E)
        (projectiveRay_equiv_mathlibProjectivization (E := E) q)
      ↔
    InfoGeometry.Projective.IsGradeMinusRay q.1 := by
  have hInv :
      mathlibProjectivization_toProjectiveRay (E := E)
          (projectiveRay_equiv_mathlibProjectivization (E := E) q) = q := by
    change
      mathlibProjectivization_toProjectiveRay (E := E)
          (projectiveRay_toMathlibProjectivization (E := E) q) = q
    exact
      mathlibProjectivization_toProjectiveRay_toMathlibProjectivization (E := E) q
  have hVal :
      (mathlibProjectivization_toProjectiveRay (E := E)
          (projectiveRay_equiv_mathlibProjectivization (E := E) q)).1 = q.1 :=
    congrArg Subtype.val hInv
  unfold IsStrictGradeMinusRay
  simp [hVal]

@[simp] theorem IsStrictGradePlusRay_projectivize (v : H₂) (hv : v ≠ 0) :
    IsStrictGradePlusRay (E := E) (strictProjectivize (E := E) v hv) ↔
      inGradePlus (E := E) v := by
  let q : PointedNonvacuumCarrier :=
    ⟨InfoGeometry.Projective.projectivize (E := E) v,
      pointed_projectivize_ne_vacuum (E := E) v hv⟩
  have hq :
      projectiveRay_equiv_mathlibProjectivization (E := E) q =
        strictProjectivize (E := E) v hv := by
    simpa [projectiveRay_equiv_mathlibProjectivization, q] using
      (projectiveRay_toMathlibProjectivization_projectivize (E := E) v hv)
  calc
    IsStrictGradePlusRay (E := E) (strictProjectivize (E := E) v hv)
      ↔ IsStrictGradePlusRay (E := E)
          (projectiveRay_equiv_mathlibProjectivization (E := E) q) := by
            simp [hq]
    _ ↔ InfoGeometry.Projective.IsGradePlusRay q.1 :=
      strictGradePlusRay_iff_pointed (E := E) q
    _ ↔ inGradePlus (E := E) v := by
      change
        InfoGeometry.Projective.IsGradePlusRay
            (InfoGeometry.Projective.projectivize (E := E) v) ↔ inGradePlus (E := E) v
      exact InfoGeometry.Projective.IsGradePlusRay_projectivize (E := E) v

@[simp] theorem IsStrictGradeMinusRay_projectivize (v : H₂) (hv : v ≠ 0) :
    IsStrictGradeMinusRay (E := E) (strictProjectivize (E := E) v hv) ↔
      inGradeMinus (E := E) v := by
  let q : PointedNonvacuumCarrier :=
    ⟨InfoGeometry.Projective.projectivize (E := E) v,
      pointed_projectivize_ne_vacuum (E := E) v hv⟩
  have hq :
      projectiveRay_equiv_mathlibProjectivization (E := E) q =
        strictProjectivize (E := E) v hv := by
    simpa [projectiveRay_equiv_mathlibProjectivization, q] using
      (projectiveRay_toMathlibProjectivization_projectivize (E := E) v hv)
  calc
    IsStrictGradeMinusRay (E := E) (strictProjectivize (E := E) v hv)
      ↔ IsStrictGradeMinusRay (E := E)
          (projectiveRay_equiv_mathlibProjectivization (E := E) q) := by
            simp [hq]
    _ ↔ InfoGeometry.Projective.IsGradeMinusRay q.1 :=
      strictGradeMinusRay_iff_pointed (E := E) q
    _ ↔ inGradeMinus (E := E) v := by
      change
        InfoGeometry.Projective.IsGradeMinusRay
            (InfoGeometry.Projective.projectivize (E := E) v) ↔ inGradeMinus (E := E) v
      exact InfoGeometry.Projective.IsGradeMinusRay_projectivize (E := E) v

theorem strictGradeNullRay_iff_pointed (q : PointedNonvacuumCarrier) :
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
      change IsStrictGradePlusRay (E := E) (strictProjectivize (E := E) v hv) at hq
      have hplus : inGradePlus (E := E) v := by
        exact (IsStrictGradePlusRay_projectivize (E := E) v hv).1 hq
      have hsame : InfoGeometry.Projective.same_ray v (modular_j (E := E) v) := by
        refine ⟨(1 : ℝ), by norm_num, ?_⟩
        simpa [hplus]
      calc
        mathlibProjectiveJ (E := E) (strictProjectivize (E := E) v hv)
          = strictProjectivize (E := E)
              (modular_j (E := E) v) (modular_j_ne_zero (E := E) hv) := by
                exact mathlibProjectiveJ_projectivize (E := E) v hv
        _ = strictProjectivize (E := E) v hv := by
              simpa using
                (strict_projectivize_eq_of_same_ray (E := E) hsame hv
                  (modular_j_ne_zero (E := E) hv)).symm

theorem mathlibProjectiveJ_eq_self_of_strictGradeMinusRay :
    ∀ {q : StrictProjectiveCarrier}, IsStrictGradeMinusRay (E := E) q →
      mathlibProjectiveJ (E := E) q = q := by
  intro q hq
  induction q using Projectivization.ind with
  | h v hv =>
      change IsStrictGradeMinusRay (E := E) (strictProjectivize (E := E) v hv) at hq
      have hminus : inGradeMinus (E := E) v := by
        exact (IsStrictGradeMinusRay_projectivize (E := E) v hv).1 hq
      have hsame : InfoGeometry.Projective.same_ray v (modular_j (E := E) v) := by
        refine ⟨(-1 : ℝ), by norm_num, ?_⟩
        simpa [hminus]
      calc
        mathlibProjectiveJ (E := E) (strictProjectivize (E := E) v hv)
          = strictProjectivize (E := E)
              (modular_j (E := E) v) (modular_j_ne_zero (E := E) hv) := by
                exact mathlibProjectiveJ_projectivize (E := E) v hv
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

end ProjectiveSectorDecomposition
