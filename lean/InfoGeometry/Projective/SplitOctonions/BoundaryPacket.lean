import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.Canonical.SplitAlbert
import InfoGeometry.Projective.SplitOctonions.Albert
import InfoGeometry.Projective.SplitOctonions.Polar
import InfoGeometry.Projective.SplitOctonions.ZornConcrete
import InfoGeometry.Projective.SplitOctonions.ZornInstance

/-!
# Split octonion / Albert / Zorn boundary packet

This file packages the split-octonion and split-Albert owner surfaces that the
repository actually proves:

* Albert-Cayley-Dickson split doubling has canonical zero divisors;
* the split Albert carrier has real finrank `27`;
* the concrete Zorn projective datum and its polar incidence are available;
* the canonical positive/negative diagonal rays and light-rays are explicit.

No twistor identification is claimed here.
No Zorn-to-`2 × 2` matrix equivalence is claimed here.
No `twistor space = split octonions` theorem is encoded here.
-/

noncomputable section

namespace InfoGeometry.Projective.SplitOctonions.BoundaryPacket

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.SplitAlbert
open InfoGeometry.Projective.SplitOctonions
open ZornProjectiveDatum
open ZornProjectiveDatum.PolarDatum
open ZornCell

universe v

/--
Repo-facing finite packet for the split-octonion / split-Albert / local-Zorn
boundary lane.

This is a theorem bundle collecting owner facts already proved elsewhere in the
repository. It does not add a new abstract split-Albert projective-plane bridge.
-/
structure SplitOctonionBoundaryPacket
    (V : Type v) [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) where
  /-- The split Albert-Cayley-Dickson doubling layer has canonical zero divisors. -/
  split_albert_zero_divisors :
    ∃ x y : AlbertStep ℝ (SplitQuaternion ℝ) (1 : ℝ),
      x ≠ 0 ∧ y ≠ 0 ∧ AlbertStep.mul x y = 0

  /-- The current split Albert carrier is the real 27-dimensional owner model. -/
  split_albert_finrank_27 :
    Module.finrank ℝ SplitAlbertCarrier = 27

  /-- The concrete Zorn polar pairing is symmetric. -/
  concrete_polar_symm :
    ∀ X Y : ZornCell ℝ V,
      polarZ (concretePolarDatum B) X Y = polarZ (concretePolarDatum B) Y X

  /-- Canonical representative-level projective incidence is the polarized-form zero test. -/
  projective_polar_incidence_iff :
    ∀ X Y : ZornProjectiveDatum.NullRep (concreteZornProjectiveDatum B),
      projective_polar_incidence (R := ℝ) (V := V) B
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B) X)
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B) Y)
        ↔ polarExpr B X.rep Y.rep = 0

  /-- The canonical positive diagonal ray is incident with every upper lightray ray. -/
  pPlus_incident_upperLightray :
    ∀ {v : V} (hv : v ≠ 0),
      Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pPlusRep (R := ℝ) (V := V) B))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (upperLightrayRep (R := ℝ) (V := V) B hv))

  /-- The canonical negative diagonal ray is incident with every lower lightray ray. -/
  pMinus_incident_lowerLightray :
    ∀ {w : V} (hw : w ≠ 0),
      Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pMinusRep (R := ℝ) (V := V) B))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (lowerLightrayRep (R := ℝ) (V := V) B hw))

  /-- Over a nontrivial field, the canonical positive and negative diagonal rays are not incident. -/
  pPlus_notIncident_pMinus :
    ¬ Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pPlusRep (R := ℝ) (V := V) B))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pMinusRep (R := ℝ) (V := V) B))

  /-- Upper/lower lightray incidence is exactly vanishing of the bilinear pairing. -/
  upperLightray_incident_lowerLightray_iff :
    ∀ {v w : V} (hv : v ≠ 0) (hw : w ≠ 0),
      Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (upperLightrayRep (R := ℝ) (V := V) B hv))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (lowerLightrayRep (R := ℝ) (V := V) B hw))
        ↔ B v w = 0

  /-- The split-octonion projective null boundary carries an explicit ray. -/
  projective_null_boundary :
    ZornProjectiveDatum.NullRay (concreteZornProjectiveDatum B)

/-- Canonical repository packet for the split-octonion / split-Albert / Zorn boundary lane. -/
def canonicalSplitOctonionBoundaryPacket
    (V : Type v) [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    SplitOctonionBoundaryPacket V B where
  split_albert_zero_divisors :=
    AlbertStep.gamma_one_has_canonical_zero_divisors (F := ℝ)
      (A := SplitQuaternion ℝ)
  split_albert_finrank_27 := splitAlbertCarrier_finrank_eq_27
  concrete_polar_symm :=
    concretePolarDatum_polarZ_symm (R := ℝ) (V := V) B
  projective_polar_incidence_iff :=
    projective_polar_incidence_iff (R := ℝ) (V := V) B
  pPlus_incident_upperLightray :=
    pPlusIncident_upperLightray_ray (R := ℝ) (V := V) B
  pMinus_incident_lowerLightray :=
    pMinusIncident_lowerLightray_ray (R := ℝ) (V := V) B
  pPlus_notIncident_pMinus :=
    pPlus_notIncident_pMinus_ray (R := ℝ) (V := V) B
  upperLightray_incident_lowerLightray_iff :=
    upperLightrayIncident_lowerLightray_iff_ray (R := ℝ) (V := V) B
  projective_null_boundary :=
    ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
      (pPlusRep (R := ℝ) (V := V) B)

/-- The boundary packet exposes its explicit null ray witness. -/
def projective_null_boundary_witness
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (P : SplitOctonionBoundaryPacket V B) :
    ZornProjectiveDatum.NullRay (concreteZornProjectiveDatum B) :=
  P.projective_null_boundary

end InfoGeometry.Projective.SplitOctonions.BoundaryPacket
