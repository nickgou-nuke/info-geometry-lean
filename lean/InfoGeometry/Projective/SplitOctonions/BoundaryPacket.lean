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

lemma split_albert_zero_divisors_lemma :
    ∃ x y : AlbertStep ℝ (SplitQuaternion ℝ) (1 : ℝ),
      x ≠ 0 ∧ y ≠ 0 ∧ AlbertStep.mul x y = 0 :=
  AlbertStep.gamma_one_has_canonical_zero_divisors (F := ℝ)
    (A := SplitQuaternion ℝ)

lemma split_albert_finrank_27_lemma :
    Module.finrank ℝ SplitAlbertCarrier = 27 :=
  splitAlbertCarrier_finrank_eq_27

lemma concrete_polar_symm_lemma {V : Type v} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ∀ X Y : ZornCell ℝ V,
      polarZ (concretePolarDatum B) X Y = polarZ (concretePolarDatum B) Y X :=
  concretePolarDatum_polarZ_symm (R := ℝ) (V := V) B

lemma projective_polar_incidence_iff_lemma {V : Type v} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ∀ X Y : ZornProjectiveDatum.NullRep (concreteZornProjectiveDatum B),
      projective_polar_incidence (R := ℝ) (V := V) B
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B) X)
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B) Y)
        ↔ polarExpr B X.rep Y.rep = 0 :=
  projective_polar_incidence_iff (R := ℝ) (V := V) B

lemma pPlus_incident_upperLightray_lemma {V : Type v} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ∀ {v : V} (hv : v ≠ 0),
      Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pPlusRep (R := ℝ) (V := V) B))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (upperLightrayRep (R := ℝ) (V := V) B hv)) :=
  pPlusIncident_upperLightray_ray (R := ℝ) (V := V) B

lemma pMinus_incident_lowerLightray_lemma {V : Type v} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ∀ {w : V} (hw : w ≠ 0),
      Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pMinusRep (R := ℝ) (V := V) B))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (lowerLightrayRep (R := ℝ) (V := V) B hw)) :=
  pMinusIncident_lowerLightray_ray (R := ℝ) (V := V) B

lemma pPlus_notIncident_pMinus_lemma {V : Type v} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ¬ Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pPlusRep (R := ℝ) (V := V) B))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pMinusRep (R := ℝ) (V := V) B)) :=
  pPlus_notIncident_pMinus_ray (R := ℝ) (V := V) B

lemma upperLightray_incident_lowerLightray_iff_lemma {V : Type v} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ∀ {v w : V} (hv : v ≠ 0) (hw : w ≠ 0),
      Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (upperLightrayRep (R := ℝ) (V := V) B hv))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (lowerLightrayRep (R := ℝ) (V := V) B hw))
        ↔ B v w = 0 :=
  upperLightrayIncident_lowerLightray_iff_ray (R := ℝ) (V := V) B

/--
Repo-facing finite packet for the split-octonion / split-Albert / local-Zorn
boundary lane.

This is a theorem bundle collecting owner facts already proved elsewhere in the
repository. It does not add a new abstract split-Albert projective-plane bridge.
-/
abbrev SplitOctonionBoundaryPacket
    (V : Type v) [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Type _ :=
  Σ' _projective_null_boundary :
      ZornProjectiveDatum.NullRay (concreteZornProjectiveDatum B),
    (∃ x y : AlbertStep ℝ (SplitQuaternion ℝ) (1 : ℝ),
        x ≠ 0 ∧ y ≠ 0 ∧ AlbertStep.mul x y = 0) ∧
      Module.finrank ℝ SplitAlbertCarrier = 27 ∧
      (∀ X Y : ZornCell ℝ V,
        polarZ (concretePolarDatum B) X Y = polarZ (concretePolarDatum B) Y X) ∧
      (∀ X Y : ZornProjectiveDatum.NullRep (concreteZornProjectiveDatum B),
        projective_polar_incidence (R := ℝ) (V := V) B
            (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B) X)
            (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B) Y)
          ↔ polarExpr B X.rep Y.rep = 0) ∧
      (∀ {v : V} (hv : v ≠ 0),
        Incident (concretePolarDatum B)
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
            (pPlusRep (R := ℝ) (V := V) B))
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
            (upperLightrayRep (R := ℝ) (V := V) B hv))) ∧
      (∀ {w : V} (hw : w ≠ 0),
        Incident (concretePolarDatum B)
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
            (pMinusRep (R := ℝ) (V := V) B))
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
            (lowerLightrayRep (R := ℝ) (V := V) B hw))) ∧
      (¬ Incident (concretePolarDatum B)
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
            (pPlusRep (R := ℝ) (V := V) B))
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
            (pMinusRep (R := ℝ) (V := V) B))) ∧
      (∀ {v w : V} (hv : v ≠ 0) (hw : w ≠ 0),
        Incident (concretePolarDatum B)
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
            (upperLightrayRep (R := ℝ) (V := V) B hv))
          (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
            (lowerLightrayRep (R := ℝ) (V := V) B hw))
          ↔ B v w = 0)

namespace SplitOctonionBoundaryPacket

variable {V : Type v} [AddCommGroup V] [Module ℝ V]
variable {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}

abbrev projective_null_boundary (P : SplitOctonionBoundaryPacket V B) := P.1
abbrev split_albert_zero_divisors (P : SplitOctonionBoundaryPacket V B) := P.2.1
abbrev split_albert_finrank_27 (P : SplitOctonionBoundaryPacket V B) := P.2.2.1
abbrev concrete_polar_symm (P : SplitOctonionBoundaryPacket V B) := P.2.2.2.1
abbrev projective_polar_incidence_iff (P : SplitOctonionBoundaryPacket V B) := P.2.2.2.2.1
abbrev pPlus_incident_upperLightray (P : SplitOctonionBoundaryPacket V B) :
    ∀ {v : V} (hv : v ≠ 0),
      Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pPlusRep (R := ℝ) (V := V) B))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (upperLightrayRep (R := ℝ) (V := V) B hv)) :=
  P.2.2.2.2.2.1
abbrev pMinus_incident_lowerLightray (P : SplitOctonionBoundaryPacket V B) :
    ∀ {w : V} (hw : w ≠ 0),
      Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pMinusRep (R := ℝ) (V := V) B))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (lowerLightrayRep (R := ℝ) (V := V) B hw)) :=
  P.2.2.2.2.2.2.1
abbrev pPlus_notIncident_pMinus (P : SplitOctonionBoundaryPacket V B) :
    ¬ Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pPlusRep (R := ℝ) (V := V) B))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (pMinusRep (R := ℝ) (V := V) B)) :=
  P.2.2.2.2.2.2.2.1
abbrev upperLightray_incident_lowerLightray_iff
    (P : SplitOctonionBoundaryPacket V B) :
    ∀ {v w : V} (hv : v ≠ 0) (hw : w ≠ 0),
      Incident (concretePolarDatum B)
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (upperLightrayRep (R := ℝ) (V := V) B hv))
        (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
          (lowerLightrayRep (R := ℝ) (V := V) B hw))
        ↔ B v w = 0 :=
  P.2.2.2.2.2.2.2.2

end SplitOctonionBoundaryPacket

/-- Canonical repository packet for the split-octonion / split-Albert / Zorn boundary lane. -/
def canonicalSplitOctonionBoundaryPacket
    (V : Type v) [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    SplitOctonionBoundaryPacket V B :=
  ⟨ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
      (pPlusRep (R := ℝ) (V := V) B),
    split_albert_zero_divisors_lemma,
    split_albert_finrank_27_lemma,
    concrete_polar_symm_lemma B,
    projective_polar_incidence_iff_lemma B,
    pPlus_incident_upperLightray_lemma B,
    pMinus_incident_lowerLightray_lemma B,
    pPlus_notIncident_pMinus_lemma B,
    upperLightray_incident_lowerLightray_iff_lemma B⟩

/-- The boundary packet exposes its explicit null ray witness. -/
def projective_null_boundary_witness
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (P : SplitOctonionBoundaryPacket V B) :
    ZornProjectiveDatum.NullRay (concreteZornProjectiveDatum B) :=
  SplitOctonionBoundaryPacket.projective_null_boundary P

end InfoGeometry.Projective.SplitOctonions.BoundaryPacket
