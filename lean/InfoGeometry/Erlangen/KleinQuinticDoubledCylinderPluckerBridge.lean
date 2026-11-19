/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Erlangen.KleinQuinticDoubledCylinderRepresentation
import InfoGeometry.Erlangen.KleinQuinticGrassmannPluckerBridge
import InfoGeometry.Erlangen.KleinQuinticVietaBinaryBridge

/-!
# Quintic Orbit Cylinders as Grassmann–Plücker Data

The Apollonius-specific signed orbit representation is already embedded in
the repository's doubled depth-three Cantor-cylinder fibers. This module
reads the selected squared orbit coordinates from those fibers, forms the
same `Gr(2,4)` row chart, and proves that its Plücker point is exactly the
quotient-level Klein point constructed from the binary-quintic coefficients.
All assertions remain at the actual finite five-coordinate/stage-three
carriers; no limit passage or analytic Cantor-space assertion is made.
-/

noncomputable section

namespace InfoGeometry.Erlangen.KleinQuinticDoubledCylinderPluckerBridge

open InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
open InfoGeometry.Erlangen.KleinApolloniusQuinticResolvent
open InfoGeometry.Erlangen.KleinQuinticDoubledCylinderRepresentation
open InfoGeometry.Erlangen.KleinQuinticGrassmannPluckerBridge
open InfoGeometry.Erlangen.KleinQuinticVietaBinaryBridge
open InfoGeometry.Erlangen.KleinQuinticTschirnhausKleinCovariant
open InfoGeometry.Projective.KleinQuadricPlucker

/-- A selected squared root read from the actual doubled Cantor-cylinder
fiber carrying the Apollonius orbit quotient. -/
def doubledCylinderSelectedRoot (ξ θ : ℝ)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker
        (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ)))
    (pick : Fin 4 → Fin 5) (i : Fin 4) : ℂ :=
  (doubledCylinderComplexReadout
    (apolloniusQuotientToDoubledCylinder ξ θ q
      (quinticCylinderAddress (pick i)))) ^ 2

/-- The `Gr(2,4)` chart obtained by reading four squared roots from the
Apollonius doubled-cylinder representation. -/
def doubledCylinderGrassmannRows (ξ θ : ℝ)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker
        (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ)))
    (pick : Fin 4 → Fin 5) : Vec4 ℂ × Vec4 ℂ :=
  (⟨1, 1, 1, 1⟩,
   ⟨doubledCylinderSelectedRoot ξ θ q pick 0,
    doubledCylinderSelectedRoot ξ θ q pick 1,
    doubledCylinderSelectedRoot ξ θ q pick 2,
    doubledCylinderSelectedRoot ξ θ q pick 3⟩)

/-- Plücker readout of the selected doubled-cylinder Grassmann chart. -/
def doubledCylinderPlucker6 (ξ θ : ℝ)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker
        (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ)))
    (pick : Fin 4 → Fin 5) : Plucker6 ℂ :=
  Plucker6.pluckerLine
    (doubledCylinderGrassmannRows ξ θ q pick).1
    (doubledCylinderGrassmannRows ξ θ q pick).2

/-- **Cylinder-to-Klein identification.** Reading the selected squared roots
from the doubled Cantor-cylinder fibers gives exactly the quotient-level
Plücker point of the source-ordered binary quintic. The proof descends to
the coefficient quotient; it does not choose a representative. -/
theorem doubledCylinderPlucker6_eq_orbitQuotientPlucker6
    (ξ θ : ℝ) (pick : Fin 4 → Fin 5)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker
        (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ))) :
    doubledCylinderPlucker6 ξ θ q pick =
      binaryQuinticOrbitQuotientPlucker6
        (apolloniusBinaryQuinticPoint ξ θ) pick q := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro v
  have hEval := apollonius_quotient_equiv_apply_mk ξ θ v
  have hEval' :
      binaryQuinticAffineOrbitQuotientEquiv
          (apollonius_parameter_ne_zero ξ θ) (Submodule.Quotient.mk v) =
        binaryQuinticOrbitEvaluation
          (apolloniusBinaryQuinticPoint ξ θ) v := by
    simpa [apolloniusBinaryQuinticPoint] using hEval
  have hread (i : Fin 4) :
      doubledCylinderComplexReadout
          (apolloniusQuotientToDoubledCylinder ξ θ
            (Submodule.Quotient.mk v) (quinticCylinderAddress (pick i))) =
        binaryQuinticOrbitEvaluation
          (apolloniusBinaryQuinticPoint ξ θ) v (pick i) := by
    unfold apolloniusQuotientToDoubledCylinder
    have hread := congrArg
      (fun r : BrioschiRootCoordinateSpace =>
        doubledCylinderComplexReadout
          (apolloniusOrbitInDoubledCylinder r
            (quinticCylinderAddress (pick i)))) hEval'
    calc
      doubledCylinderComplexReadout
          (apolloniusOrbitInDoubledCylinder
            (binaryQuinticAffineOrbitQuotientEquiv
              (apollonius_parameter_ne_zero ξ θ) (Submodule.Quotient.mk v))
            (quinticCylinderAddress (pick i))) =
          doubledCylinderComplexReadout
            (apolloniusOrbitInDoubledCylinder
              (binaryQuinticOrbitEvaluation
                (apolloniusBinaryQuinticPoint ξ θ) v)
              (quinticCylinderAddress (pick i))) := hread
      _ = binaryQuinticOrbitEvaluation
          (apolloniusBinaryQuinticPoint ξ θ) v (pick i) :=
        doubledCylinderComplexReadout_orbit _ _
  have hroot (i : Fin 4) :
      doubledCylinderSelectedRoot ξ θ (Submodule.Quotient.mk v) pick i =
        resolventSubconfiguration v (apolloniusBinaryQuinticPoint ξ θ) pick i := by
    unfold doubledCylinderSelectedRoot
    rw [hread i]
    rfl
  apply Plucker6.ext <;>
    simp [doubledCylinderPlucker6, doubledCylinderGrassmannRows,
      hroot, binaryQuinticOrbitQuotientPlucker6_mk,
      binaryQuinticResolventPlucker6, resolventGrassmannRows,
      resolventSubconfiguration, Plucker6.pluckerLine]

/-- On an explicit coefficient representative, the doubled-cylinder
Plücker readout is exactly the selected squared-orbit Plücker construction
in the binary-quintic owner. This is the representative-level map between
the doubled real cylinder fibers and the complex five-coordinate
representation; it makes no choice of a quintic root ordering. -/
theorem doubledCylinderPlucker6_eq_resolventPlucker6_on_mk
    (ξ θ : ℝ) (pick : Fin 4 → Fin 5)
    (v : BinaryQuinticCoefficientSpace) :
    doubledCylinderPlucker6 ξ θ (Submodule.Quotient.mk v) pick =
      binaryQuinticResolventPlucker6 v
        (apolloniusBinaryQuinticPoint ξ θ) pick := by
  rw [doubledCylinderPlucker6_eq_orbitQuotientPlucker6]
  exact binaryQuinticOrbitQuotientPlucker6_mk
    (apolloniusBinaryQuinticPoint ξ θ) pick v

/-- The squared root evaluation at the `k`th Klein orbit point. This is the
explicit root-side form of the resolvent coordinate stored in the cylinder.
The homogeneous expression also covers orbit points at infinity. -/
def rootTupleOrbitSquaredValue (x : Fin 5 → ℂ) (z : ℂ × ℂ)
    (k : Fin 5) : ℂ :=
  (∏ i : Fin 5, ((kleinOrderFiveIterate k.val z).2 -
    x i * (kleinOrderFiveIterate k.val z).1)) ^ 2

/-- Vieta evaluation followed by the signed five-orbit action and squaring
is exactly the homogeneous product of the five root factors at that orbit
point. -/
theorem rootTupleResolventTuple_eq_rootOrbitSquaredValue
    (x : Fin 5 → ℂ) (z : ℂ × ℂ) (k : Fin 5) :
    binaryQuinticResolventTuple (rootTupleBinaryQuintic x) z k =
      rootTupleOrbitSquaredValue x z k := by
  exact rootTupleResolventTuple_eq_homogeneous_root_values x z k

/-- The doubled-cylinder Plücker point on a Vieta representative is the
Plücker point of the four selected homogeneous root-product resolvent
coordinates. This completes the explicit finite carrier chain from ordered
roots through the binary-quintic orbit representation into the doubled
Cantor-cylinder fibers. -/
theorem doubledCylinderPlucker6_rootTupleVieta
    (ξ θ : ℝ) (pick : Fin 4 → Fin 5) (x : Fin 5 → ℂ) :
    doubledCylinderPlucker6 ξ θ
        (Submodule.Quotient.mk (rootTupleBinaryQuintic x)) pick =
      Plucker6.pluckerLine
        (⟨1, 1, 1, 1⟩ : Vec4 ℂ)
        ⟨rootTupleOrbitSquaredValue x (apolloniusBinaryQuinticPoint ξ θ)
            (pick 0),
          rootTupleOrbitSquaredValue x (apolloniusBinaryQuinticPoint ξ θ)
            (pick 1),
          rootTupleOrbitSquaredValue x (apolloniusBinaryQuinticPoint ξ θ)
            (pick 2),
          rootTupleOrbitSquaredValue x (apolloniusBinaryQuinticPoint ξ θ)
            (pick 3)⟩ := by
  rw [doubledCylinderPlucker6_eq_resolventPlucker6_on_mk]
  apply Plucker6.ext <;>
    simp [binaryQuinticResolventPlucker6, resolventGrassmannRows,
      resolventSubconfiguration, rootTupleOrbitSquaredValue,
      rootTupleResolventTuple_eq_homogeneous_root_values,
      Plucker6.pluckerLine]

/-- Send an `S₅`-orbit class of ordered roots to the coefficient-quotient
class seen by the Apollonius signed-orbit evaluation. The quotient-to-image
map is used first, so this transports an already defined root class and does
not choose a representative root ordering. -/
noncomputable def rootReindexingQuotientToApolloniusOrbitClass
    (ξ θ : ℝ) :
    Quotient rootReindexingSetoid →
      BinaryQuinticCoefficientSpace ⧸
        LinearMap.ker
          (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ)) :=
  fun q => Submodule.Quotient.mk (rootQuotientToVietaImage q).val

/-- **Root quotient / signed-orbit / cylinder compatibility.** The
Plücker point obtained by mapping an ordered-root orbit class through Vieta
and then into the doubled Cantor cylinders is exactly the Plücker point
obtained from its class in the Apollonius signed-orbit quotient. This is the
commuting carrier bridge; its Klein geometry is the squared evaluation
resolvent chart, not the distinct root-only Tschirnhaus covariant. -/
theorem rootReindexingQuotientToCylinderPlucker6_commutes
    (ξ θ : ℝ) (pick : Fin 4 → Fin 5)
    (q : Quotient rootReindexingSetoid) :
    doubledCylinderPlucker6 ξ θ
        (rootReindexingQuotientToApolloniusOrbitClass ξ θ q) pick =
      binaryQuinticOrbitQuotientPlucker6
        (apolloniusBinaryQuinticPoint ξ θ) pick
        (rootReindexingQuotientToApolloniusOrbitClass ξ θ q) := by
  refine Quotient.inductionOn q ?_
  intro x
  rw [rootReindexingQuotientToApolloniusOrbitClass,
    rootQuotientToVietaImage_mk]
  rw [doubledCylinderPlucker6_eq_resolventPlucker6_on_mk,
    binaryQuinticOrbitQuotientPlucker6_mk]

/-- The cylinder-readout Plücker point lies on Klein's quadric because it is
the same decomposable bivector as the coefficient-quotient construction. -/
theorem doubledCylinderPlucker6_on_klein
    (ξ θ : ℝ) (pick : Fin 4 → Fin 5)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker
        (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ))) :
    Plucker6.kleinQ (doubledCylinderPlucker6 ξ θ q pick) = 0 := by
  rw [doubledCylinderPlucker6_eq_orbitQuotientPlucker6]
  exact binaryQuinticOrbitQuotientPlucker6_on_klein
    (apolloniusBinaryQuinticPoint ξ θ) pick q

/-- **Apollonius–Brioschi–Cantor–Klein endpoint.** A noncanonical
Apollonius specialization realizes the Brioschi resolvent in the actual
doubled-cylinder fibers; the same coefficient class, passed through the
existing four-row Grassmann chart, yields a point on Klein's quadric. This
is a finite-stage existence bridge and makes no claim of a canonical root
ordering or a projective coefficient-to-root section. -/
theorem exists_apollonius_brioschi_cylinder_klein_point :
    ∃ ξ θ : ℝ, ∃ v : BinaryQuinticCoefficientSpace,
      doubledCylinderEvaluationResolvent
          (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ) v) =
        brioschiResolvent (brioschiParameter
          (apolloniusBinaryQuinticPoint ξ θ).1
          (apolloniusBinaryQuinticPoint ξ θ).2) ∧
      Plucker6.kleinQ (doubledCylinderPlucker6 ξ θ
        (Submodule.Quotient.mk v) (fun i : Fin 4 => ⟨i.val, by omega⟩)) = 0 := by
  obtain ⟨ξ, θ, v, hres⟩ :=
    exists_apollonius_doubledCylinder_brioschiResolvent
  refine ⟨ξ, θ, v, hres, ?_⟩
  exact doubledCylinderPlucker6_on_klein ξ θ
    (fun i : Fin 4 => ⟨i.val, by omega⟩) (Submodule.Quotient.mk v)

/-- **Indexed Brioschi roots in the Apollonius Cantor-cylinder Klein chart.**
At a nondegenerate Apollonius parameter there is a source quintic whose
squared signed-orbit tuple agrees index-by-index with Klein's five Brioschi
orbit roots. Consequently the cylinder's Brioschi resolvent is the displayed
Brioschi quintic, and its selected `Gr(2,4)` Plücker readout is exactly the
chart formed from the corresponding four Brioschi roots. The coefficient
vector and Apollonius parameter are existential; no global or equivariant
root selection is asserted. -/
theorem exists_apollonius_brioschi_cylinder_klein_chart
    (pick : Fin 4 → Fin 5) :
    ∃ ξ θ : ℝ, ∃ v : BinaryQuinticCoefficientSpace,
      binaryQuinticResolventTuple v (apolloniusBinaryQuinticPoint ξ θ) =
        kleinBrioschiRootTuple (apolloniusBinaryQuinticPoint ξ θ) ∧
      binaryQuinticResolventOmega5 v (apolloniusBinaryQuinticPoint ξ θ) =
        rootKleinOmega5 (kleinBrioschiRootTuple
          (apolloniusBinaryQuinticPoint ξ θ)) ∧
      doubledCylinderEvaluationResolvent
          (binaryQuinticOrbitEvaluation
            (apolloniusBinaryQuinticPoint ξ θ) v) =
        brioschiResolvent (brioschiParameter
          (apolloniusBinaryQuinticPoint ξ θ).1
          (apolloniusBinaryQuinticPoint ξ θ).2) ∧
      doubledCylinderPlucker6 ξ θ (Submodule.Quotient.mk v) pick =
        Plucker6.pluckerLine
          (⟨1, 1, 1, 1⟩ : Vec4 ℂ)
          ⟨kleinBrioschiRootTuple
              (apolloniusBinaryQuinticPoint ξ θ) (pick 0),
            kleinBrioschiRootTuple
              (apolloniusBinaryQuinticPoint ξ θ) (pick 1),
            kleinBrioschiRootTuple
              (apolloniusBinaryQuinticPoint ξ θ) (pick 2),
            kleinBrioschiRootTuple
              (apolloniusBinaryQuinticPoint ξ θ) (pick 3)⟩ := by
  obtain ⟨t, hT, hinj, _hOrbit⟩ :=
    exists_kleinBrioschiOrbitPolynomial_eq_resolvent_specialization
  have ht : t ≠ 0 := by
    intro hzero
    subst t
    exact kleinBrioschiRootTuple_not_injective_degenerate hinj
  obtain ⟨v, htuple, hres, hOmega⟩ :=
    exists_binaryQuinticResolventTuple_eq_kleinBrioschiRootTuple
      (1, t) (kleinOrderFiveAffineOrbit_first_ne_zero t)
      (kleinOrderFiveAffineOrbit_nodes_injective ht) hT hinj
  obtain ⟨ξ, θ, hpoint⟩ :=
    exists_apollonius_coordinates_for_nonzero_parameter t ht
  have htuplePoint :
      binaryQuinticResolventTuple v (apolloniusBinaryQuinticPoint ξ θ) =
        kleinBrioschiRootTuple (apolloniusBinaryQuinticPoint ξ θ) := by
    rw [hpoint]
    exact htuple
  have hOmegaPoint :
      binaryQuinticResolventOmega5 v (apolloniusBinaryQuinticPoint ξ θ) =
        rootKleinOmega5 (kleinBrioschiRootTuple
          (apolloniusBinaryQuinticPoint ξ θ)) := by
    rw [hpoint]
    exact hOmega
  have hresPoint :
      binaryQuinticEvaluationResolvent v
          (apolloniusBinaryQuinticPoint ξ θ) =
        brioschiResolvent (brioschiParameter
          (apolloniusBinaryQuinticPoint ξ θ).1
          (apolloniusBinaryQuinticPoint ξ θ).2) := by
    rw [hpoint]
    exact hres
  refine ⟨ξ, θ, v, htuplePoint, hOmegaPoint, ?_, ?_⟩
  · exact (apolloniusDoubledCylinderResolvent_eq_evaluationResolvent
      ξ θ v).trans hresPoint
  · rw [doubledCylinderPlucker6_eq_resolventPlucker6_on_mk]
    rw [hpoint]
    apply Plucker6.ext <;>
      simp [binaryQuinticResolventPlucker6, resolventGrassmannRows,
        resolventSubconfiguration, htuple, Plucker6.pluckerLine]

end InfoGeometry.Erlangen.KleinQuinticDoubledCylinderPluckerBridge
