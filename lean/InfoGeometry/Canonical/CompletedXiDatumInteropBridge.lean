import InfoGeometry.Canonical.CompletedZetaPotentialSymmetryBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CompletedZetaPotentialAndRealGibbsFisherBridge
import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
import InfoGeometry.Canonical.ActualCompletedXiDatumBridge
import InfoGeometry.Canonical.ActualCenteredXiDataBridge
import InfoGeometry.Canonical.ZetaFunctionalSymmetryNativeBridge

/-!
# Interoperability for completed-Xi symmetry data

The repository contains two deliberately different owners for the same finite
symmetry packet: the canonical modulus-potential owner and the topology/Fisher
owner.  This file only transports their datum structures.  It does not add a
functional equation, a zero-set theorem, or an analytic continuation claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.CompletedXiDatumInteropBridge

abbrev TopologicalDatum (xi : ℂ → ℂ) :=
  InfoGeometry.Topology.CompletedZetaPotentialAndRealGibbsFisherBridge.CompletedXiDatum xi

open InfoGeometry.Canonical.CompletedZetaPotentialSymmetry
open InfoGeometry.Topology.CompletedZetaPotentialAndRealGibbsFisherBridge
open InfoGeometry.Canonical.ZetaFunctionalSymmetryNativeBridge

/-- Transport a topological completed-Xi datum to the canonical owner. -/
def ofTopological {xi : ℂ → ℂ} (D : TopologicalDatum xi) :
    InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum where
  xi := xi
  reflection := D.func_eq
  schwarz := D.schwarz

/-- Transport a canonical completed-Xi datum to the topology owner. -/
def toTopological
    (D : InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum) :
    TopologicalDatum D.xi where
  func_eq := D.reflection
  schwarz := D.schwarz

@[simp] theorem ofTopological_xi {xi : ℂ → ℂ} (D : TopologicalDatum xi) :
    (ofTopological D).xi = xi := rfl

@[simp] theorem toTopological_func_eq
    (D : InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum) (s : ℂ) :
    D.xi (1 - s) = D.xi s :=
  D.reflection s

@[simp] theorem toTopological_schwarz
    (D : InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum) (s : ℂ) :
    D.xi (star s) = star (D.xi s) :=
  D.schwarz s

theorem canonical_logModulusPotential_v4_of_topological
    {xi : ℂ → ℂ} (D : TopologicalDatum xi) (s : ℂ) :
    (logModulusPotential (ofTopological D) (1 - s) =
        logModulusPotential (ofTopological D) s) ∧
    (logModulusPotential (ofTopological D) (star s) =
        logModulusPotential (ofTopological D) s) ∧
    (logModulusPotential (ofTopological D) (1 - star s) =
        logModulusPotential (ofTopological D) s) :=
  logModulusPotential_v4_invariant (ofTopological D) s

theorem topology_xiNormLevelSet_v4_of_canonical
    (D : InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum)
    (r : ℝ) (s : ℂ) :
    ((1 - s) ∈ xiNormLevelSet D.xi r ↔ s ∈ xiNormLevelSet D.xi r) ∧
    ((star s) ∈ xiNormLevelSet D.xi r ↔ s ∈ xiNormLevelSet D.xi r) ∧
    ((1 - star s) ∈ xiNormLevelSet D.xi r ↔ s ∈ xiNormLevelSet D.xi r) :=
  xiNormLevelSet_v4_invariant D.xi (toTopological D) r s

/-- The concrete Mathlib `riemannXi` datum in the canonical owner. -/
def actualCanonicalCompletedXiDatum :
    InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum :=
  { xi := InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi
    reflection := InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi_one_sub
    schwarz := InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge.actualRiemannXi_conj }

@[simp] theorem actualCanonicalCompletedXiDatum_xi (s : ℂ) :
    actualCanonicalCompletedXiDatum.xi s =
      InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi s := rfl

theorem actualCanonicalCompletedXiDatum_v4 (s : ℂ) :
    (Complex.normSq (actualCanonicalCompletedXiDatum.xi (1 - s)) =
        Complex.normSq (actualCanonicalCompletedXiDatum.xi s)) ∧
    (Complex.normSq (actualCanonicalCompletedXiDatum.xi (star s)) =
        Complex.normSq (actualCanonicalCompletedXiDatum.xi s)) ∧
    (Complex.normSq (actualCanonicalCompletedXiDatum.xi (1 - star s)) =
        Complex.normSq (actualCanonicalCompletedXiDatum.xi s)) := by
  exact ⟨xi_normSq_reflection actualCanonicalCompletedXiDatum s,
    xi_normSq_conjugation actualCanonicalCompletedXiDatum s,
    xi_normSq_cpt_mirror actualCanonicalCompletedXiDatum s⟩

theorem actualCanonicalCompletedXiDatum_toTopological_eq :
    toTopological actualCanonicalCompletedXiDatum =
      InfoGeometry.Canonical.ActualCompletedXiDatumBridge.actualCompletedXiDatum_concrete :=
  Subsingleton.elim _ _

/-- Center a canonical completed-Xi datum in the affine coordinate `z`. -/
def centeredData
    (D : InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum) :
    CompletedXiData where
  lambda := D.xi
  xi := fun z => D.xi ((1 / 2 : ℂ) + z)
  xi_def := by intro z; rfl

@[simp] theorem centeredData_lambda
    (D : InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum) (s : ℂ) :
    (centeredData D).lambda s = D.xi s := rfl

@[simp] theorem centeredData_xi
    (D : InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum) (z : ℂ) :
    (centeredData D).xi z = D.xi ((1 / 2 : ℂ) + z) := rfl

theorem centeredData_even_of_reflection
    (D : InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum) (z : ℂ) :
    (centeredData D).xi z = (centeredData D).xi (-z) := by
  rw [centeredData_xi, centeredData_xi]
  have h := D.reflection ((1 / 2 : ℂ) + z)
  have harg : 1 - ((1 / 2 : ℂ) + z) = (1 / 2 : ℂ) + (-z) := by ring
  rw [harg] at h
  exact h.symm

theorem centeredData_conj_of_schwarz
    (D : InfoGeometry.Canonical.CompletedZetaPotentialSymmetry.CompletedXiDatum) (z : ℂ) :
    (centeredData D).xi (star z) =
      star ((centeredData D).xi z) := by
  rw [centeredData_xi, centeredData_xi]
  have h := D.schwarz ((1 / 2 : ℂ) + z)
  have harg : star ((1 / 2 : ℂ) + z) = (1 / 2 : ℂ) + star z := by
    apply Complex.ext <;> simp
  rw [harg] at h
  exact h

theorem actualCenteredXiData_eq_centeredData_fields :
    InfoGeometry.Canonical.ActualCenteredXiDataBridge.actualCenteredXiData.lambda =
        actualCanonicalCompletedXiDatum.xi ∧
      InfoGeometry.Canonical.ActualCenteredXiDataBridge.actualCenteredXiData.xi =
        (centeredData actualCanonicalCompletedXiDatum).xi := by
  constructor <;> funext z <;> rfl

theorem actualCenteredXiData_centered_symmetry_packet (z : ℂ) :
    (centeredData actualCanonicalCompletedXiDatum).xi z =
        (centeredData actualCanonicalCompletedXiDatum).xi (-z) ∧
      (centeredData actualCanonicalCompletedXiDatum).xi (star z) =
        star ((centeredData actualCanonicalCompletedXiDatum).xi z) := by
  exact ⟨centeredData_even_of_reflection actualCanonicalCompletedXiDatum z,
    centeredData_conj_of_schwarz actualCanonicalCompletedXiDatum z⟩

end InfoGeometry.Canonical.CompletedXiDatumInteropBridge
