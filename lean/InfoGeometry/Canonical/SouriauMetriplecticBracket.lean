import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.PathConnected
import InfoGeometry.Geometry.MetriplecticKahlerInterfaces

/-!
# Souriau metriplectic bracket

The canonical owner is the generic `MetriplecticStructure` in
`Geometry.MetriplecticKahlerInterfaces`.  This module exposes its observable
bracket and the first- and second-law consequences without introducing a
coordinate model of a coadjoint orbit.
-/

namespace SouriauMetriplectic

variable {Obs X : Type*}

abbrev Data (Obs : Type*) :=
  InfoGeometry.Geometry.MetriplecticStructure Obs ℝ

def bracket (D : Data Obs) (a h : Obs) : ℝ :=
  D.poisson a h + D.metric a D.S

def metriplecticBracket (D : Data Obs) (a h : Obs) : ℝ :=
  bracket D a h

def metriplecticEvolution (D : Data Obs) (dH dS dA : Obs) : ℝ :=
  D.poisson dA dH + D.metric dA dS

theorem bracket_energy_observable_zero (D : Data Obs) (h : Obs) :
    D.poisson D.H h + D.metric D.H D.S = D.poisson D.H h := by
  rw [D.metric_H_casimir, add_zero]

theorem continuous_metriplecticEvolution_of
    [TopologicalSpace Obs] [TopologicalSpace X]
    (D : Data Obs)
    (dH dS dA : X → Obs)
    (hH : Continuous dH) (hS : Continuous dS) (hA : Continuous dA)
    (hPoisson : Continuous (fun p : Obs × Obs => D.poisson p.1 p.2))
    (hMetric : Continuous (fun p : Obs × Obs => D.metric p.1 p.2)) :
    Continuous (fun x : X => metriplecticEvolution D (dH x) (dS x) (dA x)) := by
  have hHamiltonian : Continuous (fun x : X => D.poisson (dA x) (dH x)) :=
    hPoisson.comp (hA.prodMk hH)
  have hDissipative : Continuous (fun x : X => D.metric (dA x) (dS x)) :=
    hMetric.comp (hA.prodMk hS)
  exact hHamiltonian.add hDissipative

theorem isClosed_metriplecticEvolution_level_set
    [TopologicalSpace Obs] [TopologicalSpace X]
    (D : Data Obs)
    (dH dS dA : X → Obs)
    (hH : Continuous dH) (hS : Continuous dS) (hA : Continuous dA)
    (hPoisson : Continuous (fun p : Obs × Obs => D.poisson p.1 p.2))
    (hMetric : Continuous (fun p : Obs × Obs => D.metric p.1 p.2))
    (c : ℝ) :
    IsClosed {x : X |
      metriplecticEvolution D (dH x) (dS x) (dA x) = c} := by
  exact isClosed_singleton.preimage
    (continuous_metriplecticEvolution_of D dH dS dA hH hS hA hPoisson hMetric)

theorem isCompact_metriplecticEvolution_image_of_compact
    [TopologicalSpace Obs] [TopologicalSpace X]
    (D : Data Obs) (K : Set X) (hK : IsCompact K)
    (dH dS dA : X → Obs)
    (hH : Continuous dH) (hS : Continuous dS) (hA : Continuous dA)
    (hPoisson : Continuous (fun p : Obs × Obs => D.poisson p.1 p.2))
    (hMetric : Continuous (fun p : Obs × Obs => D.metric p.1 p.2)) :
    IsCompact (Set.range (fun x : K =>
      metriplecticEvolution D (dH x.1) (dS x.1) (dA x.1))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompact_range
    ((continuous_metriplecticEvolution_of D dH dS dA hH hS hA hPoisson hMetric).comp
      continuous_subtype_val)

theorem isPathConnected_metriplecticEvolution_image_of_pathConnected
    [TopologicalSpace Obs] [TopologicalSpace X]
    (D : Data Obs) (K : Set X) (hK : IsPathConnected K)
    (dH dS dA : X → Obs)
    (hH : Continuous dH) (hS : Continuous dS) (hA : Continuous dA)
    (hPoisson : Continuous (fun p : Obs × Obs => D.poisson p.1 p.2))
    (hMetric : Continuous (fun p : Obs × Obs => D.metric p.1 p.2)) :
    IsPathConnected (Set.range (fun x : K =>
      metriplecticEvolution D (dH x.1) (dS x.1) (dA x.1))) := by
  have hdom : IsPathConnected (Set.univ : Set K) := by
    simpa using hK.preimage_coe (U := K) (W := K) Set.Subset.rfl
  simpa [Set.image_univ, Set.range_comp] using
    hdom.image
      ((continuous_metriplecticEvolution_of D dH dS dA hH hS hA hPoisson hMetric).comp
        continuous_subtype_val)

end SouriauMetriplectic
