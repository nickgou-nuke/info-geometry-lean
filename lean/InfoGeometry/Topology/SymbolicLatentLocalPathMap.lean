import Mathlib
import InfoGeometry.Topology.SymbolicLatentLocalPath

namespace InfoGeometry.Topology

/-!
Continuous maps between selected chart domains and their action on local paths.
The domain-preservation property is explicit; it is not inferred from
continuity alone.
-/

structure SymbolicLatentLocalChartMap
    (X Y κ : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ} where
  sourceChart : κ
  targetChart : κ
  toFun : X → Y
  continuous_toFun : Continuous toFun
  map_domain : ∀ x, x ∈ C.domain sourceChart →
    toFun x ∈ D.domain targetChart

def SymbolicLatentLocalChartMap.mapPath
    {X Y κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (γ : SymbolicLatentLocalPath X κ C)
    (hγ : γ.chart = F.sourceChart) :
    SymbolicLatentLocalPath Y κ D :=
  ⟨⟨F.targetChart, {
    toFun := fun t => F.toFun (γ.path t)
    continuous_toFun := F.continuous_toFun.comp γ.path.continuous
  }⟩, by
    intro t
    have hstay := γ.stays_in_chart t
    rw [hγ] at hstay
    exact F.map_domain (γ.path t) hstay⟩

theorem SymbolicLatentLocalChartMap.mapPath_apply
    {X Y κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (γ : SymbolicLatentLocalPath X κ C)
    (hγ : γ.chart = F.sourceChart)
    (t : SymbolicPathDomain) :
    (F.mapPath γ hγ).path t = F.toFun (γ.path t) := rfl

theorem SymbolicLatentLocalChartMap.mapPath_start
    {X Y κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (γ : SymbolicLatentLocalPath X κ C)
    (hγ : γ.chart = F.sourceChart) :
    (F.mapPath γ hγ).path.start = F.toFun γ.path.start := rfl

theorem SymbolicLatentLocalChartMap.mapPath_finish
    {X Y κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (γ : SymbolicLatentLocalPath X κ C)
    (hγ : γ.chart = F.sourceChart) :
    (F.mapPath γ hγ).path.finish = F.toFun γ.path.finish := rfl

def SymbolicLatentLocalChartMap.id
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (k : κ) :
    SymbolicLatentLocalChartMap X X κ (C := C) (D := C) where
  sourceChart := k
  targetChart := k
  toFun := fun x => x
  continuous_toFun := continuous_id
  map_domain := by
    intro x hx
    exact hx

theorem SymbolicLatentLocalChartMap.id_apply
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (k : κ) (x : X) :
    (SymbolicLatentLocalChartMap.id (C := C) k).toFun x = x := by
  rfl

theorem SymbolicLatentLocalChartMap.id_mapPath_apply
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (k : κ) (γ : SymbolicLatentLocalPath X κ C)
    (hγ : γ.chart = k)
    (t : SymbolicPathDomain) :
    ((SymbolicLatentLocalChartMap.id (C := C) k).mapPath γ
      (by simpa [SymbolicLatentLocalChartMap.id] using hγ)).path t =
      γ.path t := rfl

def SymbolicLatentLocalChartMap.comp
    {X Y Z κ : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    {E : SymbolicLatentOpenCover Z κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (G : SymbolicLatentLocalChartMap Y Z κ (C := D) (D := E))
    (h : F.targetChart = G.sourceChart) :
    SymbolicLatentLocalChartMap X Z κ (C := C) (D := E) where
  sourceChart := F.sourceChart
  targetChart := G.targetChart
  toFun := fun x => G.toFun (F.toFun x)
  continuous_toFun := G.continuous_toFun.comp F.continuous_toFun
  map_domain := by
    intro x hx
    have hF : F.toFun x ∈ D.domain F.targetChart := F.map_domain x hx
    rw [h] at hF
    exact G.map_domain (F.toFun x) hF

theorem SymbolicLatentLocalChartMap.comp_apply
    {X Y Z κ : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    {E : SymbolicLatentOpenCover Z κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (G : SymbolicLatentLocalChartMap Y Z κ (C := D) (D := E))
    (h : F.targetChart = G.sourceChart) (x : X) :
    (F.comp G h).toFun x = G.toFun (F.toFun x) := rfl

theorem SymbolicLatentLocalChartMap.comp_mapPath_apply
    {X Y Z κ : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    {E : SymbolicLatentOpenCover Z κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (G : SymbolicLatentLocalChartMap Y Z κ (C := D) (D := E))
    (h : F.targetChart = G.sourceChart)
    (γ : SymbolicLatentLocalPath X κ C)
    (hγ : γ.chart = F.sourceChart) (t : SymbolicPathDomain) :
    ((F.comp G h).mapPath γ hγ).path t =
      G.toFun (F.toFun (γ.path t)) := rfl

theorem SymbolicLatentLocalChartMap.comp_id_apply
    {X Y κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (x : X) :
    (F.comp (SymbolicLatentLocalChartMap.id (C := D) F.targetChart)
      (by simp [SymbolicLatentLocalChartMap.id])).toFun x =
      F.toFun x := rfl

theorem SymbolicLatentLocalChartMap.id_comp_apply
    {X Y κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (x : X) :
    ((SymbolicLatentLocalChartMap.id (C := C) F.sourceChart).comp F
      (by simp [SymbolicLatentLocalChartMap.id])).toFun x =
      F.toFun x := rfl

theorem SymbolicLatentLocalChartMap.comp_assoc_apply
    {W X Y Z κ : Type*}
    [TopologicalSpace W] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype κ]
    {A : SymbolicLatentOpenCover W κ}
    {B : SymbolicLatentOpenCover X κ}
    {C : SymbolicLatentOpenCover Y κ}
    {D : SymbolicLatentOpenCover Z κ}
    (F : SymbolicLatentLocalChartMap W X κ (C := A) (D := B))
    (G : SymbolicLatentLocalChartMap X Y κ (C := B) (D := C))
    (H : SymbolicLatentLocalChartMap Y Z κ (C := C) (D := D))
    (hFG : F.targetChart = G.sourceChart)
    (hGH : G.targetChart = H.sourceChart)
    (x : W) :
    ((F.comp G hFG).comp H hGH).toFun x =
      (F.comp (G.comp H hGH) hFG).toFun x := rfl

end InfoGeometry.Topology
