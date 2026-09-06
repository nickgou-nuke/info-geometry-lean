import Mathlib
import InfoGeometry.Topology.SymbolicLatentBasedLoopPath
import InfoGeometry.Topology.SymbolicLatentPathFunctoriality
import InfoGeometry.Topology.SymbolicLatentPathConcatenationNaturality

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Functoriality of symbolic-latent based-loop paths

A continuous map sending a basepoint `x` to `y` transports based-loop paths
from `x` to based-loop paths from `y`.  This is the path-level transport
layer behind the quotient-based loop fiber bridge.
-/

def mapSymbolicLatentBasedLoopPath
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y) :
    SymbolicLatentBasedLoopPath x → SymbolicLatentBasedLoopPath y :=
  fun γ =>
    ⟨mapSymbolicLatentPathContinuous f f.continuous γ.1, by
      constructor
      · calc
          (mapSymbolicLatentPathContinuous f f.continuous γ.1).start
              = f γ.1.start := by
                  rfl
          _ = f x := by rw [γ.2.1]
          _ = y := hxy
      · calc
          (mapSymbolicLatentPathContinuous f f.continuous γ.1).finish
              = f γ.1.finish := by
                  rfl
          _ = f x := by rw [γ.2.2]
          _ = y := hxy⟩

theorem mapSymbolicLatentBasedLoopPath_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (γ : SymbolicLatentBasedLoopPath x) :
    (mapSymbolicLatentBasedLoopPath f hxy γ).1 =
      mapSymbolicLatentPathContinuous f f.continuous γ.1 :=
  rfl

theorem mapSymbolicLatentBasedLoopPath_constant
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    mapSymbolicLatentBasedLoopPath f (x := x) (y := f x) rfl
        (⟨constantSymbolicLatentPath x, by constructor <;> rfl⟩) =
      ⟨constantSymbolicLatentPath (f x), by constructor <;> rfl⟩ := by
  rfl

theorem continuous_mapSymbolicLatentBasedLoopPath
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y) :
    Continuous (mapSymbolicLatentBasedLoopPath f hxy) := by
  unfold mapSymbolicLatentBasedLoopPath
  refine Continuous.subtype_mk
    ((ContinuousMap.continuous_postcomp (X := SymbolicPathDomain) f).comp
      continuous_subtype_val)
    (fun γ => by
      constructor
      · change f (SymbolicLatentPath.start γ.1) = y
        exact (congrArg f γ.2.1).trans hxy
      · change f (SymbolicLatentPath.finish γ.1) = y
        exact (congrArg f γ.2.2).trans hxy)

def symbolicLatentBasedLoopPathTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y) :
    TopCat.of (SymbolicLatentBasedLoopPath x) ⟶
      TopCat.of (SymbolicLatentBasedLoopPath y) :=
  TopCat.ofHom
    { toFun := mapSymbolicLatentBasedLoopPath f hxy
      continuous_toFun := continuous_mapSymbolicLatentBasedLoopPath f hxy }

theorem symbolicLatentBasedLoopPathTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (γ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentBasedLoopPathTopCatHom f hxy γ =
      mapSymbolicLatentBasedLoopPath f hxy γ :=
  rfl

theorem symbolicLatentBasedLoopPathTopCatHom_id
    {X : Type} [TopologicalSpace X] {x : X} :
    symbolicLatentBasedLoopPathTopCatHom (ContinuousMap.id X) (x := x) (y := x) rfl =
      𝟙 (TopCat.of (SymbolicLatentBasedLoopPath x)) := by
  ext γ t
  rfl

theorem mapSymbolicLatentBasedLoopPath_id
    {X : Type} [TopologicalSpace X]
    {x : X} (γ : SymbolicLatentBasedLoopPath x) :
    mapSymbolicLatentBasedLoopPath (ContinuousMap.id X) (x := x) (y := x) rfl γ = γ := by
  apply Subtype.ext
  ext t
  exact congrArg (fun p => p t) (mapSymbolicLatentPathContinuous_id γ.1)

theorem mapSymbolicLatentBasedLoopPath_comp
    {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (γ : SymbolicLatentBasedLoopPath x) :
    mapSymbolicLatentBasedLoopPath g hyz
      (mapSymbolicLatentBasedLoopPath f hxy γ) =
      mapSymbolicLatentBasedLoopPath (g.comp f)
        ((congrArg g hxy).trans hyz) γ := by
  apply Subtype.ext
  ext t
  exact congrArg (fun p => p t)
    (mapSymbolicLatentPathContinuous_comp f g f.continuous g.continuous γ.1).symm

theorem mapSymbolicLatentBasedLoopPath_comp_apply
    {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (γ : SymbolicLatentBasedLoopPath x) :
    mapSymbolicLatentBasedLoopPath g hyz
      (mapSymbolicLatentBasedLoopPath f hxy γ) =
      mapSymbolicLatentBasedLoopPath (g.comp f)
        ((congrArg g hxy).trans hyz) γ := by
  exact mapSymbolicLatentBasedLoopPath_comp f g hxy hyz γ

theorem symbolicLatentBasedLoopPathTopCatHom_comp
    {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z) :
    symbolicLatentBasedLoopPathTopCatHom f hxy ≫
        symbolicLatentBasedLoopPathTopCatHom g hyz =
      symbolicLatentBasedLoopPathTopCatHom (g.comp f)
        ((congrArg g hxy).trans hyz) := by
  ext γ t
  exact congrArg (fun q => q.1 t)
    (mapSymbolicLatentBasedLoopPath_comp f g hxy hyz γ)

theorem mapSymbolicLatentBasedLoopPath_canonicalSymbolicLatentBasedLoopConcatenation
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (γ₀ γ₁ : SymbolicLatentBasedLoopPath x) :
    mapSymbolicLatentBasedLoopPath f hxy
        (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁) =
      canonicalSymbolicLatentBasedLoopConcatenation
        (mapSymbolicLatentBasedLoopPath f hxy γ₀)
        (mapSymbolicLatentBasedLoopPath f hxy γ₁) := by
  apply Subtype.ext
  exact mapSymbolicLatentPathContinuous_canonicalSymbolicConcatenation
    f f.continuous
    (γ₀.2.2.trans γ₁.2.1.symm)
    (by
      rw [mapSymbolicLatentPathContinuous_finish,
        mapSymbolicLatentPathContinuous_start,
        γ₀.2.2, γ₁.2.1])

end InfoGeometry.Topology
