/-
  Algebraic homology interface for the Lean 4 spectral port.

  This downstream port reuses the repository-owned `HomologyTheory` carrier.
  It does not assert a topological realization or parametrized homology.
-/

import InfoGeometry.Spectral.Cohomology.Basic

namespace InfoGeometry.Spectral.Homology.Basic

open InfoGeometry.Spectral.Cohomology.Basic

universe u

abbrev HomologyTheory := InfoGeometry.Spectral.Cohomology.Basic.HomologyTheory

namespace HomologyTheory

variable {T : HomologyTheory}

/-- Homology at a degree and with a chosen underlying carrier. -/
abbrev homology (T : HomologyTheory) (n : ℤ) (X : Type u) : Type u :=
  T.carrier n X

/-- The map induced by a map of carriers. -/
abbrev homologyMap (T : HomologyTheory) {n : ℤ} {X Y : Type u}
    (f : X → Y) : homology T n X → homology T n Y :=
  T.map f

@[simp]
theorem homologyMap_id (n : ℤ) (X : Type u) (x : homology T n X) :
    homologyMap T id x = x :=
  T.map_id n X x

theorem homologyMap_comp {n : ℤ} {X Y Z : Type u}
    (g : Y → Z) (f : X → Y) (x : homology T n X) :
    homologyMap T (g ∘ f) x = homologyMap T g (homologyMap T f x) :=
  T.map_comp n g f x

/-- The suspension shift isomorphism supplied by the homology theory contract. -/
abbrev suspensionShift (n : ℤ) (X : Type u) :
    homology T (n + 1) (T.suspension X) ≃ homology T n X :=
  T.susp_iso n X

theorem suspensionShift_natural (n : ℤ) {X Y : Type u} (f : X → Y)
    (x : homology T (n + 1) (T.suspension X)) :
    suspensionShift (T := T) n Y (homologyMap T (T.suspensionMap f) x) =
      homologyMap T f (suspensionShift (T := T) n X x) :=
  T.susp_natural n f x

end HomologyTheory

end InfoGeometry.Spectral.Homology.Basic
