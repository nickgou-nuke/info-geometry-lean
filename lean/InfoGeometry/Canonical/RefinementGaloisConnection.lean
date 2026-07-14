import InfoGeometry.Canonical.CantorCylinderLattice
import InfoGeometry.Canonical.SectorLattice
import Mathlib.Order.GaloisConnection.Basic

/-!
# Refinement Galois Connection

This file implements the refinement/coarse-graining Galois connection between
sector lattices at consecutive levels $n$ and $n+1$.

Refinement maps a parent sector to the join of its children:
  $e_{n,w} \mapsto e_{n+1,w0} \vee e_{n+1,w1}$
This corresponds to taking the preimage of the truncation map.
It is a join-preserving map, making it the lower adjoint.

Coarse-graining maps a fine sector to its parent if and only if both children
are present (universal quantification / right adjoint):
  $T \mapsto \{ w \mid \forall v, \text{truncateWord}(v) = w \implies v \in T \}$
It is a meet-preserving map, making it the upper adjoint.

The adjunction is: `refine a ≤ b ↔ a ≤ coarse b`.
-/

namespace RefinementGaloisConnection

open InfoGeometry.Canonical.CantorCylinderLattice
open InfoGeometry.Canonical.SectorLattice

/-! ## 1. Spatial Refinement and Coarse-Graining -/

/-- Refines a level `n` spatial set to a level `n+1` spatial set.

This is the preimage of `truncateWord`. -/
def refineSpatial {n : ℕ} (S : Set (BinaryWord n)) : Set (BinaryWord (n + 1)) :=
  truncateWord ⁻¹' S

/-- Coarse-grains a level `n+1` spatial set to a level `n` spatial set.

This is the right adjoint to `refineSpatial`. A word `w` is in the coarse-grained
set if both its children `w0` and `w1` are in `T`. -/
def coarseSpatial {n : ℕ} (T : Set (BinaryWord (n + 1))) : Set (BinaryWord n) :=
  {w | ∀ v, truncateWord v = w → v ∈ T}

/-- The fundamental spatial Galois connection: `refineSpatial ⊣ coarseSpatial`. -/
theorem spatial_galois_connection (n : ℕ) :
    GaloisConnection (@refineSpatial n) (@coarseSpatial n) := by
  intro S T
  show (truncateWord ⁻¹' S ⊆ T) ↔ (S ⊆ {w | ∀ v, truncateWord v = w → v ∈ T})
  constructor
  · intro h w hw v hv
    have : v ∈ truncateWord ⁻¹' S := by
      simp only [Set.mem_preimage]
      rw [hv]
      exact hw
    exact h this
  · intro h v hv
    simp only [Set.mem_preimage] at hv
    exact h hv v rfl

/-! ## 2. Sector Refinement and Coarse-Graining -/

/-- Refines a sector from level `n` to `n+1`, leaving the Krein chirality unchanged. -/
def refineSector {n : ℕ} (s : Sector n) : Sector (n + 1) :=
  (refineSpatial s.1, s.2)

/-- Coarse-grains a sector from level `n+1` to `n`, leaving the Krein chirality unchanged. -/
def coarseSector {n : ℕ} (s : Sector (n + 1)) : Sector n :=
  (coarseSpatial s.1, s.2)

/-- The full sector Galois connection: `refineSector ⊣ coarseSector`. -/
theorem sector_galois_connection (n : ℕ) :
    GaloisConnection (@refineSector n) (@coarseSector n) := by
  intro a b
  show refineSpatial a.1 ⊆ b.1 ∧ a.2 ≤ b.2 ↔ a.1 ⊆ coarseSpatial b.1 ∧ a.2 ≤ b.2
  have h := spatial_galois_connection n a.1 b.1
  tauto

/-! ## 3. Order Properties -/

/-- Refinement preserves arbitrary joins (iSup). -/
theorem refineSector_iSup {n : ℕ} {ι : Type*} (f : ι → Sector n) :
    refineSector (⨆ i, f i) = ⨆ i, refineSector (f i) :=
  (sector_galois_connection n).l_iSup

/-- Coarse-graining preserves arbitrary meets (iInf). -/
theorem coarseSector_iInf {n : ℕ} {ι : Type*} (f : ι → Sector (n + 1)) :
    coarseSector (⨅ i, f i) = ⨅ i, coarseSector (f i) :=
  (sector_galois_connection n).u_iInf

end RefinementGaloisConnection
