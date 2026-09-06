import Mathlib
import InfoGeometry.Canonical.GradedRationalSectorPreservation
import InfoGeometry.Canonical.GradedRationalChainMap

namespace InfoGeometry.Canonical

/-!
  Topological lift of the existing degree-aware rational differential.
  The algebraic differential remains the owner of `d² = 0`; this file only
  supplies the native finite-dimensional topological readout.
-/

variable {V : ℕ → Type*}
  [∀ p, NormedAddCommGroup (V p)]
  [∀ p, NormedSpace ℚ (V p)]
  [∀ p, FiniteDimensional ℚ (V p)]

def continuousGradedDifferential
    (D : GradedRationalDifferential V) (p : ℕ) :
    V p →ₗ[ℚ] V (p + 1) :=
  D.d p

@[simp] theorem continuousGradedDifferential_apply
    (D : GradedRationalDifferential V) (p : ℕ) (x : V p) :
    continuousGradedDifferential D p x = D.d p x :=
  rfl

theorem continuousGradedDifferential_sq_zero
    (D : GradedRationalDifferential V) (p : ℕ) (x : V p) :
    continuousGradedDifferential D (p + 1)
        (continuousGradedDifferential D p x) = 0 := by
  simpa using D.d_sq_zero p x

theorem continuousGradedDifferential_preserves_sector
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) {x : V p} (hx : x ∈ S p) :
    continuousGradedDifferential D p x ∈ S (p + 1) := by
  simpa using hS p x hx

structure TopologicalGradedRationalChainMap
    {W : ℕ → Type*}
    [∀ p, NormedAddCommGroup (W p)]
    [∀ p, NormedSpace ℚ (W p)]
    [∀ p, FiniteDimensional ℚ (W p)]
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W) where
  algebraic : GradedRationalChainMap D E

def continuousChainMap
    {W : ℕ → Type*}
    [∀ p, NormedAddCommGroup (W p)]
    [∀ p, NormedSpace ℚ (W p)]
    [∀ p, FiniteDimensional ℚ (W p)]
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    (F : TopologicalGradedRationalChainMap D E) (p : ℕ) :
    V p →ₗ[ℚ] W p :=
  F.algebraic.map p

@[simp] theorem continuousChainMap_apply
    {W : ℕ → Type*}
    [∀ p, NormedAddCommGroup (W p)]
    [∀ p, NormedSpace ℚ (W p)]
    [∀ p, FiniteDimensional ℚ (W p)]
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    (F : TopologicalGradedRationalChainMap D E)
    (p : ℕ) (x : V p) :
    continuousChainMap F p x = F.algebraic.map p x :=
  rfl

theorem continuousChainMap_intertwines
    {W : ℕ → Type*}
    [∀ p, NormedAddCommGroup (W p)]
    [∀ p, NormedSpace ℚ (W p)]
    [∀ p, FiniteDimensional ℚ (W p)]
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    (F : TopologicalGradedRationalChainMap D E)
    (p : ℕ) (x : V p) :
    continuousChainMap F (p + 1)
        (continuousGradedDifferential D p x) =
      continuousGradedDifferential E p
        (continuousChainMap F p x) := by
  simpa using F.algebraic.commutes p x

end InfoGeometry.Canonical
