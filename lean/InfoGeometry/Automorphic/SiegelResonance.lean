/-
InfoGeometry/Automorphic/SiegelResonance.lean

Abstract split exact sequence for Siegel boundary extraction.

This module formalizes automorphic boundary surgery. It defines the
P-cuspidal resonance projector

    ℜ_P = I - ℰ_P ∘ 𝔖_P

where 𝔖_P is the Siegel constant-term operator and ℰ_P is a chosen Eisenstein
lift/section.

This is the automorphic analogue of Drazin-style core/boundary splitting.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range

noncomputable section

namespace SiegelResonance

universe uBulk uBoundary uParabolic

/-! ### 1. The Siegel-Eisenstein split exact sequence -/

/--
Witness for a split Siegel-Eisenstein boundary sequence.

`siegel` is the Siegel constant-term operator `𝔖_P`.

`eisenstein` is a chosen Eisenstein lift/section `ℰ_P`.

The section axiom says:

`𝔖_P ∘ ℰ_P = id`.

Thus `siegel` is surjective and `eisenstein` is injective.
-/
structure SiegelEisensteinWitness
    (Bulk : Type uBulk) (Boundary : Type uBoundary)
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary] where
  siegel : Bulk →ₗ[ℝ] Boundary
  eisenstein : Boundary →ₗ[ℝ] Bulk

  /-- The Eisenstein lift is a strict right-inverse to the Siegel operator. -/
  section_axiom :
    siegel.comp eisenstein = LinearMap.id

namespace SiegelEisensteinWitness

variable {Bulk : Type uBulk} {Boundary : Type uBoundary}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]
variable (W : SiegelEisensteinWitness Bulk Boundary)

/-! ### 2. Basic section consequences -/

/-- Pointwise form of the section axiom. -/
@[simp]
theorem section_apply (b : Boundary) :
    W.siegel (W.eisenstein b) = b := by
  have h :=
    congrArg
      (fun f : Boundary →ₗ[ℝ] Boundary => f b)
      W.section_axiom
  simpa [LinearMap.comp_apply] using h

/-- The Siegel operator is surjective. -/
theorem siegel_surjective :
    Function.Surjective W.siegel := by
  intro b
  exact ⟨W.eisenstein b, by simp⟩

/-- The Eisenstein section is injective. -/
theorem eisenstein_injective :
    Function.Injective W.eisenstein := by
  intro b₁ b₂ h
  have h' : W.siegel (W.eisenstein b₁) =
      W.siegel (W.eisenstein b₂) := by
    rw [h]
  simpa using h'

/-! ### 3. The automorphic projectors -/

/--
The boundary/Eisenstein projector:

`Π_bdry = ℰ_P ∘ 𝔖_P`.

This isolates the continuous scattering/radiation boundary component.
-/
def boundaryProjector : Bulk →ₗ[ℝ] Bulk :=
  W.eisenstein.comp W.siegel

/--
The cuspidal resonance projector:

`ℜ_P = I - ℰ_P ∘ 𝔖_P`.

This isolates the internal resonance component killed by the Siegel operator.
-/
def cuspidalProjector : Bulk →ₗ[ℝ] Bulk :=
  LinearMap.id - W.boundaryProjector

@[simp]
theorem boundaryProjector_apply (F : Bulk) :
    W.boundaryProjector F = W.eisenstein (W.siegel F) := by
  rfl

@[simp]
theorem cuspidalProjector_apply (F : Bulk) :
    W.cuspidalProjector F = F - W.eisenstein (W.siegel F) := by
  simp [cuspidalProjector, boundaryProjector]

/-! ### 4. Projector identities -/

/-- The boundary/Eisenstein projector is idempotent. -/
theorem boundaryProjector_idempotent :
    W.boundaryProjector * W.boundaryProjector = W.boundaryProjector := by
  apply LinearMap.ext
  intro F
  simp [boundaryProjector]

/-- Composition-form idempotence of the boundary projector. -/
theorem boundaryProjector_comp_boundaryProjector :
    W.boundaryProjector.comp W.boundaryProjector = W.boundaryProjector := by
  apply LinearMap.ext
  intro F
  simp [boundaryProjector]

/-- The cuspidal resonance projector is idempotent. -/
theorem cuspidalProjector_idempotent :
    W.cuspidalProjector * W.cuspidalProjector = W.cuspidalProjector := by
  apply LinearMap.ext
  intro F
  simp [cuspidalProjector, boundaryProjector]

/--
The boundary and cuspidal projectors are disjoint on the left:

`Π_bdry ∘ ℜ_P = 0`.
-/
theorem boundaryProjector_mul_cuspidalProjector :
    W.boundaryProjector * W.cuspidalProjector = 0 := by
  apply LinearMap.ext
  intro F
  simp [cuspidalProjector, boundaryProjector]

/--
The boundary and cuspidal projectors are disjoint on the right:

`ℜ_P ∘ Π_bdry = 0`.
-/
theorem cuspidalProjector_mul_boundaryProjector :
    W.cuspidalProjector * W.boundaryProjector = 0 := by
  apply LinearMap.ext
  intro F
  simp [cuspidalProjector, boundaryProjector]

/--
The two projectors sum to the identity:

`Π_bdry + ℜ_P = I`.
-/
theorem projector_sum :
    W.boundaryProjector + W.cuspidalProjector = LinearMap.id := by
  apply LinearMap.ext
  intro F
  simp [cuspidalProjector, boundaryProjector]

/-! ### 5. Siegel annihilation and exactness -/

/--
The Siegel operator is unchanged after applying the boundary projector:

`𝔖_P ∘ Π_bdry = 𝔖_P`.
-/
theorem siegel_comp_boundaryProjector :
    W.siegel.comp W.boundaryProjector = W.siegel := by
  apply LinearMap.ext
  intro F
  simp [boundaryProjector]

/--
The fundamental resonance theorem:

The Siegel boundary operator annihilates the cuspidal resonance core.

`𝔖_P ∘ ℜ_P = 0`.
-/
theorem siegel_annihilates_cuspidal_core :
    W.siegel.comp W.cuspidalProjector = 0 := by
  apply LinearMap.ext
  intro F
  simp [cuspidalProjector, boundaryProjector]

/-- Pointwise form of Siegel annihilation. -/
theorem siegel_cuspidalProjector_apply (F : Bulk) :
    W.siegel (W.cuspidalProjector F) = 0 := by
  simp [cuspidalProjector, boundaryProjector]

/--
The `P`-cuspidal subspace attached to the Siegel operator.
-/
def pCuspidalSubspace : Submodule ℝ Bulk :=
  LinearMap.ker W.siegel

/--
The cuspidal projector lands in the kernel of the Siegel operator.
-/
theorem cuspidalProjector_mem_ker (F : Bulk) :
    W.cuspidalProjector F ∈ LinearMap.ker W.siegel := by
  rw [LinearMap.mem_ker]
  exact W.siegel_cuspidalProjector_apply F

/--
The range of the cuspidal projector is exactly the kernel of the Siegel
operator.

This is the exactness statement:

`range ℜ_P = ker 𝔖_P`.
-/
theorem range_cuspidalProjector_eq_ker_siegel :
    LinearMap.range W.cuspidalProjector = LinearMap.ker W.siegel := by
  apply le_antisymm
  · intro F hF
    rcases LinearMap.mem_range.mp hF with ⟨G, hG⟩
    rw [← hG]
    exact W.cuspidalProjector_mem_ker G
  · intro F hF
    have hF_zero : W.siegel F = 0 := by
      simpa using (LinearMap.mem_ker.mp hF)
    refine LinearMap.mem_range.mpr ⟨F, ?_⟩
    simp [cuspidalProjector, boundaryProjector, hF_zero]

/--
The range of the boundary projector is exactly the range of the Eisenstein
section.
-/
theorem range_boundaryProjector_eq_range_eisenstein :
    LinearMap.range W.boundaryProjector = LinearMap.range W.eisenstein := by
  apply le_antisymm
  · intro F hF
    rcases LinearMap.mem_range.mp hF with ⟨G, hG⟩
    rw [← hG]
    exact LinearMap.mem_range.mpr ⟨W.siegel G, rfl⟩
  · intro F hF
    rcases LinearMap.mem_range.mp hF with ⟨b, hb⟩
    rw [← hb]
    refine LinearMap.mem_range.mpr ⟨W.eisenstein b, ?_⟩
    simp [boundaryProjector]

/--
The kernel of the boundary projector is exactly the kernel of the Siegel
operator.

This says that the boundary projector kills precisely the `P`-cuspidal states.
-/
theorem ker_boundaryProjector_eq_ker_siegel :
    LinearMap.ker W.boundaryProjector = LinearMap.ker W.siegel := by
  apply le_antisymm
  · intro F hF
    rw [LinearMap.mem_ker] at hF ⊢
    have h := congrArg W.siegel hF
    simpa [boundaryProjector] using h
  · intro F hF
    rw [LinearMap.mem_ker] at hF ⊢
    simp [boundaryProjector, hF]

/--
The kernel of the cuspidal projector is exactly the Eisenstein boundary range.
-/
theorem ker_cuspidalProjector_eq_range_eisenstein :
    LinearMap.ker W.cuspidalProjector = LinearMap.range W.eisenstein := by
  apply le_antisymm
  · intro F hF
    rw [LinearMap.mem_ker] at hF
    refine LinearMap.mem_range.mpr ⟨W.siegel F, ?_⟩
    have h : F - W.eisenstein (W.siegel F) = 0 := by
      simpa [cuspidalProjector, boundaryProjector] using hF
    exact (sub_eq_zero.mp h).symm
  · intro F hF
    rcases LinearMap.mem_range.mp hF with ⟨b, hb⟩
    rw [← hb]
    rw [LinearMap.mem_ker]
    simp [cuspidalProjector, boundaryProjector]

/--
The range of the boundary projector is exactly the kernel of the cuspidal
projector.
-/
theorem range_boundaryProjector_eq_ker_cuspidalProjector :
    LinearMap.range W.boundaryProjector =
      LinearMap.ker W.cuspidalProjector := by
  calc
    LinearMap.range W.boundaryProjector
        = LinearMap.range W.eisenstein :=
          W.range_boundaryProjector_eq_range_eisenstein
    _   = LinearMap.ker W.cuspidalProjector :=
          W.ker_cuspidalProjector_eq_range_eisenstein.symm

/--
The boundary-projector range and cuspidal-projector range intersect trivially.
-/
theorem range_boundaryProjector_inf_range_cuspidalProjector_eq_bot :
    LinearMap.range W.boundaryProjector ⊓
        LinearMap.range W.cuspidalProjector = ⊥ := by
  apply le_antisymm
  · intro F hF
    have hRange : F ∈ LinearMap.range W.eisenstein := by
      rw [← W.range_boundaryProjector_eq_range_eisenstein]
      exact hF.1
    have hKer : F ∈ LinearMap.ker W.siegel := by
      rcases LinearMap.mem_range.mp hF.2 with ⟨G, hG⟩
      rw [← hG]
      exact W.cuspidalProjector_mem_ker G
    rcases LinearMap.mem_range.mp hRange with ⟨b, hb⟩
    have hS : W.siegel F = 0 := LinearMap.mem_ker.mp hKer
    rw [← hb] at hS ⊢
    have hb0 : b = 0 := by
      simpa using hS
    simp [hb0]
  · exact bot_le

/--
A bulk state is fixed by the cuspidal projector iff it is killed by the Siegel
operator.
-/
theorem fixed_by_cuspidalProjector_iff_siegel_zero (F : Bulk) :
    W.cuspidalProjector F = F ↔ W.siegel F = 0 := by
  constructor
  · intro h
    have h0 : W.siegel (W.cuspidalProjector F) = 0 :=
      W.siegel_cuspidalProjector_apply F
    rwa [h] at h0
  · intro h
    simp [cuspidalProjector, boundaryProjector, h]

/--
A boundary lift is fixed by the boundary projector.
-/
theorem boundaryProjector_eisenstein (b : Boundary) :
    W.boundaryProjector (W.eisenstein b) = W.eisenstein b := by
  simp [boundaryProjector]

/--
A boundary lift has no cuspidal component.
-/
theorem cuspidalProjector_eisenstein (b : Boundary) :
    W.cuspidalProjector (W.eisenstein b) = 0 := by
  simp [cuspidalProjector, boundaryProjector]

/--
Every bulk state decomposes as boundary radiation plus cuspidal resonance.
-/
theorem bulk_decomposition (F : Bulk) :
    W.boundaryProjector F + W.cuspidalProjector F = F := by
  simp [cuspidalProjector, boundaryProjector]

/--
Equivalent linear-map form of the bulk decomposition.
-/
theorem boundary_add_cuspidal_eq_id :
    W.boundaryProjector + W.cuspidalProjector = LinearMap.id :=
  W.projector_sum

/--
The Eisenstein boundary subspace and the cuspidal kernel are disjoint.

This is the directness part of the split exact sequence.
-/
theorem range_eisenstein_inf_ker_siegel_eq_bot :
    LinearMap.range W.eisenstein ⊓ LinearMap.ker W.siegel = ⊥ := by
  apply le_antisymm
  · intro F hF
    rcases LinearMap.mem_range.mp hF.1 with ⟨b, hb⟩
    have hS : W.siegel F = 0 := LinearMap.mem_ker.mp hF.2
    rw [← hb] at hS ⊢
    have hb0 : b = 0 := by
      simpa using hS
    simp [hb0]
  · exact bot_le

/--
The Eisenstein boundary subspace and the cuspidal kernel span the full bulk
space.

This is the splitting part of the split exact sequence.
-/
theorem range_eisenstein_sup_ker_siegel_eq_top :
    LinearMap.range W.eisenstein ⊔ LinearMap.ker W.siegel = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro F _
    have hB :
        W.boundaryProjector F ∈ LinearMap.range W.eisenstein := by
      exact LinearMap.mem_range.mpr ⟨W.siegel F, rfl⟩
    have hC :
        W.cuspidalProjector F ∈ LinearMap.ker W.siegel :=
      W.cuspidalProjector_mem_ker F
    have hsum :
        W.boundaryProjector F + W.cuspidalProjector F = F :=
      W.bulk_decomposition F
    rw [← hsum]
    exact Submodule.add_mem_sup hB hC

end SiegelEisensteinWitness

/-! ### 6. Global cuspidality -/

/--
A state is globally cuspidal if it vanishes under every Siegel operator in the
chosen family of proper parabolic boundary operators.

This is the abstract automorphic definition:

`⋂_P ker 𝔖_P`.
-/
def GlobalCuspidalSubspace
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {ParabolicIndex : Type uParabolic}
    (siegelFamily : ParabolicIndex → Bulk →ₗ[ℝ] Boundary) :
    Submodule ℝ Bulk :=
  ⨅ P : ParabolicIndex, LinearMap.ker (siegelFamily P)

/--
Membership in the global cuspidal subspace means vanishing under every Siegel
operator in the family.
-/
theorem mem_globalCuspidalSubspace_iff
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {ParabolicIndex : Type uParabolic}
    (siegelFamily : ParabolicIndex → Bulk →ₗ[ℝ] Boundary)
    (F : Bulk) :
    F ∈ GlobalCuspidalSubspace siegelFamily ↔
      ∀ P : ParabolicIndex, siegelFamily P F = 0 := by
  simp [GlobalCuspidalSubspace]

/--
The global cuspidal subspace is contained in each local Siegel kernel.
-/
theorem globalCuspidalSubspace_le_ker
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {ParabolicIndex : Type uParabolic}
    (siegelFamily : ParabolicIndex → Bulk →ₗ[ℝ] Boundary)
    (P : ParabolicIndex) :
    GlobalCuspidalSubspace siegelFamily ≤
      LinearMap.ker (siegelFamily P) := by
  exact iInf_le _ P

end SiegelResonance
