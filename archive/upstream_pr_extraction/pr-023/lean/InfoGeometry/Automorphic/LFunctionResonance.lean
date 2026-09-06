/-
InfoGeometry/Automorphic/LFunctionResonance.lean

Automorphic L-function resonance sockets.

This module attaches arithmetic/L-function data to the operator-first
Siegel-Eisenstein splitting.

Principle:

* cuspidal L-functions are evaluated on the cuspidal projector
    ℜ_P F = (I - ℰ_P ∘ 𝔖_P) F;

* boundary/scattering L-functions are evaluated on the Siegel boundary datum
    𝔖_P F.

No Euler product, functional equation, spectral theorem, or zero theorem is
asserted here. Those are future witness layers.
-/

import Mathlib
import InfoGeometry.Automorphic.SiegelResonance
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Automorphic.LFunctionResonance

open InfoGeometry.Automorphic.SiegelResonance

universe uBulk uBoundary uHecke

variable {Bulk : Type uBulk} {Boundary : Type uBoundary}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]

/-! ## 1. Operators compatible with Siegel-Eisenstein splitting -/

/--
A bulk operator together with its induced boundary operator.

This is the operator-first socket for automorphic Laplacians, Hecke operators,
or any other symmetry operator that should respect the Siegel boundary
extraction.
-/
structure AutomorphicOperatorIntertwining
    (W : SiegelEisensteinWitness Bulk Boundary) where
  /-- Operator acting on bulk automorphic states. -/
  bulkOp : Bulk →ₗ[ℝ] Bulk

  /-- Induced operator acting on boundary data. -/
  boundaryOp : Boundary →ₗ[ℝ] Boundary

  /-- The Siegel operator intertwines the bulk and boundary operators. -/
  siegel_intertwines :
    W.siegel.comp bulkOp = boundaryOp.comp W.siegel

  /-- The Eisenstein lift intertwines the boundary and bulk operators. -/
  eisenstein_intertwines :
    bulkOp.comp W.eisenstein = W.eisenstein.comp boundaryOp

namespace AutomorphicOperatorIntertwining

variable {W : SiegelEisensteinWitness Bulk Boundary}
variable (T : AutomorphicOperatorIntertwining W)

/--
The bulk operator commutes with the boundary/Eisenstein projector.
-/
theorem boundaryProjector_commutes :
    T.bulkOp.comp W.boundaryProjector =
      W.boundaryProjector.comp T.bulkOp := by
  apply LinearMap.ext
  intro F
  change
    T.bulkOp (W.eisenstein (W.siegel F)) =
      W.eisenstein (W.siegel (T.bulkOp F))
  calc
    T.bulkOp (W.eisenstein (W.siegel F))
        = W.eisenstein (T.boundaryOp (W.siegel F)) := by
          have h :=
            congrArg
              (fun f : Boundary →ₗ[ℝ] Bulk => f (W.siegel F))
              T.eisenstein_intertwines
          simpa [LinearMap.comp_apply] using h
    _ = W.eisenstein (W.siegel (T.bulkOp F)) := by
          have h :
              W.siegel (T.bulkOp F) =
                T.boundaryOp (W.siegel F) := by
            have h0 :=
              congrArg
                (fun f : Bulk →ₗ[ℝ] Boundary => f F)
                T.siegel_intertwines
            simpa [LinearMap.comp_apply] using h0
          rw [h]

/--
The bulk operator commutes with the cuspidal resonance projector.
-/
theorem cuspidalProjector_commutes :
    T.bulkOp.comp W.cuspidalProjector =
      W.cuspidalProjector.comp T.bulkOp := by
  apply LinearMap.ext
  intro F
  have hB :
      T.bulkOp (W.boundaryProjector F) =
        W.boundaryProjector (T.bulkOp F) := by
    have h :=
      congrArg
        (fun f : Bulk →ₗ[ℝ] Bulk => f F)
        T.boundaryProjector_commutes
    simpa [LinearMap.comp_apply] using h
  calc
    T.bulkOp (W.cuspidalProjector F)
        = T.bulkOp (F - W.boundaryProjector F) := by
          simp [SiegelEisensteinWitness.cuspidalProjector]
    _ = T.bulkOp F - T.bulkOp (W.boundaryProjector F) := by
          simp
    _ = T.bulkOp F - W.boundaryProjector (T.bulkOp F) := by
          rw [hB]
    _ = W.cuspidalProjector (T.bulkOp F) := by
          simp [SiegelEisensteinWitness.cuspidalProjector]

/--
The bulk operator preserves the local cuspidal kernel.
-/
theorem maps_ker_siegel_to_ker_siegel
    {F : Bulk}
    (hF : W.siegel F = 0) :
    W.siegel (T.bulkOp F) = 0 := by
  have h :
      W.siegel (T.bulkOp F) =
        T.boundaryOp (W.siegel F) := by
    have h0 :=
      congrArg
        (fun f : Bulk →ₗ[ℝ] Boundary => f F)
        T.siegel_intertwines
    simpa [LinearMap.comp_apply] using h0
  simpa [hF] using h

end AutomorphicOperatorIntertwining

/-! ## 2. Cuspidal L-functionals -/

/--
A function-valued linear map is cuspidal relative to the
Siegel-Eisenstein splitting when it kills every Eisenstein lift.

This is the projector-algebraic part that this module can prove/use
constructively.  Euler products, analytic continuation, and functional
equations are not asserted here.
-/
def IsCuspidalLanglandsLFunctional
    (W : SiegelEisensteinWitness Bulk Boundary)
    (Lmap : Bulk →ₗ[ℝ] (ℂ → ℂ)) : Prop :=
  ∀ b : Boundary, Lmap (W.eisenstein b) = 0

/--
A cuspidal automorphic L-functional.

The map is function-valued:

`F ↦ L(F, s)`.

The actual L-function attached to a raw bulk state is evaluated only after
applying the cuspidal projector.
-/
structure CuspidalLFunctionDatum
    (W : SiegelEisensteinWitness Bulk Boundary) where
  /-- Function-valued linear map `F ↦ L(F, ·)`. -/
  Lmap : Bulk →ₗ[ℝ] (ℂ → ℂ)

  /-- Placeholder for the concrete Langlands L-functional certificate. -/
  langlands :
    IsCuspidalLanglandsLFunctional W Lmap

/--
The cuspidal L-function attached to a bulk state.

By construction, this reads only the cuspidal core:

`L_cusp(F, s) = L(ℜ_P F, s)`.
-/
def cuspidalLFunction
    (W : SiegelEisensteinWitness Bulk Boundary)
    (L : CuspidalLFunctionDatum W)
    (F : Bulk) : ℂ → ℂ :=
  L.Lmap (W.cuspidalProjector F)

/--
Pointwise value of the cuspidal L-function.
-/
def cuspidalLValue
    (W : SiegelEisensteinWitness Bulk Boundary)
    (L : CuspidalLFunctionDatum W)
    (F : Bulk)
    (s : ℂ) : ℂ :=
  cuspidalLFunction W L F s

namespace CuspidalLFunctionDatum

variable {W : SiegelEisensteinWitness Bulk Boundary}
variable (L : CuspidalLFunctionDatum W)

/-- The supplied cuspidal functional kills Eisenstein lifts. -/
theorem Lmap_eisenstein_eq_zero
    (b : Boundary) :
    L.Lmap (W.eisenstein b) = 0 :=
  L.langlands b

/--
Boundary/Eisenstein states contribute no cuspidal L-function.
-/
theorem cuspidalLFunction_boundaryProjector
    (F : Bulk) :
    cuspidalLFunction W L (W.boundaryProjector F) = 0 := by
  ext s
  simp [cuspidalLFunction,
    SiegelEisensteinWitness.cuspidalProjector,
    SiegelEisensteinWitness.boundaryProjector]

/--
Pure Eisenstein lifts contribute no cuspidal L-function.
-/
theorem cuspidalLFunction_eisenstein
    (b : Boundary) :
    cuspidalLFunction W L (W.eisenstein b) = 0 := by
  ext s
  simp [cuspidalLFunction,
    SiegelEisensteinWitness.cuspidalProjector,
    SiegelEisensteinWitness.boundaryProjector]

/--
If a bulk state is already cuspidal, its projected L-function is the raw
L-functional value.
-/
theorem cuspidalLFunction_of_siegel_zero
    (F : Bulk)
    (hF : W.siegel F = 0) :
    cuspidalLFunction W L F = L.Lmap F := by
  ext s
  simp [cuspidalLFunction,
    SiegelEisensteinWitness.cuspidalProjector,
    SiegelEisensteinWitness.boundaryProjector,
    hF]

/--
Adding a pure Eisenstein lift does not change the cuspidal L-function.
-/
theorem cuspidalLFunction_add_eisenstein
    (F : Bulk)
    (b : Boundary) :
    cuspidalLFunction W L (F + W.eisenstein b) =
      cuspidalLFunction W L F := by
  ext s
  simp [cuspidalLFunction,
    SiegelEisensteinWitness.cuspidalProjector,
    SiegelEisensteinWitness.boundaryProjector]

end CuspidalLFunctionDatum

/-! ## 3. Boundary/scattering L-functionals -/

/--
A boundary function-valued linear map is calibrated to the Siegel boundary
component when it is unchanged after replacing a bulk state by its
Eisenstein-boundary projection before applying the Siegel map.
-/
def IsBoundaryScatteringLFunctional
    (W : SiegelEisensteinWitness Bulk Boundary)
    (Lmap : Boundary →ₗ[ℝ] (ℂ → ℂ)) : Prop :=
  ∀ F : Bulk, Lmap (W.siegel (W.boundaryProjector F)) = Lmap (W.siegel F)

/--
Boundary/scattering L-function datum.

This is the arithmetic object attached to the boundary radiation extracted by
the Siegel operator.
-/
structure BoundaryScatteringLFunctionDatum
    (W : SiegelEisensteinWitness Bulk Boundary) where
  /-- Function-valued linear map on boundary data. -/
  Lmap : Boundary →ₗ[ℝ] (ℂ → ℂ)

  /-- Placeholder scattering certificate. -/
  scattering :
    IsBoundaryScatteringLFunctional W Lmap

/--
The boundary/scattering L-function attached to a bulk state:

`L_bdry(F, s) = L_bdry(𝔖_P F, s)`.
-/
def boundaryScatteringLFunction
    (W : SiegelEisensteinWitness Bulk Boundary)
    (L : BoundaryScatteringLFunctionDatum W)
    (F : Bulk) : ℂ → ℂ :=
  L.Lmap (W.siegel F)

/--
Pointwise value of the boundary/scattering L-function.
-/
def boundaryScatteringLValue
    (W : SiegelEisensteinWitness Bulk Boundary)
    (L : BoundaryScatteringLFunctionDatum W)
    (F : Bulk)
    (s : ℂ) : ℂ :=
  boundaryScatteringLFunction W L F s

namespace BoundaryScatteringLFunctionDatum

variable {W : SiegelEisensteinWitness Bulk Boundary}
variable (L : BoundaryScatteringLFunctionDatum W)

/-- The supplied scattering functional is calibrated to boundary projection. -/
theorem Lmap_siegel_boundaryProjector
    (F : Bulk) :
    L.Lmap (W.siegel (W.boundaryProjector F)) = L.Lmap (W.siegel F) :=
  L.scattering F

/--
The boundary/scattering L-function is unchanged by applying the boundary
projector.
-/
theorem boundaryScatteringLFunction_boundaryProjector
    (F : Bulk) :
    boundaryScatteringLFunction W L (W.boundaryProjector F) =
      boundaryScatteringLFunction W L F := by
  ext s
  simp [boundaryScatteringLFunction,
    SiegelEisensteinWitness.boundaryProjector]

/--
Cuspidal cores have zero boundary/scattering L-function.
-/
theorem boundaryScatteringLFunction_cuspidalProjector
    (F : Bulk) :
    boundaryScatteringLFunction W L (W.cuspidalProjector F) = 0 := by
  ext s
  simp [boundaryScatteringLFunction,
    SiegelEisensteinWitness.cuspidalProjector,
    SiegelEisensteinWitness.boundaryProjector]

/--
For a pure Eisenstein lift, the boundary/scattering L-function is the boundary
L-functional evaluated on the lifted datum.
-/
theorem boundaryScatteringLFunction_eisenstein
    (b : Boundary) :
    boundaryScatteringLFunction W L (W.eisenstein b) =
      L.Lmap b := by
  ext s
  simp [boundaryScatteringLFunction]

end BoundaryScatteringLFunctionDatum

/-! ## 4. Hecke/Laplacian resonance sockets -/

/--
A family of automorphic operators compatible with the Siegel-Eisenstein split.

This is the common socket for Hecke operators, automorphic Laplacians, or other
commuting symmetry operators.
-/
structure CompatibleAutomorphicOperatorFamily
    (W : SiegelEisensteinWitness Bulk Boundary) where
  Index : Type uHecke
  op : Index → AutomorphicOperatorIntertwining W

/--
Simultaneous eigenpacket data on the cuspidal core.

At this abstract operator layer, the constructively provable content is that
every compatible operator preserves the local Siegel kernel.
-/
def HasCuspidalEigenpacket
    {W : SiegelEisensteinWitness Bulk Boundary}
    (Ops : CompatibleAutomorphicOperatorFamily W)
    (F : Bulk) : Prop :=
  ∀ i : Ops.Index, W.siegel ((Ops.op i).bulkOp F) = 0

/-- Compatible automorphic operators preserve cuspidal kernel membership. -/
theorem hasCuspidalEigenpacket_of_siegel_zero
    {W : SiegelEisensteinWitness Bulk Boundary}
    (Ops : CompatibleAutomorphicOperatorFamily W)
    (F : Bulk)
    (hF : W.siegel F = 0) :
    HasCuspidalEigenpacket Ops F := by
  intro i
  exact (Ops.op i).maps_ker_siegel_to_ker_siegel hF

/--
Euler/eigenpacket compatibility available at the projector-algebra layer.

This combines the supplied cuspidal functional law with the theorem that
compatible operators preserve the cuspidal kernel.  It does not assert an
Euler product or analytic continuation.
-/
def HasHeckeEulerCompatibility
    {W : SiegelEisensteinWitness Bulk Boundary}
    (Ops : CompatibleAutomorphicOperatorFamily W)
    (L : CuspidalLFunctionDatum W) : Prop :=
  IsCuspidalLanglandsLFunctional W L.Lmap ∧
    ∀ F : Bulk, W.siegel F = 0 → HasCuspidalEigenpacket Ops F

/--
The Hecke/eigenpacket compatibility at this layer is constructively available
from the cuspidal functional law and operator intertwining.
-/
theorem hasHeckeEulerCompatibility
    {W : SiegelEisensteinWitness Bulk Boundary}
    (Ops : CompatibleAutomorphicOperatorFamily W)
    (L : CuspidalLFunctionDatum W) :
    HasHeckeEulerCompatibility Ops L :=
  ⟨L.langlands,
    fun F hF => hasCuspidalEigenpacket_of_siegel_zero Ops F hF⟩

/-! ## 5. Unified automorphic resonance witness -/

/--
Automorphic resonance package.

This packages the operator-first split together with its two arithmetic
readouts:

* cuspidal/discrete readout through `ℜ_P`;
* boundary/scattering readout through `𝔖_P`.
-/
structure AutomorphicLResonanceWitness
    (W : SiegelEisensteinWitness Bulk Boundary) where
  cuspL :
    CuspidalLFunctionDatum W

  boundaryL :
    BoundaryScatteringLFunctionDatum W

  operators :
    CompatibleAutomorphicOperatorFamily W

  hecke_euler_compatibility :
    HasHeckeEulerCompatibility operators cuspL

/--
Admissibility package for constructing an automorphic L-resonance witness.

This prevents the owner target from asserting that arbitrary split sequences
canonically carry Langlands L-functions.
-/
structure AutomorphicLResonanceAdmissible
    (W : SiegelEisensteinWitness Bulk Boundary) where
  cuspL :
    CuspidalLFunctionDatum W

  boundaryL :
    BoundaryScatteringLFunctionDatum W

  operators :
    CompatibleAutomorphicOperatorFamily W

  hecke_euler_compatibility :
    HasHeckeEulerCompatibility operators cuspL

/--
A resonance witness exists from admissible L-function and operator data.
-/
theorem automorphicLResonanceWitness_nonempty_of_admissible
    {W : SiegelEisensteinWitness Bulk Boundary}
    (h : AutomorphicLResonanceAdmissible.{uBulk, uBoundary, uHecke} W) :
    Nonempty (AutomorphicLResonanceWitness.{uBulk, uBoundary, uHecke} W) :=
  ⟨{
    cuspL := h.cuspL
    boundaryL := h.boundaryL
    operators := h.operators
    hecke_euler_compatibility := h.hecke_euler_compatibility
  }⟩

/--
Conditional owner target for the future theorem that constructs arithmetic
L-resonance data from admissible automorphic operator data.
-/
@[owner_target_tag]
def AutomorphicLResonanceOwnerTarget : Prop :=
  ∀ (Bulk : Type uBulk) [AddCommGroup Bulk] [Module ℝ Bulk],
  ∀ (Boundary : Type uBoundary) [AddCommGroup Boundary] [Module ℝ Boundary],
  ∀ W : SiegelEisensteinWitness Bulk Boundary,
    AutomorphicLResonanceAdmissible.{uBulk, uBoundary, uHecke} W →
      Nonempty (AutomorphicLResonanceWitness.{uBulk, uBoundary, uHecke} W)

end InfoGeometry.Automorphic.LFunctionResonance
