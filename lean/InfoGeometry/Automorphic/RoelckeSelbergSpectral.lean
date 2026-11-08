/-
InfoGeometry/Automorphic/RoelckeSelbergSpectral.lean

Abstract Roelcke-Selberg spectral interface.

This module sits after `SiegelResonance.lean`.

It does not attempt to prove the analytic spectral theorem from pure linear
algebra. Instead, it packages the Laplacian, Hecke operators, commutation
relations, and the spectral-decomposition theorem as proof-carrying data.

The algebraic consequences are proved here:

* commuting with the cuspidal projector preserves the cuspidal subspace;
* cuspidal Laplace eigenspaces are defined;
* joint Laplace-Hecke eigenspaces are defined;
* automorphic L-functions are attached to joint cuspidal eigenpackets.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Automorphic.SiegelResonance

noncomputable section

namespace InfoGeometry.Automorphic.RoelckeSelbergSpectral

open SiegelResonance

universe uBulk uBoundary uHecke

variable {Bulk : Type uBulk} {Boundary : Type uBoundary}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]

/-! ## 1. Linear commutation and eigenspaces -/

/--
Commutation of two linear endomorphisms.
-/
def CommuteLinear
    (S T : Bulk →ₗ[ℝ] Bulk) : Prop :=
  S.comp T = T.comp S

/--
Shifted operator `T - μ I`.
-/
def shiftedOperator
    (T : Bulk →ₗ[ℝ] Bulk)
    (mu : ℝ) :
    Bulk →ₗ[ℝ] Bulk :=
  T - mu • (LinearMap.id : Bulk →ₗ[ℝ] Bulk)

/--
Eigenspace of a linear operator.
-/
def eigenspace
    (T : Bulk →ₗ[ℝ] Bulk)
    (mu : ℝ) :
    Submodule ℝ Bulk :=
  LinearMap.ker (shiftedOperator T mu)

@[simp]
theorem mem_eigenspace_iff
    (T : Bulk →ₗ[ℝ] Bulk)
    (mu : ℝ)
    (F : Bulk) :
    F ∈ eigenspace T mu ↔ T F = mu • F := by
  constructor
  · intro h
    have hker : F ∈ LinearMap.ker (shiftedOperator T mu) := by
      simpa [eigenspace] using h
    have h0 : (shiftedOperator T mu) F = 0 :=
      LinearMap.mem_ker.mp hker
    have hsub : T F - mu • F = 0 := by
      simpa [shiftedOperator] using h0
    exact sub_eq_zero.mp hsub
  · intro h
    have hker : F ∈ LinearMap.ker (shiftedOperator T mu) :=
      LinearMap.mem_ker.mpr (by
        simp [shiftedOperator, h])
    simpa [eigenspace] using hker

/-! ## 2. Cuspidal eigenspaces -/

/--
Cuspidal eigenspace of an operator relative to a Siegel-Eisenstein splitting.
-/
def cuspidalEigenspace
    (W : SiegelEisensteinWitness Bulk Boundary)
    (T : Bulk →ₗ[ℝ] Bulk)
    (mu : ℝ) :
    Submodule ℝ Bulk :=
  W.pCuspidalSubspace ⊓ eigenspace T mu

@[simp]
theorem mem_cuspidalEigenspace_iff
    (W : SiegelEisensteinWitness Bulk Boundary)
    (T : Bulk →ₗ[ℝ] Bulk)
    (mu : ℝ)
    (F : Bulk) :
    F ∈ cuspidalEigenspace W T mu ↔
      W.siegel F = 0 ∧ T F = mu • F := by
  simp [
    cuspidalEigenspace,
    SiegelEisensteinWitness.pCuspidalSubspace
  ]

/--
If a linear map commutes with the cuspidal projector, then it preserves the
cuspidal subspace.
-/
theorem map_mem_pCuspidal_of_commutes
    (W : SiegelEisensteinWitness Bulk Boundary)
    (T : Bulk →ₗ[ℝ] Bulk)
    (hcomm : CommuteLinear W.cuspidalProjector T)
    {F : Bulk}
    (hF : F ∈ W.pCuspidalSubspace) :
    T F ∈ W.pCuspidalSubspace := by
  have hFker : F ∈ LinearMap.ker W.siegel := by
    simpa [SiegelEisensteinWitness.pCuspidalSubspace] using hF
  have hFzero : W.siegel F = 0 :=
    LinearMap.mem_ker.mp hFker

  have hfixed : W.cuspidalProjector F = F :=
    (W.fixed_by_cuspidalProjector_iff_siegel_zero F).2 hFzero

  have hcommF :
      W.cuspidalProjector (T F) =
        T (W.cuspidalProjector F) := by
    simpa [CommuteLinear, LinearMap.comp_apply] using
      congrArg (fun L : Bulk →ₗ[ℝ] Bulk => L F) hcomm

  have hfixedTF : W.cuspidalProjector (T F) = T F := by
    simpa [hfixed] using hcommF

  have hzero : W.siegel (T F) = 0 :=
    (W.fixed_by_cuspidalProjector_iff_siegel_zero (T F)).1 hfixedTF

  have hker : T F ∈ LinearMap.ker W.siegel :=
    LinearMap.mem_ker.mpr hzero

  simpa [SiegelEisensteinWitness.pCuspidalSubspace] using hker

/-! ## 3. Roelcke-Selberg spectral datum -/

/--
Simultaneous nonzero cuspidal eigenvectors of a Laplacian and a commuting Hecke
family.  The eigenvalues are part of the existential spectral character.
-/
def simultaneousCuspidalEigenvectors
    (W : SiegelEisensteinWitness Bulk Boundary)
    (laplacian : Bulk →ₗ[ℝ] Bulk)
    {HeckeIndex : Type uHecke}
    (hecke : HeckeIndex → Bulk →ₗ[ℝ] Bulk) :
    Set Bulk :=
  {F |
    F ∈ W.pCuspidalSubspace ∧
      F ≠ 0 ∧
        ∃ laplaceEigenvalue : ℝ,
          ∃ heckeEigenvalue : HeckeIndex → ℝ,
            laplacian F = laplaceEigenvalue • F ∧
              ∀ i : HeckeIndex, hecke i F = heckeEigenvalue i • F}

/--
Abstract Roelcke-Selberg spectral datum.

This packages the analytic theorem rather than pretending to derive it from
the split exact sequence alone.

`laplacian` is the automorphic Laplacian.

`hecke` is a family of Hecke operators.

The commutation fields ensure that all spectral operators preserve the
cuspidal resonance subspace.
-/
structure RoelckeSelbergSpectralDatum
    (W : SiegelEisensteinWitness Bulk Boundary)
    (HeckeIndex : Type uHecke) where
  /-- Automorphic Laplacian. -/
  laplacian : Bulk →ₗ[ℝ] Bulk

  /-- The Laplacian preserves the cuspidal splitting. -/
  laplacian_commutes_cuspidal :
    CommuteLinear W.cuspidalProjector laplacian

  /-- Hecke operators. -/
  hecke : HeckeIndex → Bulk →ₗ[ℝ] Bulk

  /-- Hecke operators commute with each other. -/
  hecke_pairwise_commute :
    ∀ i j : HeckeIndex,
      CommuteLinear (hecke i) (hecke j)

  /-- Hecke operators commute with the Laplacian. -/
  hecke_commutes_laplacian :
    ∀ i : HeckeIndex,
      CommuteLinear (hecke i) laplacian

  /-- Hecke operators preserve the cuspidal splitting. -/
  hecke_commutes_cuspidal :
    ∀ i : HeckeIndex,
      CommuteLinear W.cuspidalProjector (hecke i)

  /--
  Roelcke-Selberg completeness: simultaneous nonzero Laplace-Hecke
  eigenvectors span the cuspidal subspace.
  -/
  roelckeSelberg :
    Submodule.span ℝ
        (simultaneousCuspidalEigenvectors W laplacian hecke) =
      W.pCuspidalSubspace

namespace RoelckeSelbergSpectralDatum

variable {W : SiegelEisensteinWitness Bulk Boundary}
variable {HeckeIndex : Type uHecke}
variable (R : RoelckeSelbergSpectralDatum W HeckeIndex)

/-- Historical statement name, now derived from the explicit span equality. -/
def roelckeSelbergStatement : Prop :=
  Submodule.span ℝ
      (simultaneousCuspidalEigenvectors W R.laplacian R.hecke) =
    W.pCuspidalSubspace

/-- The explicit Roelcke-Selberg completeness law carried by the datum. -/
theorem roelckeSelberg_holds :
    R.roelckeSelbergStatement :=
  R.roelckeSelberg

/--
The Laplacian preserves the cuspidal subspace.
-/
theorem laplacian_mem_pCuspidal
    {F : Bulk}
    (hF : F ∈ W.pCuspidalSubspace) :
    R.laplacian F ∈ W.pCuspidalSubspace :=
  map_mem_pCuspidal_of_commutes
    W R.laplacian R.laplacian_commutes_cuspidal hF

/--
Every Hecke operator preserves the cuspidal subspace.
-/
theorem hecke_mem_pCuspidal
    (i : HeckeIndex)
    {F : Bulk}
    (hF : F ∈ W.pCuspidalSubspace) :
    R.hecke i F ∈ W.pCuspidalSubspace :=
  map_mem_pCuspidal_of_commutes
    W (R.hecke i) (R.hecke_commutes_cuspidal i) hF

end RoelckeSelbergSpectralDatum

/-! ## 4. Joint Laplace-Hecke eigenspaces -/

/--
A joint spectral character: one Laplace eigenvalue and one Hecke eigenvalue
for every Hecke operator.
-/
structure JointEigenvalue
    (HeckeIndex : Type uHecke) where
  laplace : ℝ
  hecke : HeckeIndex → ℝ

/--
The joint cuspidal Laplace-Hecke eigenspace.
-/
def jointEigenspace
    {W : SiegelEisensteinWitness Bulk Boundary}
    {HeckeIndex : Type uHecke}
    (R : RoelckeSelbergSpectralDatum W HeckeIndex)
    (chi : JointEigenvalue HeckeIndex) :
    Submodule ℝ Bulk :=
  cuspidalEigenspace W R.laplacian chi.laplace ⊓
    ⨅ i : HeckeIndex, eigenspace (R.hecke i) (chi.hecke i)

@[simp]
theorem mem_jointEigenspace_iff
    {W : SiegelEisensteinWitness Bulk Boundary}
    {HeckeIndex : Type uHecke}
    (R : RoelckeSelbergSpectralDatum W HeckeIndex)
    (chi : JointEigenvalue HeckeIndex)
    (F : Bulk) :
    F ∈ jointEigenspace R chi ↔
      (W.siegel F = 0 ∧ R.laplacian F = chi.laplace • F) ∧
        ∀ i : HeckeIndex, R.hecke i F = chi.hecke i • F := by
  simp [
    jointEigenspace,
    cuspidalEigenspace,
    SiegelEisensteinWitness.pCuspidalSubspace
  ]

/--
A nonzero joint cuspidal eigenpacket.
-/
structure CuspidalEigenpacket
    {W : SiegelEisensteinWitness Bulk Boundary}
    {HeckeIndex : Type uHecke}
    (R : RoelckeSelbergSpectralDatum W HeckeIndex)
    (chi : JointEigenvalue HeckeIndex) where
  /-- The underlying automorphic state. -/
  vector : Bulk

  /-- Nonzero eigenstate condition. -/
  nonzero : vector ≠ 0

  /-- Joint cuspidal eigencondition. -/
  mem_joint :
    vector ∈ jointEigenspace R chi

namespace CuspidalEigenpacket

variable {W : SiegelEisensteinWitness Bulk Boundary}
variable {HeckeIndex : Type uHecke}
variable {R : RoelckeSelbergSpectralDatum W HeckeIndex}
variable {chi : JointEigenvalue HeckeIndex}

/--
A cuspidal eigenpacket is killed by the Siegel operator.
-/
theorem siegel_zero
    (P : CuspidalEigenpacket R chi) :
    W.siegel P.vector = 0 := by
  have h := (mem_jointEigenspace_iff R chi P.vector).1 P.mem_joint
  exact h.1.1

/--
A cuspidal eigenpacket is a Laplace eigenvector.
-/
theorem laplacian_eigen
    (P : CuspidalEigenpacket R chi) :
    R.laplacian P.vector = chi.laplace • P.vector := by
  have h := (mem_jointEigenspace_iff R chi P.vector).1 P.mem_joint
  exact h.1.2

/--
A cuspidal eigenpacket is a Hecke eigenvector for every Hecke operator.
-/
theorem hecke_eigen
    (P : CuspidalEigenpacket R chi)
    (i : HeckeIndex) :
    R.hecke i P.vector = chi.hecke i • P.vector := by
  have h := (mem_jointEigenspace_iff R chi P.vector).1 P.mem_joint
  exact h.2 i

end CuspidalEigenpacket

/-! ## 5. Automorphic L-function datum -/

/--
Abstract automorphic L-function datum attached to joint cuspidal eigenvalues.

This is the correct interface layer. It can later be instantiated by standard,
completed, Rankin-Selberg, spin, standard representation, or Langlands-dual
L-functions.
-/
structure AutomorphicLFunctionDatum
    (HeckeIndex : Type uHecke) where
  /-- The L-function value attached to a joint eigenvalue. -/
  value :
    JointEigenvalue HeckeIndex → ℂ → ℂ

  /-- Local Euler factor attached to each Hecke place/index. -/
  localFactor :
    HeckeIndex → JointEigenvalue HeckeIndex → ℂ → ℂ

  /-- Region where the logarithmic potential is ordinary real-valued. -/
  regular :
    JointEigenvalue HeckeIndex → ℂ → Prop

  /-- Nonvanishing on the regular region. -/
  value_nonzero :
    ∀ chi s, regular chi s → value chi s ≠ 0

  /-- Region on which the selected local-factor realization is valid. -/
  convergenceRegion :
    JointEigenvalue HeckeIndex → Set ℂ

  /--
  Explicit finite local-factor realization on the declared convergence
  region. Stronger analytic models may refine this with a convergent infinite
  product theorem.
  -/
  eulerProduct :
    ∀ chi s, s ∈ convergenceRegion chi →
      ∃ finitePlaces : Finset HeckeIndex,
        value chi s =
          ∏ i ∈ finitePlaces, localFactor i chi s

namespace AutomorphicLFunctionDatum

variable {HeckeIndex : Type uHecke}
variable (L : AutomorphicLFunctionDatum HeckeIndex)

/-- Historical statement name, now the explicit local-factor law. -/
def eulerProductStatement : Prop :=
  ∀ chi s, s ∈ L.convergenceRegion chi →
    ∃ finitePlaces : Finset HeckeIndex,
      L.value chi s =
        ∏ i ∈ finitePlaces, L.localFactor i chi s

/-- Readback of the concrete Euler-product realization. -/
theorem eulerProduct_holds :
    L.eulerProductStatement :=
  L.eulerProduct

/--
Prime-surprisal / L-potential attached to a joint eigenvalue:

`Φ_L(χ,s) = -log |L(χ,s)|`.
-/
def potential
    (chi : JointEigenvalue HeckeIndex)
    (s : ℂ) : ℝ :=
  - Real.log ‖L.value chi s‖

@[simp]
theorem potential_eq_zero_of_abs_eq_one
    {chi : JointEigenvalue HeckeIndex}
    {s : ℂ}
    (h : ‖L.value chi s‖ = 1) :
    potential L chi s = 0 := by
  simp [potential, h]

/--
Evaluate the automorphic L-function on a cuspidal eigenpacket.

The value depends on the spectral character `chi`; the packet supplies the
proof that this character is realized by an actual nonzero cuspidal state.
-/
def valueOnPacket
    {W : SiegelEisensteinWitness Bulk Boundary}
    {R : RoelckeSelbergSpectralDatum W HeckeIndex}
    {chi : JointEigenvalue HeckeIndex}
    (_P : CuspidalEigenpacket R chi)
    (s : ℂ) : ℂ :=
  L.value chi s

/--
L-potential evaluated on a cuspidal eigenpacket.
-/
def potentialOnPacket
    {W : SiegelEisensteinWitness Bulk Boundary}
    {R : RoelckeSelbergSpectralDatum W HeckeIndex}
    {chi : JointEigenvalue HeckeIndex}
    (_P : CuspidalEigenpacket R chi)
    (s : ℂ) : ℝ :=
  L.potential chi s

end AutomorphicLFunctionDatum

/-! ## 6. Owner targets -/

/--
Owner target for a Roelcke-Selberg spectral datum over a given
Siegel-Eisenstein split.
-/
def RoelckeSelbergSpectralOwnerTarget
    (W : SiegelEisensteinWitness Bulk Boundary)
    (HeckeIndex : Type uHecke) : Type _ :=
  RoelckeSelbergSpectralDatum W HeckeIndex

/--
Owner target for an automorphic L-function datum on the Hecke spectrum.
-/
def AutomorphicLFunctionOwnerTarget
    (HeckeIndex : Type uHecke) : Type _ :=
  AutomorphicLFunctionDatum HeckeIndex

end InfoGeometry.Automorphic.RoelckeSelbergSpectral
