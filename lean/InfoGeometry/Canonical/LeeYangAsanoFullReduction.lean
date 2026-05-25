import Mathlib
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Canonical.LeeYangAsanoNativeCore
import InfoGeometry.Canonical.LeeYangAsanoNondegeneratePrep
import InfoGeometry.Canonical.LeeYangAsanoEndpointNative

/-!
# InfoGeometry.Canonical.LeeYangAsanoFullReduction

Native reduction of full Asano A.1 to the remaining nondegenerate
topological branch.

This file is not a witness packet.

It proves:
  full two-variable Asano contraction
  follows from:
    1. the already-closed `D = 0` branch;
    2. the already-closed determinant-zero branch;
    3. one remaining native theorem:
       `asano_nondegenerate_root_mem_negProductSet`.

After that theorem is proved, this file becomes the full Asano contraction
reduction.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoNativeCore

/--
The remaining nondegenerate topological Asano theorem.

This is the only open native target for Asano A.1 after the algebraic
prep modules.
-/
@[rep_depth operator]
def AsanoNondegenerateTopologicalTheorem : Prop :=
  ∀ {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ},
    (0 : ℂ) ∉ K₁ →
    (0 : ℂ) ∉ K₂ →
    IsClosed K₁ →
    IsClosed K₂ →
    D ≠ 0 →
    A * D - B * C ≠ 0 →
    (∀ z₁ z₂ : ℂ,
      z₁ ∉ K₁ →
      z₂ ∉ K₂ →
      asanoPhi A B C D z₁ z₂ ≠ 0) →
    A + D * z = 0 →
    z ∈ negProductSet K₁ K₂

/--
Full two-variable Asano contraction, reduced to the remaining native
nondegenerate topological branch.

This is a real Lean proof of the reduction, not a source claim.
-/
@[rep_depth operator]
theorem asano_contraction_full_of_nondegenerate_topology
    (hTop : AsanoNondegenerateTopologicalTheorem)
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hzOff : z ∉ negProductSet K₁ K₂) :
    A + D * z ≠ 0 := by
  by_cases hD : D = 0
  · subst hD
    exact asano_contraction_D_eq_zero_nonzero h0K₁ h0K₂ hPhi

  by_cases hDet : A * D - B * C = 0
  · exact
      asano_det_zero_contraction_nonzero_off_negProductSet
        h0K₁ h0K₂ hD hDet hPhi hzOff

  · intro hroot
    exact hzOff
      (hTop
        h0K₁ h0K₂ hClosed₁ hClosed₂
        hD hDet hPhi hroot)

/--
Contrapositive root-location form of the full Asano contraction.

If `A + D*z = 0`, then `z` lies in the contracted forbidden set,
assuming the one remaining nondegenerate topological branch.
-/
@[rep_depth operator]
theorem asano_contraction_root_mem_negProductSet_of_nondegenerate_topology
    (hTop : AsanoNondegenerateTopologicalTheorem)
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hroot : A + D * z = 0) :
    z ∈ negProductSet K₁ K₂ := by
  by_contra hzOff
  exact
    (asano_contraction_full_of_nondegenerate_topology
      hTop h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff)
      hroot

/--
Paired full Asano closure under the abstract nondegenerate topological branch:
1) outside forbidden set implies contraction nonvanishing;
2) contracted root implies forbidden-set membership.
-/
@[rep_depth operator]
theorem asano_contraction_pair_of_nondegenerate_topology
    (hTop : AsanoNondegenerateTopologicalTheorem)
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0) :
    (z ∉ negProductSet K₁ K₂ → A + D * z ≠ 0)
      ∧ (A + D * z = 0 → z ∈ negProductSet K₁ K₂) := by
  refine ⟨?_, ?_⟩
  · intro hzOff
    exact asano_contraction_full_of_nondegenerate_topology
      hTop h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff
  · intro hroot
    exact asano_contraction_root_mem_negProductSet_of_nondegenerate_topology
      hTop h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hroot

/--
Full two-variable Asano contraction from a concrete nondegenerate endpoint
alternative hypothesis.

This removes the abstract nondegenerate root-membership premise and replaces it
with the endpoint alternative used by the native endpoint theorem.
-/
@[rep_depth operator]
theorem asano_contraction_full_of_endpoint_nondegenerate
    (hEndpointNonDeg :
      ∀ {K₁ K₂ : Set ℂ} {A B C D z : ℂ},
        (0 : ℂ) ∉ K₁ →
        (0 : ℂ) ∉ K₂ →
        IsClosed K₁ →
        IsClosed K₂ →
        D ≠ 0 →
        A * D - B * C ≠ 0 →
        (∀ z₁ z₂ : ℂ,
          z₁ ∉ K₁ →
          z₂ ∉ K₂ →
          asanoPhi A B C D z₁ z₂ ≠ 0) →
        A + D * z = 0 →
        ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂)))
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hzOff : z ∉ negProductSet K₁ K₂) :
    A + D * z ≠ 0 := by
  by_cases hD : D = 0
  · subst hD
    exact asano_contraction_D_eq_zero_nonzero h0K₁ h0K₂ hPhi
  by_cases hDet : A * D - B * C = 0
  · exact
      asano_det_zero_contraction_nonzero_off_negProductSet
        h0K₁ h0K₂ hD hDet hPhi hzOff
  · intro hroot
    have hend :
        (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂) :=
      hEndpointNonDeg h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot
    exact hzOff
      (asano_nondegenerate_root_mem_negProductSet_of_endpoint
        h0K₁ h0K₂ hD hPhi hroot hend)

/--
Contrapositive root-location form of endpoint-based full Asano contraction.

If `A + D*z = 0`, then `z` lies in the contracted forbidden set, assuming the
concrete nondegenerate endpoint alternative hypothesis.
-/
@[rep_depth operator]
theorem asano_contraction_root_mem_negProductSet_of_endpoint_nondegenerate
    (hEndpointNonDeg :
      ∀ {K₁ K₂ : Set ℂ} {A B C D z : ℂ},
        (0 : ℂ) ∉ K₁ →
        (0 : ℂ) ∉ K₂ →
        IsClosed K₁ →
        IsClosed K₂ →
        D ≠ 0 →
        A * D - B * C ≠ 0 →
        (∀ z₁ z₂ : ℂ,
          z₁ ∉ K₁ →
          z₂ ∉ K₂ →
          asanoPhi A B C D z₁ z₂ ≠ 0) →
        A + D * z = 0 →
        ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂)))
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hroot : A + D * z = 0) :
    z ∈ negProductSet K₁ K₂ := by
  by_contra hzOff
  exact
    (asano_contraction_full_of_endpoint_nondegenerate
      hEndpointNonDeg h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff)
      hroot

/--
Paired full endpoint-based Asano closure:
1) outside forbidden set implies the contracted polynomial is nonzero;
2) a contracted root lies in the forbidden set.
-/
@[rep_depth operator]
theorem asano_contraction_pair_of_endpoint_nondegenerate
    (hEndpointNonDeg :
      ∀ {K₁ K₂ : Set ℂ} {A B C D z : ℂ},
        (0 : ℂ) ∉ K₁ →
        (0 : ℂ) ∉ K₂ →
        IsClosed K₁ →
        IsClosed K₂ →
        D ≠ 0 →
        A * D - B * C ≠ 0 →
        (∀ z₁ z₂ : ℂ,
          z₁ ∉ K₁ →
          z₂ ∉ K₂ →
          asanoPhi A B C D z₁ z₂ ≠ 0) →
        A + D * z = 0 →
        ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂)))
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0) :
    (z ∉ negProductSet K₁ K₂ → A + D * z ≠ 0)
      ∧ (A + D * z = 0 → z ∈ negProductSet K₁ K₂) := by
  refine ⟨?_, ?_⟩
  · intro hzOff
    exact asano_contraction_full_of_endpoint_nondegenerate
      hEndpointNonDeg h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff
  · intro hroot
    exact asano_contraction_root_mem_negProductSet_of_endpoint_nondegenerate
      hEndpointNonDeg h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hroot

/--
Contrapositive form of endpoint-based full Asano contraction:
outside the forbidden set, the contracted polynomial cannot vanish.
-/
@[rep_depth operator]
theorem not_root_of_not_mem_negProductSet_of_endpoint_nondegenerate
    (hEndpointNonDeg :
      ∀ {K₁ K₂ : Set ℂ} {A B C D z : ℂ},
        (0 : ℂ) ∉ K₁ →
        (0 : ℂ) ∉ K₂ →
        IsClosed K₁ →
        IsClosed K₂ →
        D ≠ 0 →
        A * D - B * C ≠ 0 →
        (∀ z₁ z₂ : ℂ,
          z₁ ∉ K₁ →
          z₂ ∉ K₂ →
          asanoPhi A B C D z₁ z₂ ≠ 0) →
        A + D * z = 0 →
        ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂)))
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hzOff : z ∉ negProductSet K₁ K₂) :
    ¬ (A + D * z = 0) := by
  intro hroot
  exact hzOff
    (asano_contraction_root_mem_negProductSet_of_endpoint_nondegenerate
      hEndpointNonDeg h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hroot)

end InfoGeometry.Canonical.LeeYangAsanoNativeCore
