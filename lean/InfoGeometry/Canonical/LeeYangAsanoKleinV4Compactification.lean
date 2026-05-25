import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Canonical.LeeYangAsanoEndpointNative
import InfoGeometry.Canonical.LeeYangAsanoFullReduction

/-!
# InfoGeometry.Canonical.LeeYangAsanoKleinV4Compactification

Klein-four / Möbius-CPT compactification socket for the remaining
nondegenerate Asano topological branch.

This file does not prove the Riemann-sphere covering theorem.

It packages the expected finite symmetry mechanism:

* four-element Klein orbit carrier;
* Möbius/CPT endpoint representatives;
* endpoint alternative extraction;
* reduction from that extraction to `AsanoNondegenerateTopologicalTheorem`.

The actual global covering proof must instantiate this certificate.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoNativeCore

/-- The finite Klein-four symmetry labels expected in the compactified chart. -/
@[rep_depth operator]
inductive KleinV4AsanoSymmetry where
  | id
  | mobius
  | cpt
  | mobiusCpt
deriving DecidableEq, Repr, Fintype

/--
The two endpoint alternatives already consumed by
`asano_nondegenerate_root_mem_negProductSet_of_endpoint`.

Left endpoint:
`C ≠ 0 ∧ -(C / D) ∈ K₁`.

Right endpoint:
`B ≠ 0 ∧ -(B / D) ∈ K₂`.
-/
@[rep_depth operator]
inductive AsanoEndpointAlternative where
  | poleInK₁
  | infinityValueInK₂
deriving DecidableEq, Repr, Fintype

/-- Interprets an endpoint label as the actual endpoint proposition. -/
@[rep_depth operator]
def endpointAlternativeHolds
    (e : AsanoEndpointAlternative)
    {K₁ K₂ : Set ℂ}
    {A B C D : ℂ} : Prop :=
  match e with
  | AsanoEndpointAlternative.poleInK₁ =>
      C ≠ 0 ∧ -(C / D) ∈ K₁
  | AsanoEndpointAlternative.infinityValueInK₂ =>
      B ≠ 0 ∧ -(B / D) ∈ K₂

/--
Klein-four / Möbius-CPT compactification certificate.

This is the geometric socket for the missing global argument.

The certificate says: under the nondegenerate Asano hypotheses and a contracted
root, the compactified V4 orbit analysis selects one endpoint representative
and proves that its endpoint alternative holds.
-/
@[socket_debt_tag, rep_depth operator]
structure AsanoKleinV4CompactificationCertificate where
  /-- Selected V4 chart element. This makes the finite symmetry reduction explicit. -/
  symmetry :
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
      KleinV4AsanoSymmetry

  /-- Selected endpoint representative in the V4 orbit. -/
  endpoint :
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
      AsanoEndpointAlternative

  /--
  The actual compactified orbit theorem: the selected endpoint alternative
  holds. This is the one field that the future Riemann-sphere/global-covering
  proof must construct.
  -/
  endpoint_holds :
    ∀ {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
      (h0K₁ : (0 : ℂ) ∉ K₁)
      (h0K₂ : (0 : ℂ) ∉ K₂)
      (hClosed₁ : IsClosed K₁)
      (hClosed₂ : IsClosed K₂)
      (hD : D ≠ 0)
      (hDet : A * D - B * C ≠ 0)
      (hPhi :
        ∀ z₁ z₂ : ℂ,
          z₁ ∉ K₁ →
          z₂ ∉ K₂ →
          asanoPhi A B C D z₁ z₂ ≠ 0)
      (hroot : A + D * z = 0),
      endpointAlternativeHolds
        (endpoint h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot)
        (K₁ := K₁) (K₂ := K₂) (A := A) (B := B) (C := C) (D := D)

/--
A Klein-four / Möbius-CPT compactification certificate closes the remaining
nondegenerate topological Asano branch.
-/
@[rep_depth operator]
theorem asano_nondegenerate_topological_of_kleinV4_compactification
    (V4 : AsanoKleinV4CompactificationCertificate) :
    AsanoNondegenerateTopologicalTheorem := by
  intro K₁ K₂ A B C D z
    h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot
  have hend :
      (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨
      (B ≠ 0 ∧ -(B / D) ∈ K₂) := by
    cases hE :
        V4.endpoint h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot with
    | poleInK₁ =>
        left
        simpa [endpointAlternativeHolds, hE] using
          (V4.endpoint_holds h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot)
    | infinityValueInK₂ =>
        right
        simpa [endpointAlternativeHolds, hE] using
          (V4.endpoint_holds h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot)

  exact
    asano_nondegenerate_root_mem_negProductSet_of_endpoint
      h0K₁ h0K₂ hD hPhi hroot hend

/--
Full Asano contraction from the Klein-four / Möbius-CPT compactification
certificate.
-/
@[rep_depth operator]
theorem asano_contraction_full_of_kleinV4_compactification
    (V4 : AsanoKleinV4CompactificationCertificate)
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
    A + D * z ≠ 0 :=
  asano_contraction_full_of_nondegenerate_topology
    (asano_nondegenerate_topological_of_kleinV4_compactification V4)
    h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff

/--
Paired full Asano closure from the Klein-four certificate through the
topological reduction path:
1) outside forbidden set implies contraction nonvanishing;
2) contracted root implies forbidden-set membership.
-/
@[rep_depth operator]
theorem asano_contraction_pair_of_kleinV4_compactification
    (V4 : AsanoKleinV4CompactificationCertificate)
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
    exact asano_contraction_full_of_kleinV4_compactification
      V4 h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff
  · intro hroot
    exact asano_contraction_root_mem_negProductSet_of_nondegenerate_topology
      (asano_nondegenerate_topological_of_kleinV4_compactification V4)
      h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hroot

/--
Direct full Asano contraction from the Klein-four certificate through the
endpoint-based nondegenerate reduction (without routing through the abstract
`AsanoNondegenerateTopologicalTheorem` wrapper).
-/
@[rep_depth operator]
theorem asano_contraction_full_of_kleinV4_compactification_direct_endpoint
    (V4 : AsanoKleinV4CompactificationCertificate)
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
  refine asano_contraction_full_of_endpoint_nondegenerate ?hEndpoint h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff
  intro K₁ K₂ A B C D z h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot
  cases hE :
      V4.endpoint h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot with
  | poleInK₁ =>
      left
      simpa [endpointAlternativeHolds, hE] using
        (V4.endpoint_holds h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot)
  | infinityValueInK₂ =>
      right
      simpa [endpointAlternativeHolds, hE] using
        (V4.endpoint_holds h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot)

/--
Contrapositive root-location form of the direct endpoint-based Klein-V4
full Asano contraction.
-/
@[rep_depth operator]
theorem asano_contraction_root_mem_negProductSet_of_kleinV4_compactification_direct_endpoint
    (V4 : AsanoKleinV4CompactificationCertificate)
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
    (asano_contraction_full_of_kleinV4_compactification_direct_endpoint
      V4 h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff)
      hroot

/--
Paired direct endpoint-based Klein-V4 Asano closure:
1) outside forbidden set implies contraction nonvanishing;
2) contracted root implies forbidden-set membership.
-/
@[rep_depth operator]
theorem asano_contraction_pair_of_kleinV4_compactification_direct_endpoint
    (V4 : AsanoKleinV4CompactificationCertificate)
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
    exact asano_contraction_full_of_kleinV4_compactification_direct_endpoint
      V4 h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff
  · intro hroot
    exact asano_contraction_root_mem_negProductSet_of_kleinV4_compactification_direct_endpoint
      V4 h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hroot

/--
Contrapositive form of direct endpoint-based Klein-V4 full Asano contraction:
outside the forbidden set, the contracted polynomial cannot vanish.
-/
@[rep_depth operator]
theorem not_root_of_not_mem_negProductSet_of_kleinV4_compactification_direct_endpoint
    (V4 : AsanoKleinV4CompactificationCertificate)
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
    (asano_contraction_root_mem_negProductSet_of_kleinV4_compactification_direct_endpoint
      V4 h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hroot)

end InfoGeometry.Canonical.LeeYangAsanoNativeCore
