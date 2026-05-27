import Mathlib
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Canonical.LeeYangAsanoDigest
import InfoGeometry.Canonical.LeeYangAsanoNativeCore
import InfoGeometry.Canonical.LeeYangAsanoNondegeneratePrep
import InfoGeometry.Canonical.LeeYangAsanoEndpointNative
import InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint
import InfoGeometry.Canonical.AsanoRuelleNondegenerateBridge
import InfoGeometry.Canonical.AsanoRuelleNondegenerateClosure
import InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint
import InfoGeometry.Analysis.AsanoContractionNative
import InfoGeometry.AsanoRuelle.TopologicalEndpoint

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
Bounded-left-branch native nondegenerate theorem (`K₂` bounded).

This is the concrete theorem currently closed by direct native proofs.
-/
@[rep_depth operator]
def AsanoNondegenerateTopologicalTheoremLeftBounded : Prop :=
  ∀ {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ},
    (0 : ℂ) ∉ K₁ →
    (0 : ℂ) ∉ K₂ →
    IsClosed K₁ →
    Bornology.IsBounded K₂ →
    D ≠ 0 →
    A * D - B * C ≠ 0 →
    (∀ z₁ z₂ : ℂ,
      z₁ ∉ K₁ →
      z₂ ∉ K₂ →
      asanoPhi A B C D z₁ z₂ ≠ 0) →
    A + D * z = 0 →
    z ∈ negProductSet K₁ K₂

/--
Native nondegenerate theorem with combined boundedness:
`Bornology.IsBounded K₁ ∨ Bornology.IsBounded K₂`.
-/
@[rep_depth operator]
def AsanoNondegenerateTopologicalTheoremBoundedOr : Prop :=
  ∀ {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ},
    (0 : ℂ) ∉ K₁ →
    (0 : ℂ) ∉ K₂ →
    IsClosed K₁ →
    IsClosed K₂ →
    (Bornology.IsBounded K₁ ∨ Bornology.IsBounded K₂) →
    D ≠ 0 →
    A * D - B * C ≠ 0 →
    (∀ z₁ z₂ : ℂ,
      z₁ ∉ K₁ →
      z₂ ∉ K₂ →
      asanoPhi A B C D z₁ z₂ ≠ 0) →
    A + D * z = 0 →
    z ∈ negProductSet K₁ K₂

/--
Direct realization of the bounded nondegenerate theorem from the native
Asano-Ruelle closure module.
-/
@[rep_depth operator]
theorem asanoNondegenerateTopologicalTheoremLeftBounded_native :
    AsanoNondegenerateTopologicalTheoremLeftBounded := by
  intro K₁ K₂ A B C D z h0K₁ h0K₂ hClosed₁ hBdd₂ hD hDet hPhi hroot
  exact
    InfoGeometry.Canonical.AsanoRuelle.asano_nondegenerate_closure_left_bdd
      A B C D z K₁ K₂ hD hDet hClosed₁ hBdd₂ h0K₁ h0K₂ hPhi hroot

/--
Direct realization of the combined-bounded native nondegenerate theorem.
-/
@[rep_depth operator]
theorem asanoNondegenerateTopologicalTheoremBoundedOr_native :
    AsanoNondegenerateTopologicalTheoremBoundedOr := by
  intro K₁ K₂ A B C D z h0K₁ h0K₂ hClosed₁ hClosed₂ hBddOr hD hDet hPhi hroot
  exact
    InfoGeometry.Canonical.AsanoRuelle.asano_nondegenerate_closure_bdd_or
      A B C D z K₁ K₂ hD hDet hClosed₁ hClosed₂ hBddOr h0K₁ h0K₂ hPhi hroot

/--
Direct bridge: the Asano-Ruelle source claim implies the remaining
nondegenerate topological Asano theorem.

This discharges the topological branch from a single literature-owned source
theorem surface, without endpoint certificates.
-/
@[rep_depth operator]
theorem asanoNondegenerateTopologicalTheorem_of_asanoRuelleSource
    (hAR :
      InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaim) :
    AsanoNondegenerateTopologicalTheorem := by
  intro K₁ K₂ A B C D z h0K₁ h0K₂ hClosed₁ hClosed₂ _hD _hDet hPhi hroot
  let P : InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial :=
    { A := A, B := B, C := C, D := D }
  have hPhiP :
      ∀ z₁ z₂ : ℂ, z₁ ∉ K₁ → z₂ ∉ K₂ →
        InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.eval P z₁ z₂ ≠ 0 := by
    intro z₁ z₂ hz₁ hz₂
    simpa [P, InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.eval, asanoPhi]
      using hPhi z₁ z₂ hz₁ hz₂
  by_contra hzNot
  have hzNotForbidden :
      z ∉ InfoGeometry.Canonical.LeeYangAsanoDigest.asanoForbiddenSet K₁ K₂ := by
    simpa [negProductSet, InfoGeometry.Canonical.LeeYangAsanoDigest.asanoForbiddenSet] using hzNot
  have hcontractNe :
      InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract P z ≠ 0 :=
    hAR K₁ K₂ P h0K₁ h0K₂ hClosed₁ hClosed₂ hPhiP z hzNotForbidden
  have hcontractZero :
      InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract P z = 0 := by
    simpa [P, InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract, asanoPhi] using hroot
  exact hcontractNe hcontractZero

/--
Full Asano contraction derived directly from the Asano-Ruelle source claim.

This bypasses endpoint-certificate surfaces and routes through the single
source theorem bridge.
-/
@[rep_depth operator]
theorem asano_contraction_full_of_asanoRuelleSource
    (hAR :
      InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaim)
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
        A + B * z₁ + C * z₂ + D * z₁ * z₂ ≠ 0)
    (hzOff : z ∉ negProductSet K₁ K₂) :
    A + D * z ≠ 0 := by
  let P : InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial :=
    { A := A, B := B, C := C, D := D }
  have hPhiP :
      ∀ z₁ z₂ : ℂ, z₁ ∉ K₁ → z₂ ∉ K₂ →
        InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.eval P z₁ z₂ ≠ 0 := by
    intro z₁ z₂ hz₁ hz₂
    simpa [P, InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.eval, asanoPhi]
      using hPhi z₁ z₂ hz₁ hz₂
  have hzOffForbidden :
      z ∉ InfoGeometry.Canonical.LeeYangAsanoDigest.asanoForbiddenSet K₁ K₂ := by
    simpa [negProductSet, InfoGeometry.Canonical.LeeYangAsanoDigest.asanoForbiddenSet] using hzOff
  have hcontractNe :
      InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract P z ≠ 0 :=
    hAR K₁ K₂ P h0K₁ h0K₂ hClosed₁ hClosed₂ hPhiP z hzOffForbidden
  simpa [P, InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract, asanoPhi]
    using hcontractNe

/--
Contrapositive root-localization form derived directly from the Asano-Ruelle
source claim.
-/
@[rep_depth operator]
theorem asano_contraction_root_mem_negProductSet_of_asanoRuelleSource
    (hAR :
      InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaim)
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
    (asano_contraction_full_of_asanoRuelleSource
      hAR h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff) hroot

/--
Paired full Asano closure derived directly from the Asano-Ruelle source claim:
1) outside forbidden set implies contraction nonvanishing;
2) contracted root implies forbidden-set membership.
-/
@[rep_depth operator]
theorem asano_contraction_pair_of_asanoRuelleSource
    (hAR :
      InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaim)
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
    exact
      asano_contraction_full_of_asanoRuelleSource
        hAR h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff
  · intro hroot
    exact
      asano_contraction_root_mem_negProductSet_of_asanoRuelleSource
        hAR h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hroot

/--
The nondegenerate topological Asano theorem implies the closed-set
Asano-Ruelle source claim.
-/
@[rep_depth operator]
theorem asanoRuelleLemmaSourceClaimClosed_of_nondegenerateTopological
    (hTop : AsanoNondegenerateTopologicalTheorem) :
    InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaimClosed := by
  intro K1 K2 P h0K1 h0K2 hClosed1 hClosed2 hPhi z hzOff
  have hPhi' :
      ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 →
        asanoPhi P.A P.B P.C P.D z1 z2 ≠ 0 := by
    intro z1 z2 hz1 hz2
    simpa [asanoPhi, InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.eval]
      using hPhi z1 z2 hz1 hz2
  have hzOff' : z ∉ negProductSet K1 K2 := by
    simpa [negProductSet, InfoGeometry.Canonical.LeeYangAsanoDigest.asanoForbiddenSet] using hzOff
  have hne : P.A + P.D * z ≠ 0 := by
    by_cases hD : P.D = 0
    · rw [hD]
      have hPhi0 :
          ∀ z1 z2 : ℂ,
            z1 ∉ K1 → z2 ∉ K2 →
              asanoPhi P.A P.B P.C 0 z1 z2 ≠ 0 := by
        intro z1 z2 hz1 hz2
        simpa [hD] using hPhi' z1 z2 hz1 hz2
      exact asano_contraction_D_eq_zero_nonzero h0K1 h0K2 hPhi0
    · by_cases hDet : P.A * P.D - P.B * P.C = 0
      · exact
          asano_det_zero_contraction_nonzero_off_negProductSet
            h0K1 h0K2 hD hDet hPhi' hzOff'
      · intro hroot
        exact hzOff'
          (hTop h0K1 h0K2 hClosed1 hClosed2 hD hDet hPhi' hroot)
  simpa [InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract] using hne

/--
Bounded closed-set Asano-Ruelle source claim from the nondegenerate topological theorem.

This is the corrected positive theorem surface used by the Lee--Yang lane.
-/
@[rep_depth operator]
theorem asanoRuelleLemmaSourceClaimClosedBounded_of_nondegenerateTopological
    (hTop : AsanoNondegenerateTopologicalTheorem) :
    InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaimClosedBounded := by
  intro K1 K2 P h0K1 h0K2 hClosed1 hClosed2 _hB1 _hB2 hPhi z hzOff
  have hPhi' :
      ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 →
        asanoPhi P.A P.B P.C P.D z1 z2 ≠ 0 := by
    intro z1 z2 hz1 hz2
    simpa [asanoPhi, InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.eval]
      using hPhi z1 z2 hz1 hz2
  have hzOff' : z ∉ negProductSet K1 K2 := by
    simpa [negProductSet, InfoGeometry.Canonical.LeeYangAsanoDigest.asanoForbiddenSet] using hzOff
  have hne : P.A + P.D * z ≠ 0 := by
    by_cases hD : P.D = 0
    · rw [hD]
      have hPhi0 :
          ∀ z1 z2 : ℂ,
            z1 ∉ K1 → z2 ∉ K2 →
              asanoPhi P.A P.B P.C 0 z1 z2 ≠ 0 := by
        intro z1 z2 hz1 hz2
        simpa [hD] using hPhi' z1 z2 hz1 hz2
      exact asano_contraction_D_eq_zero_nonzero h0K1 h0K2 hPhi0
    · by_cases hDet : P.A * P.D - P.B * P.C = 0
      · exact
          asano_det_zero_contraction_nonzero_off_negProductSet
            h0K1 h0K2 hD hDet hPhi' hzOff'
      · intro hroot
        exact hzOff'
          (hTop h0K1 h0K2 hClosed1 hClosed2 hD hDet hPhi' hroot)
  simpa [InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract] using hne

/--
Conversely, the closed-set Asano-Ruelle source claim implies the remaining
nondegenerate topological Asano theorem.
-/
@[rep_depth operator]
theorem asanoNondegenerateTopologicalTheorem_of_asanoRuelleClosed
    (hARc :
      _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaimClosed) :
    AsanoNondegenerateTopologicalTheorem := by
  intro K₁ K₂ A B C D z h0K₁ h0K₂ hClosed₁ hClosed₂ _hD _hDet hPhi hroot
  let P : _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial :=
    { A := A, B := B, C := C, D := D }
  have hPhiP :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ → z₂ ∉ K₂ →
          _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.eval P z₁ z₂ ≠ 0 := by
    intro z₁ z₂ hz₁ hz₂
    simpa [P, _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.eval, asanoPhi]
      using hPhi z₁ z₂ hz₁ hz₂
  by_contra hzNot
  have hzOff :
      z ∉ _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.asanoForbiddenSet K₁ K₂ := by
    simpa [negProductSet, _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.asanoForbiddenSet] using hzNot
  have hne :
      _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract P z ≠ 0 :=
    _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.asanoRuelleClosed_apply
      hARc P h0K₁ h0K₂ hClosed₁ hClosed₂ hPhiP hzOff
  have hzero :
      _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract P z = 0 := by
    simpa [P, _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract, asanoPhi] using hroot
  exact hne hzero

/--
Bounded nondegenerate topological Asano theorem.

This is the bounded variant that exactly matches the corrected
closed-bounded source-claim surface.
-/
@[rep_depth operator]
def AsanoNondegenerateTopologicalTheoremBounded : Prop :=
  ∀ {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ},
    (0 : ℂ) ∉ K₁ →
    (0 : ℂ) ∉ K₂ →
    IsClosed K₁ →
    IsClosed K₂ →
    Bornology.IsBounded K₁ →
    Bornology.IsBounded K₂ →
    D ≠ 0 →
    A * D - B * C ≠ 0 →
    (∀ z₁ z₂ : ℂ,
      z₁ ∉ K₁ →
      z₂ ∉ K₂ →
      asanoPhi A B C D z₁ z₂ ≠ 0) →
    A + D * z = 0 →
    z ∈ negProductSet K₁ K₂

/--
Closed-bounded Asano-Ruelle source claim implies the bounded nondegenerate
topological Asano theorem.
-/
@[rep_depth operator]
theorem asanoNondegenerateTopologicalTheoremBounded_of_asanoRuelleClosedBounded
    (hARcb :
      _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaimClosedBounded) :
    AsanoNondegenerateTopologicalTheoremBounded := by
  intro K₁ K₂ A B C D z h0K₁ h0K₂ hClosed₁ hClosed₂ hB1 hB2 _hD _hDet hPhi hroot
  let P : _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial :=
    { A := A, B := B, C := C, D := D }
  have hPhiP :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ → z₂ ∉ K₂ →
          _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.eval P z₁ z₂ ≠ 0 := by
    intro z₁ z₂ hz₁ hz₂
    simpa [P, _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.eval, asanoPhi]
      using hPhi z₁ z₂ hz₁ hz₂
  by_contra hzNot
  have hzOff :
      z ∉ _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.asanoForbiddenSet K₁ K₂ := by
    simpa [negProductSet, _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.asanoForbiddenSet] using hzNot
  have hne :
      _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract P z ≠ 0 :=
    _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.asanoRuelleClosedBounded_apply
      hARcb P h0K₁ h0K₂ hClosed₁ hClosed₂ hB1 hB2 hPhiP hzOff
  have hzero :
      _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract P z = 0 := by
    simpa [P, _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.TwoVarAffinePolynomial.contract, asanoPhi] using hroot
  exact hne hzero

/--
Exact equivalence of the remaining two mathematical surfaces:
the nondegenerate topological Asano theorem and the closed-set
Asano-Ruelle source claim.
-/
@[rep_depth operator]
theorem asanoNondegenerateTopological_iff_asanoRuelleClosed :
    AsanoNondegenerateTopologicalTheorem ↔
      _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaimClosed := by
  constructor
  · exact asanoRuelleLemmaSourceClaimClosed_of_nondegenerateTopological
  · exact asanoNondegenerateTopologicalTheorem_of_asanoRuelleClosed

/--
Closed-set Asano-Ruelle source claim from the endpoint-nondegenerate hypothesis.
-/
@[rep_depth operator]
theorem asanoRuelleLemmaSourceClaimClosed_of_endpointNonDeg
    (hEndpointNonDeg :
      ∀ {K₁ K₂ : Set ℂ} {A B C D : ℂ},
        (0 : ℂ) ∉ K₁ →
        (0 : ℂ) ∉ K₂ →
        (∀ z₁ z₂ : ℂ,
          z₁ ∉ K₁ →
          z₂ ∉ K₂ →
          InfoGeometry.Analysis.AsanoContractionNative.asanoPoly A B C D z₁ z₂ ≠ 0) →
        D ≠ 0 →
        A * D - B * C ≠ 0 →
        ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂))) :
    _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaimClosed := by
  exact
    _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.asanoRuelleLemmaSourceClaimClosed_of_sourceClaim
      (_root_.InfoGeometry.Canonical.LeeYangAsanoDigest.asanoRuelleLemmaSourceClaim_of_endpointNonDeg
        hEndpointNonDeg)

/--
Bounded closed-set Asano-Ruelle source claim from the endpoint-nondegenerate hypothesis.
-/
@[rep_depth operator]
theorem asanoRuelleLemmaSourceClaimClosedBounded_of_endpointNonDeg
    (hEndpointNonDeg :
      ∀ {K₁ K₂ : Set ℂ} {A B C D : ℂ},
        (0 : ℂ) ∉ K₁ →
        (0 : ℂ) ∉ K₂ →
        (∀ z₁ z₂ : ℂ,
          z₁ ∉ K₁ →
          z₂ ∉ K₂ →
          InfoGeometry.Analysis.AsanoContractionNative.asanoPoly A B C D z₁ z₂ ≠ 0) →
        D ≠ 0 →
        A * D - B * C ≠ 0 →
        ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂))) :
    _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.AsanoRuelleLemmaSourceClaimClosedBounded := by
  exact
    _root_.InfoGeometry.Canonical.LeeYangAsanoDigest.asanoRuelleLemmaSourceClaimClosedBounded_of_sourceClaim
      (_root_.InfoGeometry.Canonical.LeeYangAsanoDigest.asanoRuelleLemmaSourceClaim_of_endpointNonDeg
        hEndpointNonDeg)

/--
If the concrete endpoint-alternative theorem is available, then the abstract
nondegenerate topological Asano target is discharged.
-/
@[rep_depth operator]
theorem asanoNondegenerateTopologicalTheorem_of_endpoint
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
        ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂))) :
    AsanoNondegenerateTopologicalTheorem := by
  intro K₁ K₂ A B C D z h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot
  have hend :
      (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂) :=
    hEndpointNonDeg h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot
  exact
    asano_nondegenerate_root_mem_negProductSet_of_endpoint
      h0K₁ h0K₂ hD hPhi hroot hend

/--
Bounded nondegenerate topological Asano theorem from the explicit
topological-endpoint claim surface.
-/
@[rep_depth operator]
theorem asanoNondegenerateTopologicalTheoremBounded_of_topologicalEndpoint
    (hTop :
      ∀ {K₁ K₂ : Set ℂ} {A B C D z : ℂ},
        (h0K₁ : (0 : ℂ) ∉ K₁) →
        (h0K₂ : (0 : ℂ) ∉ K₂) →
        (hClosed₁ : IsClosed K₁) →
        (hClosed₂ : IsClosed K₂) →
        (hB₂ : Bornology.IsBounded K₂) →
        (hPhi :
          ∀ z₁ z₂ : ℂ,
            z₁ ∉ K₁ →
            z₂ ∉ K₂ →
            A + B * z₁ + C * z₂ + D * z₁ * z₂ ≠ 0) →
        (hD : D ≠ 0) →
        (hDet : A * D - B * C ≠ 0) →
        (hQ : A + D * z = 0) →
        InfoGeometry.AsanoRuelle.asanoRuelleTopologicalEndpointClaim
          K₁ K₂ hClosed₁ hClosed₂ hB₂ A B C D z hPhi hD hDet hQ) :
    AsanoNondegenerateTopologicalTheoremBounded := by
  intro K₁ K₂ A B C D z h0K₁ h0K₂ hClosed₁ hClosed₂ _hB₁ hB₂ hD hDet hPhi hroot
  have hend :
      (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂) := by
    have hclaim :=
      hTop h0K₁ h0K₂ hClosed₁ hClosed₂ hB₂
        (fun z₁ z₂ hz₁ hz₂ => hPhi z₁ z₂ hz₁ hz₂)
        hD hDet hroot
    simpa [InfoGeometry.AsanoRuelle.asanoRuelleTopologicalEndpointClaim, neg_div] using hclaim
  exact
    asano_nondegenerate_root_mem_negProductSet_of_endpoint
      h0K₁ h0K₂ hD hPhi hroot hend

/--
Pointwise endpoint alternative derived from the explicit topological-endpoint
claim surface.

This bridges `AsanoRuelle.TopologicalEndpoint` into the native nondegenerate
Asano lane for fixed coefficients and forbidden sets.
-/
@[rep_depth operator]
theorem endpoint_alternative_of_topologicalEndpoint_pointwise
    {K₁ K₂ : Set ℂ} {A B C D : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hK₂_bdd : Bornology.IsBounded K₂)
    (hD : D ≠ 0)
    (hDet : A * D - B * C ≠ 0)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hTop :
      ∀ z : ℂ, ∀ hQ : A + D * z = 0,
        InfoGeometry.AsanoRuelle.asanoRuelleTopologicalEndpointClaim
          K₁ K₂ hClosed₁ hClosed₂ hK₂_bdd
          A B C D z
          (fun z₁ z₂ hz₁ hz₂ => hPhi z₁ z₂ hz₁ hz₂)
          hD hDet hQ) :
    (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂) := by
  have hzf :
      InfoGeometry.Analysis.AsanoContractionNative.ZeroFreeOutside K₁ K₂ A B C D := by
    intro z₁ z₂ hz₁ hz₂
    simpa [InfoGeometry.Analysis.AsanoContractionNative.asanoPoly]
      using hPhi z₁ z₂ hz₁ hz₂
  exact InfoGeometry.Analysis.AsanoContractionNative.nonDegenerate_endpoint_of_topologicalEndpointSpec
    hClosed₁ hClosed₂ hK₂_bdd hzf hD hDet
    (by
      intro z hQ
      simpa [InfoGeometry.AsanoRuelle.asanoRuelleTopologicalEndpointClaim] using hTop z hQ)

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
Contrapositive form under the abstract nondegenerate topological branch:
outside the forbidden set, the contracted polynomial cannot vanish.
-/
@[rep_depth operator]
theorem not_root_of_not_mem_negProductSet_of_nondegenerate_topology
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
    ¬ (A + D * z = 0) := by
  intro hroot
  exact hzOff
    (asano_contraction_root_mem_negProductSet_of_nondegenerate_topology
      hTop h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hroot)

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
    A + D * z ≠ 0 :=
  asano_contraction_full_of_nondegenerate_topology
    (asanoNondegenerateTopologicalTheorem_of_endpoint hEndpointNonDeg)
    h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi hzOff

/--
Full Asano contraction from the concrete topological-left endpoint theorem.

This removes explicit endpoint assumptions and consumes the proved
`asano_endpoint_disjunction_left` surface (bounded `K₂`, closed `K₁`).
-/
@[rep_depth operator]
theorem asano_contraction_full_of_topological_left
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hBdd₂ : Bornology.IsBounded K₂)
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
  · by_cases hdet : A * D - B * C = 0
    · exact asano_det_zero_contraction_nonzero_off_negProductSet
        h0K₁ h0K₂ hD hdet hPhi hzOff
    · intro hroot
      exact hzOff
        (asano_nondegenerate_root_mem_negProductSet_of_topological_left
          h0K₁ h0K₂ hClosed₁ hBdd₂ hD hdet hPhi hroot)

/--
Full Asano contraction from the combined symmetric endpoint disjunction:
`K₁`, `K₂` closed and at least one bounded.
-/
@[rep_depth operator]
theorem asano_contraction_full_of_topological_combined
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hClosed₂ : IsClosed K₂)
    (hBddOr : Bornology.IsBounded K₁ ∨ Bornology.IsBounded K₂)
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
  · by_cases hDet : A * D - B * C = 0
    · exact asano_det_zero_contraction_nonzero_off_negProductSet
        h0K₁ h0K₂ hD hDet hPhi hzOff
    · intro hroot
      have hEnd :
          (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂) := by
        simpa [neg_div] using
          InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint.asano_endpoint_disjunction_combined
            A B C D K₁ K₂ hD hDet hClosed₁ hClosed₂ hBddOr h0K₁ h0K₂ hPhi
      exact hzOff
        (asano_nondegenerate_root_mem_negProductSet_of_endpoint
          h0K₁ h0K₂ hD hPhi hroot hEnd)

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
      ∧ (A + D * z = 0 → z ∈ negProductSet K₁ K₂) :=
  asano_contraction_pair_of_nondegenerate_topology
    (asanoNondegenerateTopologicalTheorem_of_endpoint hEndpointNonDeg)
    h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi

/--
Endpoint-based paired closure: first-component readout.
-/
@[rep_depth operator]
theorem asano_contraction_full_of_endpoint_nondegenerate_via_pair
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
  exact (asano_contraction_pair_of_endpoint_nondegenerate
    hEndpointNonDeg h0K₁ h0K₂ hClosed₁ hClosed₂ hPhi).1 hzOff

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
