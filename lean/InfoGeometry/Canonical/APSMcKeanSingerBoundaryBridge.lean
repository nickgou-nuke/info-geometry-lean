import Mathlib

/-!
# APS / McKean-Singer Boundary Bridge

This module owns the theorem-safe scalar plumbing suggested by the
McKean-Singer heat supertrace formula and the Atiyah-Patodi-Singer boundary
correction pattern.

The file is intentionally conditional.  It does not prove heat-kernel
asymptotics, Dirac Fredholm theory, cylindrical-end elliptic regularity,
Seiberg-Witten compactness, a genuine `\hat A` genus calculation, an
eta-invariant theorem, or any Riemann-zeta consequence.

#### BUCKET 1: CLOSED FINITE THEOREMS
The theorems below are closed scalar equalities over an additive group.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The conclusions depend on explicit premises:

* `hMS : finiteSupertrace = analyticIndex`;
* `hAPS : analyticIndex = bulkAhatTerm - etaCorrection`;
* `hAhat : bulkAhatTerm = 0`;
* `hEta : etaCorrection = 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
Actual McKean-Singer analysis, APS index theory on manifolds with cylindrical
ends, Seiberg-Witten monopole theory, KMS/cooling geometry, and RH/zeta-zero
interpretations.
-/

namespace InfoGeometry.Canonical.APSMcKeanSingerBoundaryBridge

/--
If the APS index readout is `bulkAhatTerm - etaCorrection`, and both the bulk
and eta terms vanish, then the analytic index vanishes.
-/
theorem analytic_index_zero_of_ahat_and_eta_vanish
    {R : Type*} [AddGroup R]
    (analyticIndex bulkAhatTerm etaCorrection : R)
    (hAPS : analyticIndex = bulkAhatTerm - etaCorrection)
    (hAhat : bulkAhatTerm = 0)
    (hEta : etaCorrection = 0) :
    analyticIndex = 0 := by
  rw [hAPS, hAhat, hEta]
  simp

/--
McKean-Singer plus APS zero-boundary readout.

If the finite supertrace is identified with the analytic index, and the APS
bulk and eta correction terms both vanish, then the finite supertrace vanishes.
-/
theorem finite_supertrace_zero_of_mckean_singer_aps_vanishing
    {R : Type*} [AddGroup R]
    (finiteSupertrace analyticIndex bulkAhatTerm etaCorrection : R)
    (hMS : finiteSupertrace = analyticIndex)
    (hAPS : analyticIndex = bulkAhatTerm - etaCorrection)
    (hAhat : bulkAhatTerm = 0)
    (hEta : etaCorrection = 0) :
    finiteSupertrace = 0 := by
  rw [hMS]
  exact analytic_index_zero_of_ahat_and_eta_vanish
    analyticIndex bulkAhatTerm etaCorrection hAPS hAhat hEta

/--
Bundled APS/McKean-Singer scalar corridor.

This is the complete closed theorem in this file: from explicit McKean-Singer
identification and explicit vanishing of the APS bulk and eta terms, both the
analytic index and the finite supertrace vanish.
-/
theorem aps_mckean_singer_boundary_capstone
    {R : Type*} [AddGroup R]
    (finiteSupertrace analyticIndex bulkAhatTerm etaCorrection : R)
    (hMS : finiteSupertrace = analyticIndex)
    (hAPS : analyticIndex = bulkAhatTerm - etaCorrection)
    (hAhat : bulkAhatTerm = 0)
    (hEta : etaCorrection = 0) :
    analyticIndex = 0 ∧ finiteSupertrace = 0 :=
  ⟨analytic_index_zero_of_ahat_and_eta_vanish
      analyticIndex bulkAhatTerm etaCorrection hAPS hAhat hEta,
    finite_supertrace_zero_of_mckean_singer_aps_vanishing
      finiteSupertrace analyticIndex bulkAhatTerm etaCorrection
      hMS hAPS hAhat hEta⟩

end InfoGeometry.Canonical.APSMcKeanSingerBoundaryBridge
