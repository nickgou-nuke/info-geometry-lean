/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.Conclusion.ReadusNullTrichotomyNormalForm
import Omega.Conclusion.ThreeEndCertificateOrthogonality

namespace Omega.Conclusion

/-- Joint conclusion-level wrapper: the three-end certificate package is sufficient on the
advertised axes, its failure modes stay orthogonal, the `NULL` outputs remain exhaustive, and no
hidden failure mode survives.
    thm:conclusion-three-end-certificate-joint-sufficiency-minimality -/
theorem paper_conclusion_three_end_certificate_joint_sufficiency_minimality
    (D : Omega.Conclusion.ThreeEndCertificateOrthogonalityData)
    (semanticNull protocolNull collisionNull hiddenFailure : Prop)
    (hexhaustive : semanticNull ∨ protocolNull ∨ collisionNull)
    (hnohidden : hiddenFailure → False) :
    D.factorsThroughProduct ∧ D.failuresAreOrthogonal ∧
      (semanticNull ∨ protocolNull ∨ collisionNull) ∧ ¬ hiddenFailure := by
  rcases
      paper_conclusion_readus_null_trichotomy_normal_form semanticNull protocolNull collisionNull
        hiddenFailure hexhaustive hnohidden with
    ⟨hTrichotomy, hNoHidden⟩
  exact ⟨D.h_factorsThroughProduct, D.h_failuresAreOrthogonal, hTrichotomy, hNoHidden⟩

end Omega.Conclusion
