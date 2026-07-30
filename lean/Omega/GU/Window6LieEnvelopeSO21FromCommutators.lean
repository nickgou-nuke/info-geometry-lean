import Mathlib.Tactic
import Omega.GU.Window6PushEnvelopeCertificateUpgrade

namespace Omega.GU

theorem paper_window6_lie_envelope_so21_from_commutators :
  window6CommutatorSeedIsSkew ∧
    window6PushEnvelopeCertificate.commutatorTarget = .orthogonal ∧
    window6PushEnvelopeCertificate.ambientDimension = 21 ∧
    window6PushEnvelopeCertificate.orthogonalDimension =
      window6PushEnvelopeCertificate.ambientDimension *
        (window6PushEnvelopeCertificate.ambientDimension - 1) / 2 ∧
    window6PushEnvelopeCertificate.orthogonalDimension = 210 := by

  have hcert := paper_window6_push_envelope_certificate_upgrade
  rcases hcert with ⟨horth, _, hdim⟩
  rcases horth with ⟨hskew, htarget, hambient, hformula⟩
  rcases hdim with ⟨hdim210, _, _, _, _⟩
  exact ⟨hskew, htarget, hambient, hformula, hdim210⟩

end Omega.GU
