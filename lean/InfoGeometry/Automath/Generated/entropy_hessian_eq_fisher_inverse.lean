import InfoGeometry.Canonical.SouriauTheoremTranslatorPacket

namespace Automath.Generated

open InfoGeometry.Canonical.SouriauTheoremTranslatorPacket

/-!
This generated module is only a compatibility consumer.  It does not prove
the analytic identity `Hess(S) = Fisher⁻¹`: that identity is an explicit
stage-2 gate in the canonical translator packet.  Keeping the gate visible
prevents a pointwise identification supplied by a caller from being advertised
as a native Hessian/Fisher derivation.
-/

/-- Read the inverse-Hessian equality from its explicit proof-carrying gate. -/
theorem entropyHessian_eq_fisherInverse_of_gate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : EntropyFisherInverseGate E) :
    G.entropyHessian = G.fisherInverse :=
  G.entropy_hessian_eq_fisher_inverse

end Automath.Generated
