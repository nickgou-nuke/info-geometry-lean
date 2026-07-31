import Mathlib.Tactic

namespace Omega.SPG

/-- Chapter-local package for the finite audit setup behind bidirectional certificates. The finite
index families `Instance`, `Theta`, and `Mode` describe the bounded audit table `T(x) × M(x)`;
`Bad` records the local failure predicate; and the remaining fields abstract the complexity
consequences proved from full-table verification, bad-witness extraction, and deterministic
enumeration. -/
def fullTableCertified {Instance Theta Mode : Type}
    (Bad : Instance → Theta → Mode → Prop) : Prop :=
  ∀ i θ m, ¬ Bad i θ m

def badWitnessCertified {Instance Theta Mode : Type}
    (Bad : Instance → Theta → Mode → Prop) : Prop :=
  ∃ i θ m, Bad i θ m

structure FiniteAuditBidirectionalCertificateData (Instance Theta Mode : Type) where
  finiteInstance : Finite Instance
  finiteTheta : Finite Theta
  finiteMode : Finite Mode
  Bad : Instance → Theta → Mode → Prop
  enumerableInPolyTime : Prop
  inNP : Prop
  inCoNP : Prop
  inP : Prop
  fullTableCertificate : fullTableCertified Bad
  badWitnessCertificate : badWitnessCertified Bad
  np_of_fullTable : fullTableCertified Bad → inNP
  conp_of_badWitness : badWitnessCertified Bad → inCoNP
  p_of_enumeration : fullTableCertified Bad → badWitnessCertified Bad →
    enumerableInPolyTime → inP

/-- Finite bidirectional audit certificates: validating the whole bounded audit table gives the
`NP` side, extracting one bad witness gives the `coNP` side, and deterministic polynomial-time
enumeration upgrades the same finite package to `P`.
    thm:spg-finite-audit-bidirectional-certificates-np-conp -/
theorem paper_spg_finite_audit_bidirectional_certificates_np_conp {Instance Theta Mode : Type}
    (h : FiniteAuditBidirectionalCertificateData Instance Theta Mode) :
    h.inNP ∧ h.inCoNP ∧ (h.enumerableInPolyTime → h.inP) := by
  refine
    ⟨h.np_of_fullTable h.fullTableCertificate, h.conp_of_badWitness h.badWitnessCertificate, ?_⟩
  intro henum
  exact h.p_of_enumeration h.fullTableCertificate h.badWitnessCertificate henum

end Omega.SPG
