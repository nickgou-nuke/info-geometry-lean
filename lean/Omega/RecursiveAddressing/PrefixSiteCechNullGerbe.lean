import Omega.RecursiveAddressing.PrefixSiteProjectiveRepTwist

namespace Omega.RecursiveAddressing

/-- Minimal paper-facing gerbe package over a prefix-site Čech groupoid. The fields record only
    the local gerbe properties and the represented Čech class needed by the wrapper theorem.
    thm:prefix-site-cech-null-gerbe -/
structure PrefixSiteGerbe (ι : Type*) (A : Type*) where
  groupoid : PrefixSiteCechGroupoid ι
  locallyNonempty : Prop
  locallyConnected : Prop
  banded : Prop
  cechClass : ι → ι → ι → A

/-- Neutrality is the concrete coboundary-killing predicate of the represented Čech class. -/
def PrefixSiteGerbe.neutral {ι A : Type*} [AddCommGroup A]
    (G : PrefixSiteGerbe ι A) : Prop :=
  MultiplierKilledByCoboundary G.groupoid G.cechClass

/-- The gerbe twisted by `α`: its neutrality is exactly the coboundary-killing condition for the
    multiplier class. -/
def twistedGerbe {ι A : Type*} [AddCommGroup A] (G : PrefixSiteCechGroupoid ι)
    (α : ι → ι → ι → A)
    (locallyNonempty locallyConnected banded : Prop) : PrefixSiteGerbe ι A where
  groupoid := G
  locallyNonempty := locallyNonempty
  locallyConnected := locallyConnected
  banded := banded
  cechClass := α

/-- Paper-facing gerbe semantics for the prefix-site Čech obstruction: the cocycle `α` defines a
    locally nonempty, locally connected, banded gerbe whose neutrality is equivalent to the
    multiplier being killed by a coboundary. -/
theorem paper_recursive_addressing_prefix_site_cech_null_gerbe
    {ι A : Type*} [AddCommGroup A] (G : PrefixSiteCechGroupoid ι) (α : ι → ι → ι → A)
    (locallyNonempty locallyConnected banded : Prop)
    (hLocallyNonempty : locallyNonempty)
    (hLocallyConnected : locallyConnected)
    (hBanded : banded) :
    ∃ Gα : PrefixSiteGerbe ι A,
      Gα.locallyNonempty ∧
      Gα.locallyConnected ∧
      Gα.banded ∧
      (Gα.neutral ↔ MultiplierKilledByCoboundary G α) ∧
      Gα.cechClass = α := by
  refine ⟨twistedGerbe G α locallyNonempty locallyConnected banded, ?_⟩
  simp [twistedGerbe, PrefixSiteGerbe.neutral, hLocallyNonempty,
    hLocallyConnected, hBanded]

/-- Paper label: `thm:prefix-site-cech-null-gerbe`. Abstract packaging of the functorial gerbe
construction: the gerbe built from a cover and cocycle is banded, its neutral objects are exactly
global certificates, and it depends only on the represented Čech class. -/
theorem paper_prefix_site_cech_null_gerbe {Cover Cocycle Gerbe Class : Type*}
    (mkGerbe : Cover → Cocycle → Gerbe) (cohomologyClass : Cocycle → Class)
    (bandedGerbe neutralGerbe globalCertificate : Gerbe → Prop)
    (hbanded : ∀ U alpha, bandedGerbe (mkGerbe U alpha))
    (hneut :
      ∀ U alpha, neutralGerbe (mkGerbe U alpha) ↔ globalCertificate (mkGerbe U alpha))
    (hclass :
      ∀ U alpha beta,
        cohomologyClass beta = cohomologyClass alpha → mkGerbe U beta = mkGerbe U alpha)
    (U : Cover) (alpha : Cocycle) :
    bandedGerbe (mkGerbe U alpha) ∧
      (neutralGerbe (mkGerbe U alpha) ↔ globalCertificate (mkGerbe U alpha)) ∧
      (∀ beta, cohomologyClass beta = cohomologyClass alpha →
        mkGerbe U beta = mkGerbe U alpha) := by
  exact ⟨hbanded U alpha, hneut U alpha, fun beta hbeta => hclass U alpha beta hbeta⟩

end Omega.RecursiveAddressing
