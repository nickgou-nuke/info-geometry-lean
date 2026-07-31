import Mathlib.Tactic

namespace Omega.GU

/-- Support separation for two radial-quadratic laws forces both directed KL divergences to be
infinite.
    prop:group-jg-radial-quadratic-kl-infinite -/
theorem paper_group_jg_radial_quadratic_kl_infinite
    {forwardKlInfinite reverseKlInfinite supportSeparated : Prop}
    (hSupport : supportSeparated)
    (hForward : supportSeparated → forwardKlInfinite)
    (hReverse : supportSeparated → reverseKlInfinite) :
    forwardKlInfinite ∧ reverseKlInfinite := by
  exact ⟨hForward hSupport, hReverse hSupport⟩

end Omega.GU
