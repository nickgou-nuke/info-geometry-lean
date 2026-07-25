import Mathlib.Tactic
import InfoGeometry.Canonical.SplitCliffordSourceSuperVirasoroRecursive

/-!
# InfoGeometry.Canonical.SplitCliffordSuperVirasoroLimitR

Ramond-limit closure wrapper for the finite truncation Super-Virasoro schema.

This file packages eventual defect-vanishing hypotheses into vectorwise
eventual exact superbracket equalities for integer-indexed Ramond modes.
-/

noncomputable section

namespace InfoGeometry.Canonical.SuperVirasoro

open Filter

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/--
Vectorwise Ramond-limit closure packet:
eventual vanishing of finite truncation defects on a fixed vector `v`.
-/
structure RVectorLimitClosure
    (m r s : ℤ)
    (J ψ : ℤ → Module.End 𝕜 V)
    (central_N : ℤ → ℤ → 𝕜)
    (v : V) : Prop where
  LG_defect_eventually_zero :
    ∀ᶠ N : ℤ in atTop, defect_LG N m r J ψ v = 0
  GG_defect_eventually_zero :
    ∀ᶠ N : ℤ in atTop, defect_GG N r s J ψ central_N v = 0

/--
Ramond-limit closure theorem (vectorwise): from eventual defect-vanishing,
both superbrackets are eventually exact on `v`.
-/
theorem r_limit_superbrackets_eventually_exact_on_vector
    (m r s : ℤ)
    (J ψ : ℤ → Module.End 𝕜 V)
    (central_N : ℤ → ℤ → 𝕜)
    (v : V)
    (h : RVectorLimitClosure m r s J ψ central_N v) :
    (∀ᶠ N : ℤ in atTop,
      (((L_trunc N m J ψ) * (G_trunc N r J ψ) - (G_trunc N r J ψ) * (L_trunc N m J ψ)) v)
        =
      ((((m : 𝕜) / 2 - (r : 𝕜)) • G_trunc N (m + r) J ψ) v))
    ∧
    (∀ᶠ N : ℤ in atTop,
      (((G_trunc N r J ψ) * (G_trunc N s J ψ) + (G_trunc N s J ψ) * (G_trunc N r J ψ)) v)
        =
      (((((2 : 𝕜) • L_trunc N (r + s) J ψ) + (central_N r s) • (1 : Module.End 𝕜 V)) v))) := by
  constructor
  · exact eventually_exact_LG_on_vector m r J ψ v h.LG_defect_eventually_zero
  · exact eventually_exact_GG_on_vector r s J ψ central_N v h.GG_defect_eventually_zero

end InfoGeometry.Canonical.SuperVirasoro

