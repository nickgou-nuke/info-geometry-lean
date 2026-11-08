import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordSourceSuperVirasoroRecursive

/-!
# InfoGeometry.Canonical.SplitCliffordSuperVirasoroLimitNS

NS-limit closure wrapper for the finite truncation Super-Virasoro schema.

This file packages eventual defect-vanishing hypotheses into vectorwise
eventual exact superbracket equalities at `N → +∞`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SuperVirasoro

open Filter

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/--
Vectorwise NS-limit closure packet:
eventual vanishing of finite truncation defects on a fixed vector `v`.
-/
def NSVectorLimitClosure
    (m r s : ℤ)
    (J ψ : ℤ → Module.End 𝕜 V)
    (central_N : ℤ → ℤ → 𝕜)
    (v : V) : Prop :=
  (∀ᶠ N : ℤ in atTop, defect_LG N m r J ψ v = 0) ∧
    (∀ᶠ N : ℤ in atTop, defect_GG N r s J ψ central_N v = 0)

/--
NS-limit closure theorem (vectorwise): from eventual defect-vanishing,
both superbrackets are eventually exact on `v`.
-/
theorem ns_limit_superbrackets_eventually_exact_on_vector
    (m r s : ℤ)
    (J ψ : ℤ → Module.End 𝕜 V)
    (central_N : ℤ → ℤ → 𝕜)
    (v : V)
    (h : NSVectorLimitClosure m r s J ψ central_N v) :
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
  · exact eventually_exact_LG_on_vector m r J ψ v h.1
  · exact eventually_exact_GG_on_vector r s J ψ central_N v h.2

end InfoGeometry.Canonical.SuperVirasoro
