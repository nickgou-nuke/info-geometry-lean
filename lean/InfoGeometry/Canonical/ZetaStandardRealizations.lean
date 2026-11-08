import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.ZetaStandardRealizations

Honest Lean formalization of the standard realization surfaces of the Riemann
zeta function.

This file does not prove analytic continuation or the classical analytic
equivalences from first principles. Instead, it formalizes the standard
definition surfaces as exact structure fields and proves the symmetry-adapted
centered-`ξ` consequence `Ξ(z) = Ξ(-z)` from the completed-zeta functional
symmetry `ξ(s) = ξ(1-s)`.
-/

namespace InfoGeometry.Canonical.ZetaStandardRealizations

abbrev ComplexFunction := ℂ → ℂ

/-- Symmetry-adapted centered coordinate `s = 1/2 + z`. -/
noncomputable def criticalCentered (z : ℂ) : ℂ := (1 / 2 : ℂ) + z

@[simp] theorem one_sub_criticalCentered (z : ℂ) :
    1 - criticalCentered z = criticalCentered (-z) := by
  simp [criticalCentered]
  ring

@[simp] theorem criticalCentered_neg (z : ℂ) :
    criticalCentered (-z) = 1 - criticalCentered z := by
  rw [← one_sub_criticalCentered]

/-- Dirichlet-series realization on a stated domain. -/
structure DirichletSeriesRealization where
  zeta : ComplexFunction
  dirichletSeries : ComplexFunction
  domain : Set ℂ
  zeta_eq_dirichletSeries : ∀ ⦃s : ℂ⦄, s ∈ domain → zeta s = dirichletSeries s

namespace DirichletSeriesRealization

@[simp] theorem eq_on_domain (D : DirichletSeriesRealization) {s : ℂ} (hs : s ∈ D.domain) :
    D.zeta s = D.dirichletSeries s :=
  D.zeta_eq_dirichletSeries hs

end DirichletSeriesRealization

/-- Euler-product realization on a stated domain. -/
structure EulerProductRealization where
  zeta : ComplexFunction
  eulerProduct : ComplexFunction
  domain : Set ℂ
  zeta_eq_eulerProduct : ∀ ⦃s : ℂ⦄, s ∈ domain → zeta s = eulerProduct s

namespace EulerProductRealization

@[simp] theorem eq_on_domain (E : EulerProductRealization) {s : ℂ} (hs : s ∈ E.domain) :
    E.zeta s = E.eulerProduct s :=
  E.zeta_eq_eulerProduct hs

end EulerProductRealization

/-- Alternating `η`-series realization on a stated domain. -/
structure EtaRealization where
  zeta : ComplexFunction
  eta : ComplexFunction
  domain : Set ℂ
  zeta_eq_eta_rescaled : ∀ ⦃s : ℂ⦄, s ∈ domain → zeta s = eta s / (1 - 2 ^ (1 - s))

namespace EtaRealization

@[simp] theorem eq_on_domain (E : EtaRealization) {s : ℂ} (hs : s ∈ E.domain) :
    E.zeta s = E.eta s / (1 - 2 ^ (1 - s)) :=
  E.zeta_eq_eta_rescaled hs

end EtaRealization

/-- Mellin-integral realization on a stated domain. -/
structure MellinIntegralRealization where
  zeta : ComplexFunction
  mellinIntegral : ComplexFunction
  domain : Set ℂ
  zeta_eq_mellinIntegral : ∀ ⦃s : ℂ⦄, s ∈ domain → zeta s = mellinIntegral s

namespace MellinIntegralRealization

@[simp] theorem eq_on_domain (M : MellinIntegralRealization) {s : ℂ} (hs : s ∈ M.domain) :
    M.zeta s = M.mellinIntegral s :=
  M.zeta_eq_mellinIntegral hs

end MellinIntegralRealization

/-- Completed-`ξ` realization with the `s ↔ 1-s` symmetry. -/
structure CompletedXiRealization where
  xi : ComplexFunction
  xi_symm : ∀ s : ℂ, xi s = xi (1 - s)

namespace CompletedXiRealization

/-- Centered completed zeta `Ξ(z) = ξ(1/2 + z)`. -/
noncomputable def centeredXi (X : CompletedXiRealization) : ComplexFunction :=
  fun z => X.xi (criticalCentered z)

theorem centeredXi_apply (X : CompletedXiRealization) (z : ℂ) :
    X.centeredXi z = X.xi (criticalCentered z) :=
  rfl

@[simp] theorem centeredXi_even (X : CompletedXiRealization) (z : ℂ) :
    X.centeredXi z = X.centeredXi (-z) := by
  unfold centeredXi
  calc
    X.xi (criticalCentered z) = X.xi (1 - criticalCentered z) := by
      exact X.xi_symm (criticalCentered z)
    _ = X.xi (criticalCentered (-z)) := by
      rw [one_sub_criticalCentered]

end CompletedXiRealization

/-- Functional-equation realization on a stated domain. -/
structure FunctionalEquationRealization where
  zeta : ComplexFunction
  reflectedRhs : ComplexFunction
  domain : Set ℂ
  zeta_eq_reflectedRhs : ∀ ⦃s : ℂ⦄, s ∈ domain → zeta s = reflectedRhs s

namespace FunctionalEquationRealization

@[simp] theorem eq_on_domain (F : FunctionalEquationRealization) {s : ℂ} (hs : s ∈ F.domain) :
    F.zeta s = F.reflectedRhs s :=
  F.zeta_eq_reflectedRhs hs

end FunctionalEquationRealization

/-- Bernoulli special-value realization at negative integers. -/
structure BernoulliSpecialValues where
  zeta : ComplexFunction
  bernoulli : ℕ → ℂ
  zeta_neg_nat_eq : ∀ n : ℕ, zeta (-((n : ℂ))) = -(bernoulli (n + 1)) / (n + 1)

namespace BernoulliSpecialValues

@[simp] theorem at_negative_nat (B : BernoulliSpecialValues) (n : ℕ) :
    B.zeta (-((n : ℂ))) = -(B.bernoulli (n + 1)) / (n + 1) :=
  B.zeta_neg_nat_eq n

end BernoulliSpecialValues

/-- Hurwitz specialization `ζ(s) = ζ(s,1)`. -/
structure HurwitzSpecialization where
  zeta : ComplexFunction
  hurwitz : ℂ → ℂ → ℂ
  zeta_eq_hurwitz_one : ∀ s : ℂ, zeta s = hurwitz s 1

namespace HurwitzSpecialization

@[simp] theorem at_one (H : HurwitzSpecialization) (s : ℂ) :
    H.zeta s = H.hurwitz s 1 :=
  H.zeta_eq_hurwitz_one s

end HurwitzSpecialization

/-- Polylog specialization `ζ(s) = Li_s(1)`. -/
structure PolylogSpecialization where
  zeta : ComplexFunction
  polylog : ℂ → ℂ → ℂ
  zeta_eq_polylog_one : ∀ s : ℂ, zeta s = polylog s 1

namespace PolylogSpecialization

@[simp] theorem at_one (P : PolylogSpecialization) (s : ℂ) :
    P.zeta s = P.polylog s 1 :=
  P.zeta_eq_polylog_one s

end PolylogSpecialization

/-- Bundle the standard zeta realization surfaces together. -/
structure StandardZetaAtlas where
  dirichlet : DirichletSeriesRealization
  euler : EulerProductRealization
  eta : EtaRealization
  mellin : MellinIntegralRealization
  xi : CompletedXiRealization
  functional : FunctionalEquationRealization
  bernoulli : BernoulliSpecialValues
  hurwitz : HurwitzSpecialization
  polylog : PolylogSpecialization

namespace StandardZetaAtlas

@[simp] theorem centeredXi_even (A : StandardZetaAtlas) (z : ℂ) :
    A.xi.centeredXi z = A.xi.centeredXi (-z) :=
  CompletedXiRealization.centeredXi_even A.xi z

end StandardZetaAtlas

end InfoGeometry.Canonical.ZetaStandardRealizations
